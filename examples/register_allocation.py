import json
import sys
from collections import defaultdict, OrderedDict
import logging
import bisect
import argparse # for getting register count info
from cfg import block_map, successors, add_terminators, add_entry, reassemble, edges
from form_blocks import form_blocks

# ASSUMES THAT LOOP NORMALIZATION HAS OCCURRED AND SSA CODE THAT WAS LOOP NORMALIZED IS THE INPUT!

logging.basicConfig(filename='debug.log', level=logging.DEBUG)

def validate_number(value):
    ''' 
    function to check if the passed in argument (number of registers) is >= 2
    '''
    number = int(value)
    if number < 2:
        raise argparse.ArgumentTypeError("The number must be greater than 2.")
    return number

def def_blocks(blocks):
    """Get a map from variable names to defining blocks.
    """
    out = defaultdict(set)
    for name, block in blocks.items():
        for instr in block:
            if 'dest' in instr:
                out[instr['dest']].add(name)
    return dict(out)


def find_empty_list_value(d, ord_dict):
    '''
    Simple way to find the block with an empty list. used to find the entry block
    '''
    for key in ord_dict.keys():
        if d.get(key) == []:
            return key
    return None  # If no empty list is found

def postorder_dfs(graph, start, visited=None, postorder_list=None, in_process=None):
    '''
    Find the approximate postorder of nodes. Uses DFS based algo
    '''
    if visited is None:
        visited = set()
    if postorder_list is None:
        postorder_list = []
    if in_process is None:
        in_process = set()

    if start in in_process:
        # Simply return if a cycle is detected, avoiding infinite recursion
        return

    if start not in visited:
        # Mark the node as being processed (in the current DFS path)
        in_process.add(start)

        # Visit all adjacent nodes (children)
        for neighbor in graph[start]:
            postorder_dfs(graph, neighbor, visited, postorder_list, in_process)

        # After visiting all children, mark the node as visited
        visited.add(start)
        # Remove the node from the in-process set
        in_process.remove(start)
        # Append the node to the postorder list after all descendants are visited
        postorder_list.append(start)

    return postorder_list

def get_types(func):
    # Silly way to get the type of variables. (According to the Bril
    # spec, well-formed programs must use only a single type for every
    # variable within a given function.)
    types = {arg['name']: arg['type'] for arg in func.get('args', [])}
    for instr in func['instrs']:
        if 'dest' in instr:
            types[instr['dest']] = instr['type']
    return types


def loop_blocks_by_backEdge(preds, back_edge_block, header_block):
    '''
    Find all blocks that could be executed between a header block and a back edge block
    Used in loop analysis, assumes that the header block dominates the back edge block as would occur in loops
    '''
    reachable_blocks = set()
    stack = [back_edge_block]
    visited = set()
    while stack:
        # Get the current block
        current_block = stack.pop()
        if current_block in visited:
            continue
        visited.add(current_block)
        if current_block == header_block:
            continue
        reachable_blocks.add(current_block)
        for pred in preds.get(current_block, []):
            if pred not in visited:
                stack.append(pred)
        # add header to complete loop
        reachable_blocks.add(header_block)
    return reachable_blocks

def postorder_traversal(root, succs, backedges):
    visited = set()
    postorder = []

    def dfs(node):
        if node in visited:
            return
        visited.add(node)
        # Traverse successors, excluding backedges
        for succ in succs.get(node, []):
            if (node, succ) not in backedges:
                dfs(succ)
        # Append the node after visiting its successors
        postorder.append(node)

    # Start traversal from the root
    dfs(root)
    return postorder


        
# function to remove overlapping (nested) loops since post_order traversal should take care of nested loop ordering
def reduce_dict(d):
    keys_to_remove = set()

    for key1, value1 in d.items():
        for key2, value2 in d.items():
            if key1 != key2 and set(value1).issubset(set(value2)):
                keys_to_remove.add(key1)

    return {key: value for key, value in d.items() if key not in keys_to_remove}

# function to reorder a list of blocks so that loop components are placed next to each other without violating the postorder
def reorder_postorder(postorder, filtered_loops):
    i = 0
    while i < len(postorder):
        element = postorder[i]
        # Check if the element is a <something>_preheader
        if element.endswith("_preheader"):
            loop_name = element.split("_preheader")[0]
            loop_key = (f"{loop_name}_latch", loop_name)
            
            # Check if the loop_key exists in filtered_loops
            if loop_key in filtered_loops:
                # Get the elements to reorder
                loop_elements = filtered_loops[loop_key]
                loop_elements_set = set(filtered_loops[loop_key])
                
                # Remove all loop elements from postorder
                postorder = [x for x in postorder if x not in loop_elements_set]
                
                # Add the loop elements after the current <something>_preheader
                postorder = postorder[:i + 1] + loop_elements + postorder[i + 1:]
        
        # Move to the next element
        i += 1
    
    return postorder

# finds phi instrucitons for a specific block
def find_phis(block_map_result):

    phi_map = {}
    for block in block_map_result:
        current_block_phis = []

        for instruction in block_map_result[block]:
            if "op" in instruction and instruction.get('op') == 'phi':
                current_block_phis.append(instruction)
        
        phi_map[block] = current_block_phis
    
    return phi_map

# Custom Interval Class
class Interval:

    def __init__(self, id):
        self.ranges = []  # List of (start_instruction, end_instruction)
        self.start = None  # First point where the variable is live
        self.register = None # Register ID for this Interval
        self.interval_id = id # Interval Object Id for a specific Operand
        self.uses = set() # List of uses of the target Operand
        self.end = None # Last point where the variable is live in this Interval

    def add_use(self, use_time):
        self.uses.add(use_time)

    def add_range(self, start, end):
        self.ranges.append((start, end))  # Add the new range
        self.ranges.sort(key=lambda x: x[0])  # Sort ranges by start

        # Merge overlapping ranges
        merged_ranges = []
        current_start, current_end = self.ranges[0]
        for s, e in self.ranges[1:]:
            if s <= current_end:  # Overlapping
                current_end = max(current_end, e)
            else:
                merged_ranges.append((current_start, current_end))
                current_start, current_end = s, e
        merged_ranges.append((current_start, current_end))  # Add the last range
        self.end = merged_ranges[-1][1]
        self.ranges = merged_ranges    

    def set_from(self, start):
        if self.start is None:
            self.start = start
            # we now need to cut the interval that intersects with start
            for i, range in enumerate(self.ranges):
                start_range, end_range = range
                # we know there is an intersection if start is between start and end of this range
                if (start_range <= start <= end_range):
                    # update the index to be (global) start, end_range
                    cut_range = (start, end_range)
                    self.ranges[i] = cut_range
                    break # we found where to cut

    def covers(self, time): # check if target time is within any range
        for range in self.ranges:
            start, end = range
            if start <= time <= end:
                return True
        return False

    def nextUseAfter(self, target_time): # find the soonest use after target time for this interval
        temp = sorted(self.uses)
        #for use in self.uses:
        for use in temp:
            if target_time <= use:
                return use
        return None

    def firstUse(self): # find the first use
        temp = sorted(self.uses)
        #return self.uses[0]
        return temp[0]


def earliestIntersection(source_interval, target_interval):
    # we want to find in the source interval where the target interval first intersects
    earliest = float("inf")
    for range in source_interval.ranges:
        source_start, source_end = range

        for t_range in target_interval.ranges:
            target_start, target_end = t_range

            if source_start <= target_start <= source_end: # if our start is within source
                earliest = min(earliest, target_start)
            elif source_start <= target_end <= source_end:
                earliest = min(earliest, target_end)
    return earliest 

# function to split current interval into a new one for the same object
def split_interval(target_operand, old_interval, free_until_pos, intervals):

    # first we need to create our new interval class
    new_interval = Interval(len(intervals[target_operand]) + 1) # creates unique id

    # we copy over the ranges that include or come after free_until_pos
    # we also save which ranges we should remove
    ranges_to_remove = []
    for i, range in enumerate(old_interval.ranges):
        start, end = range
        if free_until_pos < start <= end: # in this case the range does not intersect with free until pos
            new_interval.add_range(start, end)
            ranges_to_remove.append(range)
        #VERIFY
        elif start < free_until_pos <= end: #in this case there is an intersection
            new_interval.add_range(free_until_pos, end)
            old_interval.ranges[i] = (start, free_until_pos)
            print("debug: ", start, free_until_pos)

    # we set the Start of the interval, cutting the first range copied over
    print(new_interval.ranges)
    new_interval.set_from(free_until_pos)
    new_interval.set_from(new_interval.ranges[0][0])

    # we fix the previous interval to no longer include the ranges that got added over
    
    for range in ranges_to_remove:
        old_interval.ranges.remove(range) #VERIFY

    # update the end of our old interval (new interval updated dynamically)
    old_interval.end = sorted(old_interval.ranges)[-1][1]

    # update the end of our new interval (new interval updated dynamically)
    new_interval.end = sorted(new_interval.ranges)[-1][1]

    # we fix the uses that come after the time
    for use in old_interval.uses:
        if use >= free_until_pos:
            new_interval.add_use(use)
    for use in new_interval.uses:
        old_interval.uses.remove(use)
    
    # add the new interval to the map and edit the old interval
    for i, interval in enumerate(intervals[target_operand]):
        if interval.interval_id == old_interval.interval_id:
            intervals[target_operand][i] = old_interval
            break
    intervals[target_operand].append(new_interval)
    return intervals, new_interval, old_interval


# finds variable related to block label for a phi
def find_phi_label_arg(phi, target_block):

    for i, label in enumerate(phi['labels']):
        if label == target_block:
            return phi['args'][i]
    return None

# Finds all uses of a specific variable
def find_uses(block_map_result, instr_to_index):

    var_to_use_map = {}
    for block in block_map_result:
        for i, instruction in enumerate(block_map_result[block]):
            overall_index = instr_to_index[(block, i)]
            if "args" in instruction:
                for arg in instruction["args"]:

                    if arg not in var_to_use_map:
                        var_to_use_map[arg] = set()
                    
                    var_to_use_map[arg].add(overall_index)
    return var_to_use_map

# Update Index Mapping after spill_id's block and index
#instr_to_index is (block, index) --> ID
# index_to_instr is ID --> [(block, index)]
def update_indices(instr_to_index, index_to_instr, spill_id):
    for desired_block, desired_index  in index_to_instr[spill_id]: 
        # we loop but honestly this will only happens once as long as its not a phi at that index
        remove_from_instr_to_index = set()
        add_to_instr_to_index = set()
        for key in instr_to_index:
            curr_block, curr_index = key
            if curr_block == desired_block and curr_index >= desired_index:
                # this is a specific block and index that must be shifted
                id_to_update = instr_to_index[(curr_block, curr_index)]

                # update the current instr_to_index map to point to this id
                add_to_instr_to_index.add((curr_block, curr_index + 1))
                remove_from_instr_to_index.add((curr_block, curr_index))

                # update blocks and indices impacted by this change at id
                for pair in index_to_instr[id_to_update]:
                    pair_block, pair_index = pair
                    if pair_block == desired_block and pair_index >= desired_index:
                        pair[1] += 1
        for pair in remove_from_instr_to_index:
            instr_to_index.remove(pair)
        for pair in add_to_instr_to_index:
            instr_to_index.add(pair)
    return instr_to_index, index_to_instr

# builds intervals based on algorithm in paper
def build_intervals(postorder, succs, phi_map, block_map_result, instr_to_index, block_start_end_map, header_to_latch_map, var_to_use_map):
    intervals = {} # maps operands to interval classes
    live_in = {} # maps blocks to sets of operands live at block entry

    for block in reversed(postorder):
        instructions = block_map_result[block]
        live = set()
        
        # Union of liveIn sets from successors
        for successor in succs[block]:
            live.update(live_in.get(successor, set()))
        
        # Handle phi functions in successors
        for successor in succs[block]:
            for phi in phi_map[successor]: 
                live.add(find_phi_label_arg(phi, block))
        
        # Initialize intervals for live variables
        for operand in live:
            if operand not in intervals:
                intervals[operand] = [Interval(1)] #VERIFY
            intervals[operand][0].add_range(block_start_end_map[block][0], block_start_end_map[block][1])
            # logging.debug(f'A: Adding range for {operand} {block_start_end_map[block][0]} to {block_start_end_map[block][1]}')
        
        # Process operations in reverse - go through each instruction and make sure its an operation
        for i in range(len(instructions) - 1, -1, -1):
            instruction = instructions[i]
            # conditional to check if instruction is operation
            if "op" in instruction and instruction.get('op') == 'phi':
                continue
            else:
                # Handle Outputs
                if "dest" in instruction:
                    output = instruction["dest"]
                    if output not in intervals:
                        intervals[output] = [Interval(1)]

                    intervals[output][0].set_from(instr_to_index[(block, i)])
                    live.discard(output)

                # Handle Inputs
                if "args" in instruction:
                    for input in instruction["args"]:
                        if input not in intervals:
                            intervals[input] = [Interval(1)]
                        intervals[input][0].add_range(block_start_end_map[block][0], instr_to_index[(block, i)])
                        intervals[input][0].add_use(instr_to_index[(block, i)])
                        # logging.debug(f'B: Adding range for {input} {block_start_end_map[block][0]} to {instr_to_index[(block, i)]}')
                        live.add(input)
        
        # Handle phi outputs
        for phi in phi_map[block]:
            logging.debug(phi)
            live.discard(phi["dest"])
        
        # Loop handling
        if block in header_to_latch_map: # note: need a function to determine if this block is a loop header
            loop_end = header_to_latch_map[block] # need a function to get loop latch/exit
            for operand in live:
                if operand not in intervals:
                    intervals[operand] = [Interval(1)]
                intervals[operand][0].add_range(block_start_end_map[block][0], block_start_end_map[loop_end][1])
                # logging.debug(f'C: Adding range for {operand} {block_start_end_map[block][0]} to {block_start_end_map[loop_end][1]}')
        
        # Save liveIn for the block
        live_in[block] = live

    return intervals, live_in

if __name__ == "__main__":
    prog = json.load(sys.stdin)
    
    
    # gather the number for registers from the cmdline
    parser = argparse.ArgumentParser(description="Process an integer argument greater than 2.")
    parser.add_argument("numRegisters", type=validate_number, help="An integer number greater than 2")
    args = parser.parse_args()

    # enter each (main) function
    for fn in prog["functions"]:
        function_args = []
        if "args" in fn:
            function_args = fn["args"]


        # create a map block_map_result that maps label to block of code
        blocks = list(form_blocks(fn['instrs']))
        block_map_result = block_map(blocks)


        # preds is a map from a block's label to its predecesor's labels. same for succs
        preds, succs = edges(block_map_result)

        # this is the function entry block
        entry = find_empty_list_value(preds, block_map_result)

        # calculate the order in which to do dominance analysis        
        ordered_keys = list(reversed(postorder_dfs(succs, entry)))
        #add missing keys
        for key in block_map_result.keys():
            if key not in ordered_keys:
                ordered_keys.append(key)

        
        
        #DOMINANCE!!!!!
        # REMEMBER: dominance[v] is "who dominates v"  (block label -> [list of labels of blocks that dominate v])
        dominance = {}
        for v in succs:
            dominance[v] = set(ordered_keys)
        

        dom_changed = True
        while dom_changed:
            dom_changed = False
            for current in ordered_keys:
                if preds[current]:
                    new_dominance = set.intersection(*(dominance[p] for p in preds[current]))
                else:
                    new_dominance = set()  # If no predecessors, use an empty set

                new_dominance.add(current)

                if dominance[current] != new_dominance:
                    dominance[current] = new_dominance
                    dom_changed = True
            


        # Initialize the dominate dictionary (block label -> [list of dominated blocks' labels])
        # REMEMBER: dominate[v] is "who v dominates"
        dominate = {v: set() for v in dominance}

        # Populate the dominate dictionary
        for dominated, dominators in dominance.items():
            for dominator in dominators:
                dominate[dominator].add(dominated)



        # Create the dominator tree
        # REMEMBER: dominator_tree[v] is "set of children who are one level lower in the dominance tree
        dominator_tree = {}
        for v in succs:
            dominator_tree[v] =set()
        for dominator, dom_set in dominate.items():
            dom_tree_children = dom_set.difference({dominator})
            for dominated in dom_set:
                if dominator != dominated:
                    dominated_strict_dom_set = dominate[dominated].difference({dominated})
                    dom_tree_children = dom_tree_children.difference(dominated_strict_dom_set)
            dominator_tree[dominator] = dom_tree_children


        # strict dominance
        def strict_dom(A,B):
            return ( B in dominate[A] ) and ( A != B )
        

        # create Dominance Frontier
        dominance_frontier = {v: set() for v in dominance}
        for dominator, dom_set in dominate.items():
            for dominated in dom_set:  
                for successor in succs[dominated]:
                    if not strict_dom(dominator, successor):
                        dominance_frontier[dominator].add(successor)

                        
        # Finding Back Edges (A -> B, where B dominates A)
        backEdge_list = []

        header_to_latch_map = {} # maps header blocks to their latch block

        for dominator, doms in dominate.items():
            for domed in doms:
                if dominator in succs[domed]:
                    backEdge_list.append((domed, dominator))
                    header_to_latch_map[dominator] = domed


        #find all the blocks that are associated with each loop
        loops = {} # map from backedge to loop-involved blocks
        for be in backEdge_list:
            loops[be] = loop_blocks_by_backEdge(preds, be[0], be[1])




        # ESTABLISHING ORDER
        postorder = postorder_traversal(entry, succs, loops.keys())[::-1]
        
        # this is the order of linear blocks
        # MAY NEED REVISION!!!!

        def sort_set_by_reference(my_set, reference_list):
            '''Return set elements sorted by their position in the reference list'''
            return [x for x in reference_list if x in my_set]
            

        # sorting the loops by postorder
        loops_sorted_lists = {}
        for be, loop_set in loops.items():
            loops_sorted_lists[be] = sort_set_by_reference(loop_set, postorder)
        

        filtered_nested_loops = reduce_dict(loops_sorted_lists)
        
        reordered_postorder = reorder_postorder(postorder, filtered_nested_loops)

        phi_map = find_phis(block_map_result)

        # label instructions to their index/id
        instr_to_index = {} # maps tuple (block, instruction_block_index) to overall index
        index_to_instr = {}
        block_start_end_map = {} # maps block to tuple (index of starting instruction, index of ending instruction)
        index_of_instr = 2
        for block in block_map_result:
            block_start = index_of_instr
            # go through each instruction in our map
            for i in range(len(block_map_result[block])):
                instr_to_index[(block, i)] = index_of_instr
                if index_of_instr in index_to_instr:
                    index_to_instr[index_of_instr].append((block, i))
                else:
                    index_to_instr[index_of_instr] = [(block, i)]
                if i + 1 < len(block_map_result[block]) and "op" in block_map_result[block][i+1] and block_map_result[block][i+1].get('op') == 'phi':
                    # we dont change the index of phis if the next instruciton is also a phi instruction
                    continue
                else:
                    index_of_instr += 2
            block_end = index_of_instr - 2
            block_start_end_map[block] = (block_start, block_end)

        var_to_use_map = find_uses(block_map_result, instr_to_index)

        intervals, live_in = build_intervals(reordered_postorder, succs, phi_map, block_map_result, instr_to_index, block_start_end_map, header_to_latch_map, var_to_use_map)

        #print(reorder_postorder(postorder, filtered_nested_loops))
        # logging.debug(f'intervals: {intervals}')
        # logging.debug(f'live in: {live_in}')

        # for op in intervals:
        #     for interval in intervals[op]:
        #         logging.debug(f'operand: {op}')
        #         logging.debug(f'interval id {interval.interval_id}')
        #         logging.debug(f'ranges: {interval.ranges}')
        #         logging.debug(f'start: {interval.start}')
        #         logging.debug(f'end: {interval.end}')



        


        # # test splitting interval
        # intervals, new_interval = split_interval('arr_0', intervals['arr_0'][0], 12, intervals)
        # logging.debug("post split interval")
        # for op in intervals:
        #     for interval in intervals[op]:
        #         logging.debug(f'operand: {op}')
        #         logging.debug(f'interval id {interval.interval_id}')
        #         logging.debug(f'ranges: {interval.ranges}')
        #         logging.debug(f'start: {interval.start}')
        #         logging.debug(f'end: {interval.end}')

        
        ################################################
        #     WRITING CODE FOR THE LINEAR SCAN         #
        # ASSUMPTIONS:
        # 1. We have a list of lifetime intervals of the format [( <Interval Object>, associated_variable/register), ...]
        #       sorted by start time
        lifetimeIntervals = [(val[0], key) for (key, val) in intervals.items()]
        # ASSUMES THAT EACH variable only has ONE interval object
        # 2. we have a dictionary of uses where the the variable/register is the key and the value is a list of uses sorted in increasing order [line1, line2, ...]
        # var_to_use_map = {}
        # 3. we have the proper block order from before. This should be reordered_postorder (from lifetime ranges branch)
        reordered_postorder = reordered_postorder
        print(reordered_postorder)
        #
        # 4. Number of physical registers We assume that we have at least as many registers as the maximum arguments in an instruction (ideally this is 3 or 1+maxnum fo phi instructions)
        numRegisters= args.numRegisters
        # Between functions, we do not care, all registers to stack both in here and in base case
        # ALL variables can be spilled (no fixed intervals)

        # 5. We will be adding BRIL instructions to signify the stack spills. We will store these in a map from location to a list of variables that are spilled there
        spills = defaultdict(list)
        ################################################

        # state sets. All contain tuples for the format ( <Interval Object>, associated_variable/register )
        # for item in lifetimeIntervals:
        #     print(item[0].start, item[0].ranges, item[1])

        # throw out all intervals relating to the __undefined phi variable input:
        lifetimeIntervals = [tup for tup in lifetimeIntervals if tup[1] != "__undefined"]

        unhandled = sorted(lifetimeIntervals, key=lambda x: x[0].start) 
        active = set() # intervals that are active at the current position (start<= curent position <= end)
        inactive = set() # intervals that are inactive at the current position (start<= curent position <= end)
        handled = set() # intervals that are handled at the current position

        print("unhandled: ")
        for qwert, qwertV in unhandled:
                print(qwertV+": "+", ".join([f"[{s}, {e}]" for s, e in qwert.ranges]) + ". Uses: "+ ", ".join([str(u) for u in qwert.uses]) + ". Start: ", qwert.start) 

        while unhandled:
            current, curVariable = unhandled.pop(0)
            #ruthless skip of current if it has NO RANGES
            if current.ranges == []: continue
            position = current.start
            
            print("position", position, current, curVariable, current.ranges, current.uses)
            for qwert, qwertV in unhandled:
                print(qwertV+": "+", ".join([f"[{s}, {e}]" for s, e in qwert.ranges]) + ". Uses: "+ ", ".join([str(u) for u in qwert.uses]) ) 
                
            
            
            #check for intervals in active that are handled or inactive
            first_remove_from_active = set()
            for it, it_var in active:
                if it.end < position:
                    handled.add((it, it_var))
                    first_remove_from_active.add( (it, it_var) )
                elif not it.covers(position):
                    inactive.add((it, it_var))
                    first_remove_from_active.add( (it, it_var) )
            for item in first_remove_from_active:
                active.remove(item)
            
            # check for intervals in inactive that are handled or active
            first_remove_from_inactive = set()
            for it, it_var in inactive:
                if it.end < position:
                    handled.add((it, it_var))
                    first_remove_from_inactive.add( (it, it_var) )
                elif it.covers(position):
                    active.add((it, it_var))
                    first_remove_from_inactive.add( (it, it_var) )
            for item in first_remove_from_inactive:
                inactive.remove(item)



            currentWasAllocated = False
            ######################
            # TryAllocateFreeReg #
            ######################
            # find a register for current (TryAllocateFreeReg)
            freeFailed = False    
            freeUntilPos = [float('inf')]*numRegisters # set freeUntilPos of all physical registers to maxInt. The physical register (int) is the index.
            for it, it_var in active:
                freeUntilPos[it.register] = 0
            for it, it_var in inactive:
                # if it.containsPosition(position):#TODo Current intersects inactive
                freeUntilPos[it.register] = min(freeUntilPos[it.register],      earliestIntersection(current, it) )  #TODo earliest intersection with current (after position, but should be handled without check)
            candidate_register = freeUntilPos.index(max(freeUntilPos)) # register with highest freeUntilPos

            # if curVariable == "val_0": print(current.ranges)

            if freeUntilPos[candidate_register] == 0:
                # no register is available without spilling
                freeFailed = True
            elif current.end <= freeUntilPos[candidate_register]:
                # register available for the whole interval
                current.register = candidate_register
                currentWasAllocated = True
                print("TERMINAL: WHOLE INSERTION AT REGISTER: ", candidate_register)
            else:
                               
                # def split_interval(target_operand, old_interval, free_until_pos, intervals):
                # return intervals, new_interval, old_interval
                intervals, new_interval, current = split_interval( curVariable, current, freeUntilPos[candidate_register], intervals)
                
                # register available for teh first part of the interval
                current.register = candidate_register
                currentWasAllocated = True

                # split_child = current.generateChild(freeUntilPos[candidate_register])
                # split_child_index = bisect.bisect_left(unhandled, (new_interval, curVariable), key = lambda x: x[0].start)
                # unhandled.insert(split_child_index, (new_interval, curVariable))
                unhandled.append((new_interval, curVariable))
                unhandled.sort(key = lambda x : x[0].start)
                print("TERMINAL: PARTIAL INSERTION AT REGISTER: ", candidate_register, " UNTIL ", freeUntilPos[candidate_register])


            ######################
            # AllocateBlockedReg #
            ######################
            #if free register allocation failed
            if freeFailed:
                nextUsePos = [float('inf')]*numRegisters # set nextUsePos of all physical registers to maxInt. The physical register (int) is the index.
                for it, it_var in active:
                    nextUsePos[it.register] = min(it.nextUseAfter(current.start), nextUsePos[it.register])
                for it, it_var in inactive:
                    nextUsePos[it.register] = min(it.nextUseAfter(current.start), nextUsePos[it.register])
                
                candidate_register = nextUsePos.index(max(nextUsePos)) # register with highest nextUsePos
            
                current_first_use = current.firstUse()
                if current_first_use > nextUsePos[candidate_register]:
                    # all other intervals are used before current is used
                    # so it is best to spill current itself
                    
                    
                    
                    # split_child = current.generateChild(current.firstUse())
                    print("DEBUG self spill: ", curVariable, current_first_use)
                    intervals, new_interval, current = split_interval( curVariable, current, current_first_use, intervals) # lookout for index to split

                    # split_child_index = bisect.bisect_left(unhandled, (new_interval, curVariable), key = lambda x: x[0].start)
                    # unhandled.insert(split_child_index, (new_interval, curVariable))
                    unhandled.append((new_interval, curVariable))
                    unhandled.sort(key= lambda x : x[0].start)

                    # TODO: create a BRIL instruction like 'stack = id var' that represents a spill
                    #spills[current_first_use].append(curVariable) maybe we shouldnt do this doesnt make sense
                    print("TERMINAL splitting self: ", curVariable, current.ranges)
                    
                    

                else:
                    # spill intervals that currently block reg

                    add_to_active = set()
                    remove_from_active = set()
                    add_to_inactive = set()
                    remove_from_inactive = set()

                    for it, it_var in active:
                        if it.register == candidate_register:
                            #split_active = it.generateChild(current.firstUse())
                            print("DEBUG active spill: ", it_var, it.ranges, current_first_use)
                            intervals, new_active, old_active = split_interval( it_var, it, current_first_use, intervals)
                            old_active.register = candidate_register
                            add_to_active.add((old_active, it_var))
                            remove_from_active.add((it, it_var))
                            # split_active_index = bisect.bisect_left(unhandled, (new_active, it_var), key = lambda x: x[0].start)
                            # unhandled.insert(split_active_index, (new_active, it_var))
                            unhandled.append((new_active, it_var))
                            unhandled.sort(key= lambda x : x[0].start)
                            # TODO: create a BRIL instruction like 'stack = id var' that represents a spill
                            # TODo: spil old_active
                            spills[current_first_use].append(it_var)

                            old_active.register = None
                            logging.debug("SPILL to STACK")
                            print("spilling: ", it_var, new_active.ranges)
                    

                    for it, it_var in inactive:
                        if it.register == candidate_register:
                            #split_inactive = it.generateChild(current.firstUse())
                            print("DEBUG inactive spill: ", it_var, it.ranges, current_first_use)
                            intervals, new_inactive, old_inactive = split_interval( it_var, it, current_first_use, intervals)
                            old_inactive.register = candidate_register
                            add_to_inactive.add((it_var, old_inactive))
                            remove_from_inactive.add((it_var, it))
                            # split_inactive_index = bisect.bisect_left(unhandled, (new_inactive, it_var), key = lambda x: x[0].start)
                            # unhandled.insert(split_inactive_index, (new_inactive, it_var))
                            unhandled.append((new_inactive, it_var))
                            unhandled.sort(key= lambda x : x[0].start)
                            # TODO: create a BRIL instruction like 'stack = id var' that represents a spill
                            # TODo: spill old_inactive
                            spills[current_first_use].append(it_var)
                            
                            old_inactive.register = None
                            logging.debug("SPILL to STACK")
                            print("spilling: ", it_var, new_inactive.ranges)

                    # fix inactive and active
                    for pair in add_to_active:
                        active.add(pair)
                    for pair in remove_from_active:
                        active.remove(pair)
                    for pair in add_to_inactive:
                        inactive.add(pair)
                    for pair in remove_from_inactive:
                        inactive.remove(pair)

                    
                    current.register = candidate_register
                    currentWasAllocated = True
                    print("TERMINAL: many previous removed: ", "Aftermath Unhandled: ", ', '.join([qwertV+": "+", ".join([f"[{s}, {e}]" for s, e in qwert.ranges]) + ". Uses: "+ ", ".join([str(u) for u in qwert.uses]) for qwert, qwertV in unhandled]))
                    


                # Since there are no fixed intervals for any registers, we do not further process

            # if current has a register assigned then add current to active
            if currentWasAllocated:
                active.add((current, curVariable))
        
        
        
        
        fn["instrs"] = reassemble(block_map_result)


    # UNCOMMENT LATER
    json.dump(prog, sys.stdout, indent=2)