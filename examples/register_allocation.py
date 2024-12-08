import json
import sys
from collections import defaultdict, OrderedDict
import logging

from cfg import block_map, successors, add_terminators, add_entry, reassemble, edges
from form_blocks import form_blocks

# ASSUMES THAT LOOP NORMALIZATION HAS OCCURRED AND SSA CODE THAT WAS LOOP NORMALIZED IS THE INPUT!

logging.basicConfig(filename='debug.log', level=logging.DEBUG)

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

# defines interval class
class Interval:
    def __init__(self):
        self.ranges = []  # List of (start_instruction, end_instruction)
        self.uses = set()
        self.start = None  # First point where the variable is live

    def add_range(self, start, end):
        self.ranges.append((start, end))
        self.uses.add(end)

    def add_uses(self, new_uses):
        self.uses.update(new_uses)

    def set_from(self, start):
        if self.start is None:
            self.start = start

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

# builds intervals based on algorithm in paper
def build_intervals(postorder, succs, phi_map, block_map_result, instr_to_index, block_start_end_map, header_to_latch_map, var_to_use_map):
    intervals = {} # maps operands to intervals
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
                intervals[operand] = Interval()
            intervals[operand].add_range(block_start_end_map[block][0], block_start_end_map[block][1])
        
        # Process operations in reverse - go through each instruction and make sure its an operation
        for i in range(len(instructions) - 1, -1, -1):
            instruction = instructions[i]
            # conditional to check if instruction is operation
            # Handle Outputs
            if "dest" in instruction:
                output = instruction["dest"]
                if output not in intervals:
                    intervals[output] = Interval()

                intervals[output].set_from(instr_to_index[(block, i)])
                live.discard(output)

            # Handle Inputs
            if "args" in instruction:
                for input in instruction["args"]:
                    if input not in intervals:
                        intervals[input] = Interval()
                    intervals[input].add_range(block_start_end_map[block][0], instr_to_index[(block, i)])
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
                    intervals[operand] = Interval()
                intervals[operand].add_range(block_start_end_map[block][0], block_start_end_map[loop_end][1])
        
        # Save liveIn for the block
        live_in[block] = live
    
    # add all uses to intervals
    for op in intervals:
        op_interval = intervals[op]
        if op in var_to_use_map:
            op_interval.add_uses(var_to_use_map[op])

    return intervals, live_in

if __name__ == "__main__":
    prog = json.load(sys.stdin)


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
        block_start_end_map = {} # maps block to tuple (index of starting instruction, index of ending instruction)
        index_of_instr = 1
        for block in block_map_result:
            block_start = index_of_instr
            for i in range(len(block_map_result[block])):
                instr_to_index[(block, i)] = index_of_instr
                index_of_instr += 1
            block_end = index_of_instr - 1
            block_start_end_map[block] = (block_start, block_end)
        
        var_to_use_map = find_uses(block_map_result, instr_to_index)

        intervals, live_in = build_intervals(postorder, succs, phi_map, block_map_result, instr_to_index, block_start_end_map, header_to_latch_map, var_to_use_map)

        #print(reorder_postorder(postorder, filtered_nested_loops))
        logging.debug(f'intervals: {intervals}')
        logging.debug(f'live in: {live_in}')

        for interval in intervals:
            logging.debug(f'interval: {interval}')
            logging.debug(f'{intervals[interval].ranges}')
            logging.debug(f'{intervals[interval].uses}')
            logging.debug(f'{intervals[interval].start}')



        fn["instrs"] = reassemble(block_map_result)
        




    # UNCOMMENT LATER
    json.dump(prog, sys.stdout, indent=2)