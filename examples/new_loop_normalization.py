import json
import sys
from collections import defaultdict, OrderedDict

from cfg import block_map, successors, add_terminators, add_entry, reassemble, edges
from form_blocks import form_blocks

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

        # cleaning up by adding an entry block and terminators if a block does not have them
        add_entry(block_map_result)
        add_terminators(block_map_result)

        # preds is a map from a block's label to its predecesor's labels. same for succs
        preds, succs = edges(block_map_result)

        # this is the function entry block
        entry = find_empty_list_value(preds, block_map_result)


        # remove false starts (blocks that have no preds and arent the entry):
        to_be_deleted =[]
        for p in preds:
            if len(preds[p]) ==0 and p != entry:
                to_be_deleted.append(p)
        
        # check for all blocks for which all successors are not reachable to be deleted for simplicity
        del_flag = True
        while del_flag:
            del_flag = False
            for p in preds:
                if p not in to_be_deleted and all(elem in to_be_deleted for elem in preds[p]) and p!= entry:
                    del_flag= True
                    to_be_deleted.append(p)
        for bad_blocks in to_be_deleted:
            del block_map_result[bad_blocks]
        
        
        
        #recompute with cleaned CFG:
        preds, succs = edges(block_map_result)

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
        for dominator, doms in dominate.items():
            for domed in doms:
                if dominator in succs[domed]:
                    backEdge_list.append((domed, dominator))


        #find all the blocks that are associated with each loop
        loops = {} # map from backedge to loop-involved blocks
        for be in backEdge_list:
            loops[be] = loop_blocks_by_backEdge(preds, be[0], be[1])

        
        
        # NORMALIZATION

        # creation of latches
        backs = {}

        header_to_latch = {} # map from headers to latches since they are 1-1 now

        for a, head in backEdge_list:
            if head not in backs:
                backs[head] = [a]
            else:
                if a not in backs[head]:
                    backs[head].append(a)

        for head, origins in backs.items():
            new_key = head+"_latch"
            jumpList = [{'labels': [head], 'op': 'jmp'}] # point it to head

            for origin in origins:
                for i in range(len(block_map_result[origin])):
                    if "op" in block_map_result[origin][i] and (block_map_result[origin][i]["op"] in ["br", "jmp"] ):
                        # this is a CF statement
                        for j in range(len(block_map_result[origin][i]["labels"])):
                            # each time head is label make it points to latch
                            if block_map_result[origin][i]["labels"][j] == head:
                                block_map_result[origin][i]["labels"][j] = new_key
            
            
            block_map_result[new_key] = jumpList
            header_to_latch[head] = new_key # add to 1-1 relation
            
        







        # creation of preheaders
        header_to_preheader = {} # map from headers to preheaders since they are 1-1 now
        for head in header_to_latch:
            # create the new preheader
            new_key = head+"_preheader"
            jumpList = [{'labels': [head], 'op': 'jmp'}]


            for p in preds[head]:
                if p != header_to_latch[head] and p not in backs[head]:
                    # these should be all of the nodes that preceed any executions of the loop
                    for i in range(len(block_map_result[p])):
                        if "op" in block_map_result[p][i] and (block_map_result[p][i]["op"] in ["br", "jmp"] ):
                            # this is a CF statement
                            for j in range(len(block_map_result[p][i]["labels"])):
                                # each time head is label make it points to latch
                                if block_map_result[p][i]["labels"][j] == head:
                                    block_map_result[p][i]["labels"][j] = new_key

            block_map_result[new_key] = jumpList
            header_to_preheader[head] = new_key
        

        preds, succs = edges(block_map_result)

        
        # fixing phis for latch:
        
        for block in block_map_result:
            
            if block.endswith("_latch"):
                phis_to_fix_in_header = {}
                head_block = block[:-6]# find the header
                for i in range (len( block_map_result[head_block])):
                    tbr = []
                    if "op" in block_map_result[head_block][i] and block_map_result[head_block][i]["op"] == "phi":
                        for j in range(len(block_map_result[head_block][i]["labels"])):
                            if block_map_result[head_block][i]["labels"][j] in preds[block]:
                                if i not in phis_to_fix_in_header:
                                    phis_to_fix_in_header[i] = []
                                phis_to_fix_in_header[i].append((block_map_result[head_block][i]["labels"][j] , block_map_result[head_block][i]["args"][j] , block_map_result[head_block][i]["type"] , block_map_result[head_block][i]["dest"]))
                                tbr.append(j)
                        tbr.sort(reverse=True)
                        for q in tbr:
                            block_map_result[head_block][i]["labels"].pop(q)
                            block_map_result[head_block][i]["args"].pop(q)
                        block_map_result[head_block][i]["labels"].append(block)
                        block_map_result[head_block][i]["args"].append(block_map_result[head_block][i]["dest"]+"_L")

                for _, fixer in phis_to_fix_in_header.items():
                    
                    ar = []
                    lbls = []
                    for fix in fixer:
                        lbls.append(fix[0])
                        ar.append(fix[1])
                    new_instr = { "args": ar, "dest": fixer[0][3]+"_L", "labels": lbls, "op": "phi", "type": fixer[0][2]}
                    block_map_result[block].insert(-1, new_instr)
                
                    
        
        # fixing phis for pre-header:
        for block in block_map_result:
            
            if block.endswith("_preheader"):
                phis_to_fix_in_header = {}
                head_block = block[:-10]# find the header
                for i in range (len( block_map_result[head_block])):
                    tbr = []
                    if "op" in block_map_result[head_block][i] and block_map_result[head_block][i]["op"] == "phi":
                        for j in range(len(block_map_result[head_block][i]["labels"])):
                            if block_map_result[head_block][i]["labels"][j] in preds[block]:
                                if i not in phis_to_fix_in_header:
                                    phis_to_fix_in_header[i] = []
                                phis_to_fix_in_header[i].append((block_map_result[head_block][i]["labels"][j] , block_map_result[head_block][i]["args"][j] , block_map_result[head_block][i]["type"] , block_map_result[head_block][i]["dest"]))
                                tbr.append(j)
                        tbr.sort(reverse=True)
                        for q in tbr:
                            block_map_result[head_block][i]["labels"].pop(q)
                            block_map_result[head_block][i]["args"].pop(q)
                        block_map_result[head_block][i]["labels"].append(block)
                        block_map_result[head_block][i]["args"].append(block_map_result[head_block][i]["dest"]+"_pre")

                for _, fixer in phis_to_fix_in_header.items():
                    
                    ar = []
                    lbls = []
                    for fix in fixer:
                        lbls.append(fix[0])
                        ar.append(fix[1])
                    new_instr = { "args": ar, "dest": fixer[0][3]+"_pre", "labels": lbls, "op": "phi", "type": fixer[0][2]}
                    block_map_result[block].insert(-1, new_instr)





        





        fn["instrs"] = reassemble(block_map_result)
        




    # UNCOMMENT LATER
    json.dump(prog, sys.stdout, indent=2)