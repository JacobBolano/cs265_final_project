import json
import sys
from collections import defaultdict, OrderedDict

from cfg import block_map, successors, add_terminators, add_entry, reassemble, edges
from form_blocks import form_blocks

# ASSUMES THAT LOOP NORMALIZATION HAS OCCURRED AND SSA CODE THAT WAS LOOP NORMALIZED IS THE INPUT!


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
        for dominator, doms in dominate.items():
            for domed in doms:
                if dominator in succs[domed]:
                    backEdge_list.append((domed, dominator))


        #find all the blocks that are associated with each loop
        loops = {} # map from backedge to loop-involved blocks
        for be in backEdge_list:
            loops[be] = loop_blocks_by_backEdge(preds, be[0], be[1])




        # ESTABLISHING ORDER
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
        

        
        # function to remove overlapping (nested) loops since post_order traversal should take care of nested loop ordering
        def reduce_dict(d):
            keys_to_remove = set()

            for key1, value1 in d.items():
                for key2, value2 in d.items():
                    if key1 != key2 and set(value1).issubset(set(value2)):
                        keys_to_remove.add(key1)

            return {key: value for key, value in d.items() if key not in keys_to_remove}

        
        filtered_nested_loops = reduce_dict(loops_sorted_lists)
        
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

        print(reorder_postorder(postorder, filtered_nested_loops))


        fn["instrs"] = reassemble(block_map_result)
        




    # UNCOMMENT LATER
    # json.dump(prog, sys.stdout, indent=2)