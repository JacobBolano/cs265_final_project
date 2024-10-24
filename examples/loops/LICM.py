import json
import sys
from collections import defaultdict, OrderedDict

from cfg import block_map, successors, add_terminators, add_entry, reassemble, edges
from form_blocks import form_blocks


const_ops = set([
"add", "sub", "mul", "div", "eq", "le", "lt", "gt", "ge", "and", "or", "not", "id"
])



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
    for key in ord_dict.keys():
        if d.get(key) == []:
            return key
    return None  # If no empty list is found

def postorder_dfs(graph, start, visited=None, postorder_list=None, in_process=None):
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


def loop_blocks_by_backEdge(preds, N, Header):
    reachable_blocks = set()
    stack = [N]
    visited = set()
    while stack:
        # Get the current block
        current_block = stack.pop()
        if current_block in visited:
            continue
        visited.add(current_block)
        if current_block == Header:
            continue
        reachable_blocks.add(current_block)
        for pred in preds.get(current_block, []):
            if pred not in visited:
                stack.append(pred)
        # add header to complete loop
        reachable_blocks.add(Header)
    return reachable_blocks


if __name__ == "__main__":
    prog = json.load(sys.stdin)


    # enter each (main) function
    for fn in prog["functions"]:
    
        blocks = list(form_blocks(fn['instrs']))
        block_map_result = block_map(blocks)
        # add_entry(block_map_result)
        # add_terminators(block_map_result)

        preds, succs = edges(block_map_result)

        # modified for mutliple blocks with no preds. we want the first one.
        entry = find_empty_list_value(preds, block_map_result)

        ordered_keys = list(reversed(postorder_dfs(succs, entry)))
        #add missing keys
        for key in block_map_result.keys():
            if key not in ordered_keys:
                ordered_keys.append(key)

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
        #print("dominance", dominance)

        # REMEMBER: dominance[v] is "who dominates v"


        # Initialize the dominate dictionary
        # REMEMBER: dominate [v] is "who v dominates"
        dominate = {v: set() for v in dominance}

        # Populate the dominate dictionary
        for dominated, dominators in dominance.items():
            for dominator in dominators:
                dominate[dominator].add(dominated)

        # #print the resulting dominate dictionary
        # print("dominate", dominate)

        dominator_tree = {}
        for v in succs:
            dominator_tree[v] =set()
        for dominator, dom_set in dominate.items():
            # print("_________________________________________")
            dom_tree_children = dom_set.difference({dominator})
            # print("before subtractions: ", dom_tree_children)
            for dominated in dom_set:
                if dominator != dominated:
                    dominated_strict_dom_set = dominate[dominated].difference({dominated})
                    # print("subtracting this: ", dominated, ":", dominated_strict_dom_set)
                    dom_tree_children = dom_tree_children.difference(dominated_strict_dom_set)
                    # print("results in : ", dom_tree_children)
            dominator_tree[dominator] = dom_tree_children

        #print("Tree: ", dominator_tree)

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

        # print("Frontier: ", dominance_frontier)
                        
        # Finding Back Edges (A -> B, where B dominates A)
        backEdge_list = []
        for dominator, doms in dominate.items():
            for domed in doms:
                if dominator in succs[domed]:
                    backEdge_list.append((domed, dominator))
        # print(backEdge_list)

        # print(preds)
        # print(succs)

        #find all the blocks that are associated with each loop
        loops = {} # map from backedge to loop-involved blocks
        for be in backEdge_list:
            loops[be] = loop_blocks_by_backEdge(preds, be[0], be[1])
        # print(loops)


        # sort the loops based on length so that inner ones are processed first
        sorted_loops = sorted(loops.items(), key=lambda item: len(item[1]))


        # iterate through the loops and ...
        for be, loop_blocks in sorted_loops:
            # print(be, loop_blocks)
            #create a dict of loop blocks so that we can find all of the defs
            temp_loop_dict = {}
            for b in loop_blocks:
                temp_loop_dict[b] = block_map_result[b]
            defs = def_blocks(temp_loop_dict)
            # print("defs of", be, " :", defs)
            
            head = be[1]
            preheader = head+"_preheader"
            # print("preheader", preheader)
            
            count =0 
            #iterate to fixed point
            change_happened = True
            while change_happened:
                # count += 1
                # if count > 6: break
                # set of instructions to be hoisted by block by index
                to_be_hoisted = {b: [] for b in loop_blocks}
                
                change_happened = False
                
                # iterate over each blocks instr
                order_to_hoist = []
                # print("order houst", order_to_hoist)
                for block in loop_blocks:
                    order_to_hoist.append(block)
                    for i in range(len(block_map_result[block])):
                        if "op" in block_map_result[block][i] and block_map_result[block][i]["op"] == "const":
                            to_be_hoisted[block].append(i)
                            change_happened = True
                            # print(b,i)
                        elif "op" in block_map_result[block][i] and block_map_result[block][i]["op"] in const_ops:
                            invariant_args = True
                            for a in block_map_result[block][i]["args"]:
                                if a in defs:
                                    invariant_args = False
                            if invariant_args:
                                to_be_hoisted[block].append(i)
                                change_happened = True
                                # print(b,i)
                    
            


                #hoisting
                # print(order_to_hoist)
                
                for block in order_to_hoist:
                    # count += 1
                    # if count > 6: break
                    # print("endtered")
                    # create a list of instructions to be added to 
                    indices_to_hoist = to_be_hoisted[block]
                    instrs_to_hoist = [block_map_result[block][ind] for ind in indices_to_hoist]
                    block_map_result[preheader] = block_map_result[preheader][:-1] + instrs_to_hoist + [block_map_result[preheader][-1]]

                    #remember to do in reverse order to not mess up indices!!    
                    reversed_hoist_indices = indices_to_hoist[::-1]
                    for rev_ind in reversed_hoist_indices:
                        del block_map_result[block][rev_ind]
                    # print("after hoist", block, block_map_result[block])
                






        # #print(reassemble(block_map_result))
        fn["instrs"] = reassemble(block_map_result)
        




    # UNCOMMENT LATER
    json.dump(prog, sys.stdout, indent=2)