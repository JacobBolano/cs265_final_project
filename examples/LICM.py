import json
import sys
from collections import defaultdict

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


if __name__ == "__main__":
    prog = json.load(sys.stdin)


    # enter each (main) function
    for fn in prog["functions"]:
    
        blocks = list(form_blocks(fn['instrs']))
        block_map_result = block_map(blocks)
        add_entry(block_map_result)
        add_terminators(block_map_result)

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
        for node, dom_by in dominance.items():
            for dominator in dom_by:
                # #print(node, dominator, dominate[dominator].intersection(dominance[node]))
                if dominator in preds[node] and (dominate[dominator].intersection(dominance[node]) - {node} == {dominator}):
                    dominator_tree[dominator].add(node)
        #print("Tree: ", dominator_tree)

        # create Dominance Frontier
        dominance_frontier = {v: set() for v in dominance}
        for dominator, dom_set in dominate.items():
            for dominated in dom_set:
                # if dominated != dominator: # this is for strict dominance !!TODO check this!! WE DONT NEED THIS
                for successor in succs[dominated]:
                    if successor not in dom_set:
                        dominance_frontier[dominator].add(successor)
        # print("Frontier: ", dominance_frontier)
                        
        # Finding Back Edges (A -> B, where B dominates A)
        backEdge_list = []
        for dominator, doms in dominate.items():
            for domed in doms:
                if dominator in succs[domed]:
                    backEdge_list.append((domed, dominator))
        print(backEdge_list)

        print(preds)
        print(succs)

          
        

                




        # #print(reassemble(block_map_result))
        fn["instrs"] = reassemble(block_map_result)
        




    # UNCOMMENT LATER
    # json.dump(prog, sys.stdout, indent=2)