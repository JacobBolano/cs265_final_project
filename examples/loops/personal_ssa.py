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
        function_args = []
        if "args" in fn:
            function_args = fn["args"]

        blocks = list(form_blocks(fn['instrs']))
        block_map_result = block_map(blocks)
        add_entry(block_map_result)
        add_terminators(block_map_result)

        preds, succs = edges(block_map_result)

        # modified for mutliple blocks with no preds. we want the first one.
        entry = find_empty_list_value(preds, block_map_result)
        # print("entry", entry)
        # print("preds", preds)

        # remove false starts (blocks that have no preds and arent the entry):
        to_be_deleted =[]
        for p in preds:
            if len(preds[p]) ==0 and p != entry:
                to_be_deleted.append(p)
        del_flag = True
        while del_flag:
            del_flag = False
        for p in preds:
            if p not in to_be_deleted and all(elem in to_be_deleted for elem in preds[p]) and p!= entry:
                del_flag= True
                to_be_deleted.append(p)
        for bad_blocks in to_be_deleted:
            del block_map_result[bad_blocks]
        
        #recompute:
        preds, succs = edges(block_map_result)



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
        # print("dominance", dominance)

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

        # print("Tree: ", dominator_tree)

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


        defs = def_blocks(block_map_result)
        # print(defs)

        types = get_types(fn)
        #print("types:", types)


        # map to see where the phis are per variable
        phi_map = {d: set() for d in defs } # phi[var] = [block1, ...]
        
        phi_placement_flag = True
        while phi_placement_flag:
            phi_placement_flag = False
            defs_to_be_added = {d: set() for d in defs}
            for v in defs:
                for defining_block in defs[v]:
                    for block in dominance_frontier[defining_block]:
                        if not (block in phi_map[v]):
                            # we need to create the instruction for the first time
                            phi_placement_flag = True

                            phi_map[v].add(block)
                            new_instr = { "args": [], "dest": v, "labels": [], "op": "phi", "type": types[v]}

                            block_map_result[block] = [new_instr] + block_map_result[block]
                            defs_to_be_added[v].add(block)
            for d, blocks_to_be_added in defs_to_be_added.items():
                for btba in blocks_to_be_added:
                    defs[d].add(btba)

                    


        # print(block_map_result)
        
        # fill in the phis
        stack = {v: [] for v in defs}  # SHOULD LISTS BE EMPTY??
        for f_arg in function_args:
            stack[f_arg["name"]] = [f_arg["name"]]
        counter = {v:0 for v in defs}
        for f_arg in function_args:
            counter[f_arg["name"]] = 1
        nameTrackBack = {v:v for v in defs}
        def rename(b):
            # print("b, ", b)
            num_pushes = {v: 0 for v in defs}
            for i in range(len(block_map_result[b])):
                # print(i, "______________________________")
                # print(block_map_result[b][i])
                if "args" in block_map_result[b][i] and "phi" !=  block_map_result[b][i]["op"]:
                    arguments = block_map_result[b][i]["args"]
                    #print(arguments)
                    for j in range(len(arguments)):
                        arguments[j] = stack[arguments[j]][-1]
                    #print(arguments)
                    block_map_result[b][i]["args"] = arguments
                    # #print("args done ",block_map_result[b][i])
                
                # #print("what happened?", block_map_result[b][i])
                # print("early mid stack: ",stack)

                if "dest" in block_map_result[b][i]:
                    # print(block_map_result[b][i]["dest"] )
                    fresh = block_map_result[b][i]["dest"] + "_"+str(counter[block_map_result[b][i]["dest"]])
                    counter[block_map_result[b][i]["dest"]] += 1
                    nameTrackBack[fresh] = block_map_result[b][i]["dest"]
                    
                    stack[block_map_result[b][i]["dest"]].append(fresh)
                    num_pushes[block_map_result[b][i]["dest"]] = num_pushes[block_map_result[b][i]["dest"]] + 1

                    block_map_result[b][i]["dest"] = fresh
                #     print(block_map_result[b][i])
                # print("mid stack: ",stack)

            # print("sucessors: ", succs[b])     

            for succ in succs[b]:
                index = 0
                while "op" in block_map_result[succ][index] and block_map_result[succ][index]["op"] == "phi":
                    # print(block_map_result[succ][index]["dest"])
                    # print("entered")
                    # print("nameTrackBack: ", nameTrackBack)
                    if (block_map_result[succ][index]["dest"] in nameTrackBack) :
                        
                        trackedBack = nameTrackBack[block_map_result[succ][index]["dest"]] 
                        if (len(stack[trackedBack]) != 0):
                            block_map_result[succ][index]["args"].append(stack[trackedBack][-1])
                            block_map_result[succ][index]["labels"].append(b)
                        else: # this is for the case where the stack is empty
                            block_map_result[succ][index]["args"].append("__undefined")
                            block_map_result[succ][index]["labels"].append(b)
                    index += 1
            # print("end stack: ",stack)
            # print(b, block_map_result[b])        
            for child in dominator_tree[b]:
                rename(child)


            #clear the stack to maintain it
            for var, cnt in num_pushes.items():
                for i in range (cnt):
                    stack[var].pop()



        rename(entry)            
        

                




        # print(reassemble(block_map_result))
        fn["instrs"] = reassemble(block_map_result)
        




    # UNCOMMENT LATER
    json.dump(prog, sys.stdout, indent=2)