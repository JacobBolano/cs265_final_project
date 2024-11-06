import json
import sys
from form_blocks import TERMINATORS, form_blocks
from cfg import block_map, add_terminators, add_entry, edges, reassemble
from collections import deque, defaultdict


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


def dict_intersection(dict1, dict2):
    # Get the intersection of the keys from both dictionaries
    common_keys = dict1.keys() & dict2.keys()
    # Create a new dictionary with common keys where values in dict1 and dict2 are the same
    return {key: dict1[key] for key in common_keys if dict1[key] == dict2[key]}





if __name__ == "__main__":
    prog = json.load(sys.stdin)


    # enter each (main) function
    for fn in prog["functions"]:
        # print(fn["name"])
        function_args = []
        if "args" in fn:
            function_args = fn["args"]
        # print(function_args)
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


        instr_to_index = {}
        index_of_instr = 1
        for block in block_map_result:
            for i in range(len(block_map_result[block])):
                instr_to_index[json.dumps(block_map_result[block][i])] = index_of_instr
                index_of_instr += 1
        # print(instr_to_index)


        #start initialization of block facts
        ins = {}
        outs = {}
        worklist = deque()
        worklist_set = set()
        
        for key in ordered_keys:
            ins[key] = {}
            outs[key] = {}
            worklist.append(key)
            worklist_set.add(key)
        # print("ins", ins)
        # print("outs", outs)
        














        # # Use ins and outs to make dead store elimination optimizat
        # for block in block_map_result:
        #     cur = outs[block].copy()
        #     loaded_vals = set()
        #     for i in range(len(block_map_result[block]) - 1, -1, -1):
        #         flag = True
        #         if "op" in block_map_result[block][i] and block_map_result[block][i]["op"] == "load":
        #             for val  in cur[block_map_result[block][i]["args"][0]]:




        #         if "args" in block_map_result[block][i]:
        #             for a in block_map_result[block][i]["args"]:
        #                 if a in 



        fn["instrs"] = reassemble(block_map_result)
        # #print(fn["instrs"])






    # UNCOMMENT LATER
    json.dump(prog, sys.stdout, indent=2)