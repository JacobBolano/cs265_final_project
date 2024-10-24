import json
import sys
from form_blocks import TERMINATORS, form_blocks
from cfg import block_map, add_terminators, add_entry, edges, reassemble
from collections import deque

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

def find_empty_list_value(d):
    for key, value in d.items():
        if value == []:
            return key
    return None  # If no empty list is found

def dict_intersection(dict1, dict2):
    # Get the intersection of the keys from both dictionaries
    common_keys = dict1.keys() & dict2.keys()
    # Create a new dictionary with common keys where values in dict1 and dict2 are the same
    return {key: dict1[key] for key in common_keys if dict1[key] == dict2[key]}



const_ops = set([
"add", "mul", "div", "eq", "le", "lt", "gt", "ge", "and", "or", "not", "id"
])

if __name__ == "__main__":
    prog = json.load(sys.stdin)


    # enter each (main) function
    for fn in prog["functions"]:
    
        blocks = list(form_blocks(fn['instrs']))
        block_map_result = block_map(blocks)
        add_entry(block_map_result)
        add_terminators(block_map_result)
        

        preds, succs = edges(block_map_result)
        # print(preds)
        # print(succs)
        # print(block_map_result)

        entry = find_empty_list_value(preds)

        ordered_keys = list(postorder_dfs(succs, entry))
        #add missing keys
        for key in block_map_result.keys():
            if key not in ordered_keys:
                ordered_keys.append(key)
        #start initialization of block facts
        ins = {}
        outs = {}
        worklist = deque()
        worklist_set = set()
        for key in ordered_keys:
            ins[key] = set()
            outs[key] = set()
            worklist.append(key)
            worklist_set.add(key)

        while len(worklist) != 0:
            b = worklist.popleft()
            worklist_set.remove(b)

            # meet over succs
            successors = succs[b]
            cur_out = set()
            if successors:
                cur_out = ins[successors[0]]
                for key in successors[1:]:
                    cur_out = cur_out.union(ins[key])
            outs[b] = cur_out.copy()
            
            # transfer function
            cur_in = cur_out.copy()
            
            
            changeFlag = False
            for i in range(len(block_map_result[b]) - 1, -1, -1):
                if "dest" in block_map_result[b][i] and block_map_result[b][i]["dest"] in cur_in:
                    cur_in.remove(block_map_result[b][i]["dest"])
                if "args" in block_map_result[b][i]:
                    for a in block_map_result[b][i]["args"]:
                        cur_in.add(a)
                
                
            
            if ins[b] != cur_in:
                changeFlag = True
            ins[b] = cur_in.copy()
            # print("finished ", b)
            # print("ins", ins)
            # print("outs", outs)
            # worklist successor extension
            if changeFlag:
                for p in preds[b]:
                    if p not in worklist_set:
                        worklist.appendleft(p)
                        worklist_set.add(p)
            # print(b, ins[b], outs[b])
        for b in block_map_result:
            new_block = []
        
            # transfer function
            cur = outs[b].copy()

            for i in range(len(block_map_result[b]) - 1, -1, -1):
                flag = True
                if "dest" in block_map_result[b][i] :
                    if block_map_result[b][i]["dest"] not in cur:
                        #new_block.append(block_map_result[b][i])
                        flag = False

                    cur.discard(block_map_result[b][i]["dest"])
                

                if "args" in block_map_result[b][i]:
                    # new_block.append(block_map_result[b][i])
                    for a in block_map_result[b][i]["args"]:
                        cur.add(a) 
                if flag:
                    new_block.append(block_map_result[b][i])


            block_map_result[b] = reversed(new_block)
            # print(block_map_result[b])
            #     if not ("dest" in block_map_result[b][i] and block_map_result[b][i]["dest"] not in ins[b] and block_map_result[b][i]["op"] != "call"):
            #         new_block.append(block_map_result[b][i])
            # block_map_result[b] = new_block
                    
            
        fn["instrs"] = reassemble(block_map_result)
        #print(fn["instrs"])






    # UNCOMMENT LATER
    json.dump(prog, sys.stdout, indent=2)