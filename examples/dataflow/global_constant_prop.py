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


def evaluate_operation(op, constants):
    
    # Handle operations
    if op == "add":
        return sum(constants)
    elif op == "mul":
        result = 1
        for const in constants:
            result *= const
        return result
    elif op == "div":
        return constants[0] / constants[1]
    elif op == "eq":
        return constants[0] == constants[1]
    elif op == "le":
        return constants[0] <= constants[1]
    elif op == "lt":
        return constants[0] < constants[1]
    elif op == "gt":
        return constants[0] > constants[1]
    elif op == "ge":
        return constants[0] >= constants[1]
    elif op == "and":
        return all(constants)
    elif op == "or":
        return any(constants)
    elif op == "not":
        return not constants[0]
    elif op == "id":
        return constants[0]

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
        
        



        # tbd = []
        # for key , blk in block_map_result.items():
        #     if blk == []:
        #         tbd.append(key)
        # for key in tbd:
        #     del block_map_result[key]
        # print(block_map_result)


        preds, succs = edges(block_map_result)
        # print(preds)
        # print(succs)
        

        entry = find_empty_list_value(preds)

        ordered_keys = list(reversed(postorder_dfs(succs, entry)))
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
            ins[key] = {}
            outs[key] = {}
            worklist.append(key)
            worklist_set.add(key)
        # print("ins", ins)
        # print("outs", outs)

        while len(worklist) != 0:
            b = worklist.popleft()
            worklist_set.remove(b)

            # meet over preds
            predecessors = preds[b]
            cur_in = {}
            if predecessors:
                # print(predecessors)
                # print(outs)
                cur_in = outs[predecessors[0]]
                for key in predecessors[1:]:
                    cur_in = dict_intersection(cur_in, outs[key])
            ins[b] = cur_in.copy()
            # transfer function
            cur_out = cur_in.copy()
            
            
            changeFlag = False
            for i in range(len(block_map_result[b])):
                
                if "op" in block_map_result[b][i] and block_map_result[b][i]["op"] in const_ops:
                    if "args" in block_map_result[b][i] and all(arg in cur_out for arg in block_map_result[b][i]['args']) :

                        argVals = [cur_out[arg] for arg in block_map_result[b][i]['args']]
                        result = evaluate_operation(block_map_result[b][i]["op"], argVals)

                        block_map_result[b][i] = {"dest": block_map_result[b][i]["dest"], "op": "const", "type": "bool" if isinstance(result, bool) else "int", "value": result}
                        cur_out[block_map_result[b][i]["dest"]] = result
                        #changeFlag = True
                elif "op" in block_map_result[b][i] and block_map_result[b][i]["op"] == "const":
                    cur_out[block_map_result[b][i]["dest"]] =  block_map_result[b][i]["value"]                   
                    # print("entered")
            
            if outs[b] != cur_out:
                changeFlag = True
            outs[b] = cur_out.copy()
            # print("finished ", b)
            # print("ins", ins)
            # print("outs", outs)
            # worklist successor extension
            if changeFlag:
                # print("succs happening", succs[b])
                for s in succs[b]:
                    if s not in worklist_set:
                        worklist.append(s)
                        worklist_set.add(s)
            

        fn["instrs"] = reassemble(block_map_result)
        #print(fn["instrs"])






    # UNCOMMENT LATER
    json.dump(prog, sys.stdout, indent=2)