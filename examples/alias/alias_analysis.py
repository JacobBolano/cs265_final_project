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
        
        # add the "__all__" for the function args
        for f_arg in function_args:
            if type(f_arg['type']) is dict:
                # print(f_arg['name'])
                ins[entry][f_arg['name']] = set(["__all__"])
        # print("ins", ins)
        # print("outs", outs)

        while len(worklist) != 0:
            b = worklist.popleft()
            worklist_set.remove(b)

            # meet over preds
            predecessors = preds[b]
            cur_in = ins[b].copy()
            if predecessors:
                for p in predecessors:
                    for pred_name in outs[p].keys():
                        if pred_name not in cur_in:
                            cur_in[pred_name] = set()
                        for item in outs[p][pred_name]:
                            cur_in[pred_name].add(item)
            
            ins[b] = cur_in.copy()
            # transfer function
            cur_out = cur_in.copy()
            
            
            changeFlag = False
            for i in range(len(block_map_result[b])):

                # if alloc
                if "op" in block_map_result[b][i] and block_map_result[b][i]["op"] == "alloc":
                    cur_out[block_map_result[b][i]["dest"]] = set( [ instr_to_index[json.dumps(block_map_result[b][i])] ] )

    
                # if ptradd
                if "op" in block_map_result[b][i] and block_map_result[b][i]["op"] == "ptradd":
                    add_from = block_map_result[b][i]["args"][0]
                    add_to = block_map_result[b][i]["dest"]
                    if add_to not in cur_out:
                        cur_out[add_to] = set()
                    for trans in cur_out[add_from]:
                        cur_out[add_to].add(trans)

                # if ptr id
                if ("op" in block_map_result[b][i] and block_map_result[b][i]["op"] == "id" and 
                    type(block_map_result[b][i]["type"]) is dict and "ptr" in block_map_result[b][i]["type"] ):

                    add_from = block_map_result[b][i]["args"][0]
                    add_to = block_map_result[b][i]["dest"]
                    if add_to not in cur_out:
                        cur_out[add_to] = set()
                    for trans in cur_out[add_from]:
                        cur_out[add_to].add(trans)

                    

                # if ptr ptr load or a function cal returning a pointer
                
                if "op" in block_map_result[b][i] and block_map_result[b][i]["op"] in ["load", "call"] and "type" in block_map_result[b][i] and  type(block_map_result[b][i]["type"]) is dict and "ptr" in block_map_result[b][i]["type"]:
                    add_to = block_map_result[b][i]["dest"]
                    if add_to not in cur_out:
                        cur_out[add_to] = set()
                    cur_out[add_to].add("__all__")

                


            
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

        # print("ins: ", ins) 
        # print("outs: ", outs) 



        # do a reverse load liveness analysis:
        entry = find_empty_list_value(preds, block_map_result)
        ordered_keys = list(postorder_dfs(succs, entry))
        #add missing keys
        for key in block_map_result.keys():
            if key not in ordered_keys:
                ordered_keys.append(key)
        #start initialization of block facts
        ins_liveness = {}
        outs_liveness = {}
        worklist_liveness = deque()
        worklist_set_liveness = set()
        for key in ordered_keys:
            ins_liveness[key] = set()
            outs_liveness[key] = set()
            worklist_liveness.append(key)
            worklist_set_liveness.add(key)
        while len(worklist_liveness) != 0:
            b = worklist_liveness.popleft()
            worklist_set_liveness.remove(b)

            # meet over succs
            successors_liveness = succs[b]
            cur_out_liveness = set()
            if successors_liveness:
                cur_out_liveness = ins_liveness[successors_liveness[0]]
                for key in successors_liveness[1:]:
                    cur_out_liveness = cur_out_liveness.union(ins_liveness[key])
            outs_liveness[b] = cur_out_liveness.copy()

            # transfer function
            cur_in_liveness = cur_out_liveness.copy()
            
            
            changeFlag_liveness = False
            for i in range(len(block_map_result[b]) - 1, -1, -1):
                if "op" in block_map_result[b][i] and block_map_result[b][i]["op"]=="load":
                    ptr = block_map_result[b][i]["args"][0]
                    for adr in outs[b][ptr]:
                        cur_in_liveness.add(adr)
                if "op" in block_map_result[b][i] and block_map_result[b][i]["op"]=="call":
                    if "args" in block_map_result[b][i]:
                        for a in block_map_result[b][i]["args"]:
                            if a in outs[b]:
                                for adr in outs[b][a]:
                                    cur_in_liveness.add(adr)
                if "op" in block_map_result[b][i] and block_map_result[b][i]["op"]=="ret": #and "type" in fn and type(fn["type"]) is dict and "ptr" in fn["type"]:
                   if "args" in block_map_result[b][i]:
                        for a in block_map_result[b][i]["args"]:
                            if a in outs[b]:
                                for adr in outs[b][a]:
                                    cur_in_liveness.add(adr)
                
                
                
            
            if ins_liveness[b] != cur_in_liveness:
                changeFlag_liveness = True
            ins_liveness[b] = cur_in_liveness.copy()

            if changeFlag_liveness:
                for p in preds[b]:
                    if p not in worklist_set_liveness:
                        worklist_liveness.append(p)
                        worklist_set_liveness.add(p)
        
        # print("ins_liveness: ", ins_liveness)
        # print("outs_liveness: ", outs_liveness)

        
        
        for b in block_map_result:
            new_block = []
        
            # transfer function
            cur_liveness = outs_liveness[b].copy()
            stores = set()

            for i in range(len(block_map_result[b]) - 1, -1, -1):
                flag = True
                if "op" in block_map_result[b][i] and block_map_result[b][i]["op"] == "store":
                    where_pointer_could_point = outs[b][block_map_result[b][i]["args"][0]]
                    if where_pointer_could_point.isdisjoint(cur_liveness) and ("__all__" not in where_pointer_could_point):
                        flag = False
                    if block_map_result[b][i]["args"][0] in stores:
                        flag = False
                    stores.add(block_map_result[b][i]["args"][0])


                if "op" in block_map_result[b][i] and block_map_result[b][i]["op"]=="load":
                    ptr = block_map_result[b][i]["args"][0]
                    for adr in outs[b][ptr]:
                        cur_liveness.add(adr)
                    stores.discard(ptr)
                if "op" in block_map_result[b][i] and block_map_result[b][i]["op"]=="call":
                    if "args" in block_map_result[b][i]:
                        for a in block_map_result[b][i]["args"]:
                            if a in outs[b]:
                                for adr in outs[b][a]:
                                    cur_liveness.add(adr)
                                stores.discard(a)
                if "op" in block_map_result[b][i] and block_map_result[b][i]["op"]=="ret": #and "type" in fn and type(fn["type"]) is dict and "ptr" in fn["type"]:
                   if "args" in block_map_result[b][i]:
                        for a in block_map_result[b][i]["args"]:
                            if a in outs[b]:
                                for adr in outs[b][a]:
                                    cur_liveness.add(adr)
                                stores.discard(a)
                if flag:
                    new_block.append(block_map_result[b][i])
                # else:
                    # print(fn["name"], b, i)


            block_map_result[b] = reversed(new_block)









        fn["instrs"] = reassemble(block_map_result)
        # #print(fn["instrs"])






    # UNCOMMENT LATER
    json.dump(prog, sys.stdout, indent=2)