import json
import sys
from collections import defaultdict

from cfg import block_map, successors, add_terminators, add_entry, reassemble, edges
from form_blocks import form_blocks

if __name__ == "__main__":
    prog = json.load(sys.stdin)


    # enter each (main) function
    for fn in prog["functions"]:
        function_args = []
        if "args" in fn:
            function_args = fn["args"]

        blocks = list(form_blocks(fn['instrs']))
        block_map_result = block_map(blocks)
     
        
        for block in block_map_result:
            indices_to_remove = []
            for i in range(len(block_map_result[block])):
                if "op" in block_map_result[block][i] and block_map_result[block][i]["op"] == "phi":
                    indices_to_remove.append(i)
                    for j in range (len(block_map_result[block][i]["labels"])):
                        phi_arg = block_map_result[block][i]["args"][j]
                        phi_dest = block_map_result[block][i]["dest"]
                        if phi_arg != "__undefined" and phi_arg != phi_dest:
                            phi_label = block_map_result[block][i]["labels"][j]
                            
                            
                            phi_type = block_map_result[block][i]["type"]
                            new_instr = {"args": [phi_arg],"dest": phi_dest,"op": "id","type": phi_type}
                            block_map_result[phi_label].insert(-1, new_instr)
            indices_to_remove.sort(reverse=True)
            for index in indices_to_remove:
                block_map_result[block].pop(index)
                




        # print(reassemble(block_map_result))
        fn["instrs"] = reassemble(block_map_result)
        




    # UNCOMMENT LATER
    json.dump(prog, sys.stdout, indent=2)