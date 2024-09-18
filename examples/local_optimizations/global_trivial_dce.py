import json
import sys


if __name__ == "__main__":
    prog = json.load(sys.stdin)



    # enter each (main) function
    for fn in prog["functions"]:
      
        # record prior to an iteration to see if there has been a change
        flag = True
        #print(fn["instrs"])
        while flag:
            old = fn["instrs"]
            # create a set of variables who's use we will monitor
            used = set()
            #iterate through the instructions backwards 
            #find all the variables needed for the print and remove ops that are not relevant to them
            for instr in fn["instrs"]:
                if "op" in instr and "args" in instr:
                    for arg in instr["args"]:
                        used.add(arg)
            #print(used)    
            for fn in prog["functions"]:
                fn["instrs"] = [instr for instr in fn["instrs"] if not ("dest" in instr and instr["dest"] not in used)]
            
            
            if fn["instrs"] == old:
                flag = False

        
    json.dump(prog, sys.stdout, indent=2)
