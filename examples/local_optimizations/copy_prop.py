import json
import sys

# Instructions that terminate a basic block.
TERMINATORS = 'br', 'jmp', 'ret'


def form_blocks(instrs):
    """Given a list of Bril instructions, generate a sequence of
    instruction lists representing the basic blocks in the program.

    Every instruction in `instr` will show up in exactly one block. Jump
    and branch instructions may only appear at the end of a block, and
    control can transfer only to the top of a basic block---so labels
    can only appear at the *start* of a basic block. Basic blocks may
    not be empty.
    """

    # Start with an empty block.
    cur_block = []

    for instr in instrs:
        if 'op' in instr:  # It's an instruction.
            # Add the instruction to the currently-being-formed block.
            cur_block.append(instr)

            # If this is a terminator (branching instruction), it's the
            # last instruction in the block. Finish this block and
            # start a new one.
            if instr['op'] in TERMINATORS:
                yield cur_block
                cur_block = []

        else:  # It's a label.
            # End the block here (if it contains anything).
            if cur_block:
                yield cur_block

            # Start a new block with the label.
            cur_block = [instr]

    # Produce the final block, if any.
    if cur_block:
        yield cur_block




if __name__ == "__main__":
    prog = json.load(sys.stdin)


    operations_that_modify_dest = set([
    "add",
    "mul",
    "div",
    "const",
    "eq",
    "le",
    "lt",
    "gt",
    "ge",
    "and",
    "or",
    "not",
    #"id"
    ])

    # enter each (main) function
    for fn in prog["functions"]:
    #for fn in range (len(prog["functions"])):
        blocks = form_blocks(fn['instrs'])


        new_blocks = []
        
        for block in blocks:
            equivalences = {}
            for i in range(0, len(block)): # for instruction block[i]

                # print(equivalences)
                if "op" in block[i]  and  block[i]["op"] == "id":
                    
                    #print(block[i]["dest"], block[i]["args"][0])
                    if block[i]["args"][0] in equivalences:
                        equiv = equivalences[block[i]["args"][0]]
                        block[i]["args"] = [ equiv ]
                        equivalences[block[i]["dest"]] = equiv
                    else:
                         equivalences[block[i]["dest"]] = block[i]["args"][0]


                elif "op" in block[i]  and  block[i]["op"] in operations_that_modify_dest:  
                    if "args" in block[i]:
                        block[i]["args"] = [equivalences[arg] if (arg in equivalences) else arg for arg in block[i]["args"]]
                    equivalences.pop(block[i]["dest"], None)# clobbered

                        

            # print("val2num", val2num)
            # print("num2val", num2val)
            # print("var2num", var2num)
            # print("num2var", num2var)

                   
            
            new_blocks.append(block)


        # for block in new_blocks:
        #     print(block)
        fn["instrs"] = [item for sublist in new_blocks for item in sublist]
    
    
    # UNCOMMENT LATER
    json.dump(prog, sys.stdout, indent=2)
