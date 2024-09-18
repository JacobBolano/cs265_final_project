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

    # new 

    # enter each (main) function
    for fn in prog["functions"]:
    #for fn in range (len(prog["functions"])):
        blocks = form_blocks(fn['instrs'])


        new_blocks = []
        
        for block in blocks:
            # print("before", block)
            # record prior to an iteration to see if there has been a change
            flag = True
            while flag:
                flag = False
                old = block
                # create a set of variables who's use we will monitor
                unused = {}

                # instructions that need to be removed
                inst_to_be_removed = []
                
                # If the variable is used, 
                for i in range(0, len(block)): # for instruction block[i]
                    
                    # if its used, its not unused
                    if "args" in block[i]:
                        for argument in block[i]["args"]:
                            
                            unused.pop(argument, None)

                    # if the instruction defines something,
                    # we can kill the unused definitions
                    if "dest" in block[i]:
                        if block[i]["dest"] in unused:
                            inst_to_be_removed.append(unused[block[i]["dest"]])
                    
                    # mark the new def as unused for now
                        unused[block[i]["dest"]] = i
                
                # now we remove all of the clobbered unused instructions
                inst_to_be_removed = sorted(inst_to_be_removed, reverse = True) # sorting to make deletions not affect each other

                for index in inst_to_be_removed:
                    del block[index]
                    flag = True
                   
            # print("after", block)
            new_blocks.append(block)


        # for block in new_blocks:
        #     print(block)
        fn["instrs"] = [item for sublist in new_blocks for item in sublist]
    
    
    # UNCOMMENT LATER
    json.dump(prog, sys.stdout, indent=2)
