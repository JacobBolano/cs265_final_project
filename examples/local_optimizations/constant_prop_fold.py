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



def evaluate_operation(op, items):
    # Extract the constants from the list
    constants = [item[1] for item in items]
    
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





if __name__ == "__main__":
    prog = json.load(sys.stdin)


    # enter each (main) function
    for fn in prog["functions"]:
    #for fn in range (len(prog["functions"])):
        blocks = form_blocks(fn['instrs'])


        new_blocks = []
        
        for block in blocks:
            val2num = {}
            num2val = {}
            var2num = {}
            num2var = {}
            uniqueId = 1

            temp_references = {}

            for i in range(0, len(block) ): # for instruction block[i]
                if "op" in block[i] and (block[i]["op"] in TERMINATORS  or block[i]["op"] == "print") :
                    continue
                value = ""
                num = -1
                if "op" in block[i]:
                    # if the instr has arguemnts (sum, id, mult, div)
                    if "args" in block[i]:
                        #args = [var2num[arg] for arg in block[i]["args"]]
                        args = []
                        for arg in block[i]["args"]:
                            if not (arg in var2num or arg in temp_references): # symbolic case
                                num2val[uniqueId] = ("symbolic", str(uniqueId))
                                val2num[("symbolic", str(uniqueId))] = uniqueId
                                var2num[arg] = uniqueId
                                num2var[uniqueId] = arg

                                uniqueId += 1
                            
                            if arg in temp_references:
                                args.append( var2num[temp_references[arg]] )
                            else:
                                args.append( var2num[arg] )
                             
                                


                        
                        value = tuple([block[i]["op"]] + args)

                        # constant folding:
                        const_ops = set([
                            "add", "mul", "div", "eq", "le", "lt", "gt", "ge", "and", "or", "not"
                            ])
                        if block[i]["op"] in const_ops and all( num2val[n][0] == "const" for n in value[1:]) and not (block[i]["op"] == "div"  and num2val[value[2]][1] == 0):
                            inputs = [num2val[n] for n in value[1:]]
                            folding_result = evaluate_operation(block[i]["op"],  inputs)

                            # change the instruction
                            block[i] = {"dest": block[i]["dest"], "op": "const", "type": "bool" if isinstance(folding_result, bool) else "int", "value": folding_result}
                            
                            # update the state tables
                            num = uniqueId
                            value = tuple([block[i]["op"]] + [folding_result])
                            val2num[value] = num
                            num2val[num] = value
                            if block[i]["dest"] in var2num:
                                temp_name = block[i]["dest"]+"_temp"+str(uniqueId)
                                temp_references[block[i]["dest"]] = temp_name
                                block[i]["dest"] = temp_name
                                var2num[temp_name] = num
                                num2var[num] = temp_name
                            else:
                                var2num[ block[i]["dest"] ] = num
                                num2var[num] = block[i]["dest"]                                    
                            uniqueId += 1
                            #continue to next instruction
                            continue


                    elif block[i]["op"] == "const":
                        value = tuple(["const"]+[block[i]["value"]])

                    if value not in val2num:
                        num = uniqueId
                        val2num[value] = num
                        num2val[num] = value
                        uniqueId += 1
                        
                    else:
                        num = val2num[value]
                        if num2var[num] in temp_references: # its clobbered
                            pass
                        else: # eliminate-able common subexpression
                            block[i]["op"] = "id"
                            block[i]["args"] = [num2var[num]]

                    if block[i]["dest"] in var2num:
                        temp_name = block[i]["dest"]+"_temp"+str(uniqueId)
                        uniqueId +=1
                        

                        temp_references[block[i]["dest"]] = temp_name
                        block[i]["dest"] = temp_name

                        var2num[temp_name] = num
                        num2var[num] = temp_name
                    
                    else:
                        var2num[ block[i]["dest"] ] = num
                        num2var[num] = block[i]["dest"]
                        

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