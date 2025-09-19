# input: variable count, cutting size, cutting type
# output: clauses required for xor chain and variable count

import os
import subprocess
import sys
import time

script_dir = os.path.dirname(os.path.abspath(__file__))
clauses_path = os.path.join(script_dir, "xor_clauses.cnf")

clauses = []

relation_type = [4,4,4,4]
net_classes = 4
net_order = 10

row_length = net_classes * net_order
col_length = net_order * net_order

order = sum(relation_type)
cutting_size = 4
cutting_type = "Linear"

overwrite_variables = []
variable_offset = row_length * col_length

auxiliary_variables = 0
variable_list = [] 
chains = []
    
for i in range(len(relation_type)):
    for j in range(relation_type[i]):
        overwrite_variables.append(i * net_order + j + 1) 

def updateClauses(): # update the clauses.cnf file
    with open(clauses_path, "w") as f:
        for i in range(col_length): # iterate for each row
            for clause in clauses:
                mapped = []
                for var in clause:
                    isNegative = var < 0
                    if abs(var) <= order:  # main variable
                        new_var = overwrite_variables[abs(var) - 1] + row_length * i # offset by index
                        if isNegative:
                            new_var *= -1
                        mapped.append(str(new_var))
                    else:  # auxiliary variable
                        new_var = abs(var) + variable_offset - order + auxiliary_variables * i # offset such that auxiliary_variables are not reused
                        if isNegative:
                            new_var *= -1
                        mapped.append(str(new_var))
                f.write(" ".join(mapped) + "\n") # + " 0\n" not needed since we will add that in our generate.py script
            # f.write("\n")

def getCombinations(totalList, array, n, currentRemovals): # n >= 0, generate all possible combinations from n choices
    if n == 0:
        totalList.append(currentRemovals)
    else: 
        for i in range(len(array)):
            tmpList = array[i + 1 : len(array)]
            removals = currentRemovals.copy()
            removals.append(array[i])
            getCombinations(totalList, tmpList, n - 1, removals)

def add_xor_clauses(chain): # create XOR clauses for given chain, should add 2^(len(chain) - 1) clauses for XOR
    for notCount in range(0, len(chain) + 1, 2):
        total = []
        getCombinations(total, list(range(len(chain))), notCount, [])
        for i in range(len(total)):
            tmpChain = chain.copy()
            for j in range(len(total[i])):
                tmpChain[total[i][j]] = -tmpChain[total[i][j]]
            clauses.append(tmpChain) 
            print("    Added clause:", tmpChain)

def recursive_xor(): # create XOR chains
    global auxiliary_variables
    if len(variable_list) <= cutting_size:
        variable_list[0] = -variable_list[0]
        chains.append(variable_list)
    else:
        tempList = []
        for i in range(cutting_size):
            if i + 1 == cutting_size:
                auxiliary_variables += 1
                auxiliary = order + auxiliary_variables
                tempList.append(-auxiliary)
                if cutting_type == "Pooled":
                    variable_list.append(auxiliary)
                else:
                    variable_list.insert(0, auxiliary)
            else:
                tempList.append(variable_list.pop(0))
        chains.append(tempList)
        recursive_xor()

for i in range(order):
    variable_list.append(i + 1)

recursive_xor()
print(f"Input parameters: order {order}, cutting size {cutting_size}, cutting style \"{cutting_type}\".")
print("Variables Mapped to:", overwrite_variables)
print("\nXOR Chains:",chains)
for i in range(len(chains)):
    add_xor_clauses(chains[i])

updateClauses()

print(f"\nGenerated {len(clauses)} (Total: {len(clauses) * col_length}) XOR clauses by introducing {auxiliary_variables} (Total: {auxiliary_variables * col_length}) auxiliary variable(s).")
print(f"Wrote clauses to: {clauses_path}")

# cd /mnt/g/Code/sat\ solver\ stuff/stinson\ xor
