# input: variable count, cutting size, cutting type
# output: clauses required for xor chain and variable count

# MODIFIED VERSION OF SCRIPT, USED ONLY FOR 4-NET(6)

import os
import subprocess
import sys
import time

script_dir = os.path.dirname(os.path.abspath(__file__))
clauses_path = os.path.join(script_dir, "xor_clauses.cnf")

clauses = []

order = 36
cutting_size = 4
cutting_type = "Linear"

solutionsOnly = True

overwrite_variables = []

# 2-net(6) with 6^2 = 36 order, we duplicate it 8 times to fill out all required columns as seen in updateClauses' inner workings. 
# if all constraints we get 0 then it means linear depedence exists, otherwise no dependence relation exists. Its shown in stinson's paper that the 4th linear dependence relation doesnt exist so we expect 1.
# what we are encoding is the search for linear independence (1) which would prove that 4-net(6) exists. We already know, from stinson's paper, that this will be UNSAT
for i in range(0, 6 ** 2):
    overwrite_variables.append(i * 4 * 6 + 1)

auxiliary_variables = 0
variable_list = [] 
chains = []

def updateClauses(): # update the clauses.cnf file
    with open(clauses_path, "w") as f:
        for clause in clauses:
            for i in range(4): # iterate for r, c, s, t
                for j in range(2): # iterate for index x_0, x_1; where x is r, c, s, or t
                    mapped = []
                    for var in clause:
                        isNegative = var < 0
                        if abs(var) <= order:  # main variable
                            new_var = overwrite_variables[abs(var) - 1] + i * 6 + j # offset by index and column selected
                            if isNegative:
                                new_var *= -1
                            mapped.append(str(new_var))
                        else:  # auxiliary variable
                            new_var = abs(var) + 864 - 36 + auxiliary_variables * (i * 2 + j) # offset such that auxiliary_variables are not reused
                            if isNegative:
                                new_var *= -1
                            mapped.append(str(new_var))
                    f.write(" ".join(mapped) + "\n") # + " 0\n" not needed since we will add that in our generate.py script

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
        if solutionsOnly == False:
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
print(f"Input parameters: order {order}, cutting size {cutting_size}, cutting style \"{cutting_type}\", only solutions \"{solutionsOnly}\".")
print("\nXOR Chains:",chains)
for i in range(len(chains)):
    add_xor_clauses(chains[i])

updateClauses()

print(f"\nGenerated {len(clauses)} XOR clauses by introducing {auxiliary_variables} auxiliary variable(s).")
print(f"Wrote clauses to: {clauses_path}")

# cd /mnt/g/Code/sat\ solver\ stuff/stinson\ xor