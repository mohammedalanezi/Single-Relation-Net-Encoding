import os
import subprocess
import sys
import time

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)
input_path = os.path.join(script_dir, "input.cnf")
output_path = os.path.join(script_dir, "output.txt")
proof_path = os.path.join(script_dir, "proof.txt")
clauses_path = os.path.join(script_dir, "xor_clauses.cnf")
kissat_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat") # Before testing: Update this to your sat solver's location 
#drat_path = os.path.join(parent_dir, "drat-trim-master", "drat-trim") 

start_time = time.time()
dimacs_elapsed = 0
kissat_elapsed = 0
verify_elapsed = 0

addOrthogonalClauses = True # Creates naive orthogonality clauses, TODO: update to use other encoding (auxiliary matrix) 
addSymmetryBreakingClauses = True # Creates symmetry breaking clauses
addRelationConstraints = True # Creates relation constraints, requires symmetry breaking to be on for the full usage of relations
addXORClauses = False # Imports the clauses required to check the existence of a dependence relation in 4-net(6)'s first two rows, columns, first latin square symbols, and second latin square symbols 

relation_type = [4,4,4,4]
n = 10
seed = None
if len(sys.argv) >= 2:
	seed = int(sys.argv[1]) # Any integer?
clauses = []

def checkValid(square):
	n = len(square)
	if any(len(row) != n for row in square): # All rows are length n
		return False
	for row in square: # Each row contains all symbols 0 to n-1 exactly once
		if sorted(row) != list(range(n)):
			return False
	for col_idx in range(n): # Each column contains all symbols 0 to n-1 exactly once
		col = [square[row_idx][col_idx] for row_idx in range(n)]
		if sorted(col) != list(range(n)):
			return False
	return True

def checkOrthogonal(squares):
	square1 = squares[0:n]
	square2 = squares[n:n*2]
	exists = []
	for i in range(n):
		for j in range(n):
			pair = (square1[i][j], square2[i][j])
			if pair in exists:
				return False
			exists.append(pair)
	return True

def get1DIndex(l, r, c, s): # 4n by n^2 matrix
	index = 4 * n * n * r # Split net encoding into n blocks, go the the rth block
	index += 4 * n * c # Split each block into n subblocks, go the cth subblock
	index += n * (2 + l) # Skip position data and redundant latin square
	index += s # Pick symbol we're at    
	return index + 1 # Test this with n=3

for j in range(n): # Position data for sections a and b
	for i in range(n):
		row = 4 * n * n * j + 4 * n * i + 1
		clauses.append(str(row + j))
		clauses.append(str(row + j + (n - j) + i))
		for k in range(n):
			if k + row != row + j:
				clauses.append("-" + str(row + k)) # Make sure only 1 true value across the row variables in each row
			if row + j + (n - j) + k != row + j + (n - j) + i:
				clauses.append("-" + str(row + j + (n - j) + k)) # Make sure only 1 true value across the col variables in each row

for l in range(2): # Maintain latin square clauses
	for x in range(n):
		for y in range(n): # Create at least one value clause for row, col and symbol
			clause1 = "" # row
			clause2 = "" # col
			clause3 = "" # sym
			for z in range(n):
				clause1 = clause1 + str(get1DIndex(l, x,y,z)) + " "
				clause2 = clause2 + str(get1DIndex(l, x,z,y)) + " "
				clause3 = clause3 + str(get1DIndex(l, z,x,y)) + " "
				for w in range(z + 1, n): # At most one symbol (binary exclusions)
					clauses.append("-" + str(get1DIndex(l, x,y,z)) + " -" + str(get1DIndex(l, x,y,w)))
					clauses.append("-" + str(get1DIndex(l, x,z,y)) + " -" + str(get1DIndex(l, x,w,y)))
					clauses.append("-" + str(get1DIndex(l, z,x,y)) + " -" + str(get1DIndex(l, w,x,y)))
			clauses.append(clause1)
			clauses.append(clause2)
			clauses.append(clause3)

# XOR Clauses, over r_0, r_1, c_0, c_1, s_0, s_1, t_0, and t_1, if we get 0 then we get dependence relation (expected, UNSAT), if we get 1 then we have independence relation.
largestVariable = get1DIndex(1, n - 1, n - 1, n - 1) # Tracks the largest variable for cnf header
if addXORClauses:
	with open(clauses_path, "r") as f:
		for line in f:
			line = line.strip()
			clauses.append(line)
			clause = [int(x) for x in line.split()] # Converts line into list of variables
			for var in clause:
				largestVariable = max(largestVariable, abs(var)) # Gets the largest variable, often an auxiliary xor variable, in order to update variable count

# Delisle Relations, with only one relation
if addRelationConstraints: # Build the relation set(s) based on single relation type
	R = set()
	for j in range(len(relation_type)): # rows (parallel class 1), columns (2), symbols of latin square A (3), symbols of latin square B (4)
		for i in range(relation_type[j]):
			R.add(j*n + i)
	# For each (row, col) position, constrain which (symbol1, symbol2) pairs can appear
	for i in range(n):
		row_in_R = i in R
		for j in range(n):
			col_in_R = (n + j) in R
			for s in range(n):
				s_in_R = (2*n + s) in R
				for t in range(n):
					t_in_R = (3*n + t) in R
					# Since we encode a single relation, check parity constraint: total number of lines in relation must have consistent parity
					count = sum([row_in_R, col_in_R, s_in_R, t_in_R])
					# If odd parity, forbid combination
					if count % 2 == 1: # A[i][j] != s or B[i][j] != t
						clauses.append("-" + str(get1DIndex(0, i, j, s)) + " -" + str(get1DIndex(1, i, j, t)))

# Delisle symmetry breaking
if addSymmetryBreakingClauses: # A = 1st latin square, B = 2nd latin square
	clauses.append("c Proposition 3")
	## Proposition 3: In A, Encode [1,0] <= [0,1]. 
	for s1 in range(n): # Disallow [0,1]=s2 when [1,0]=s1 with s1 > s2 
		for s2 in range(s1): # s1 > s2
			clauses.append("-" + str(get1DIndex(0, 1, 0, s1)) + " -" + str(get1DIndex(0, 0, 1, s2)))
	for t1 in range(n): # Second square: if same s symbol, A[1,0] == A[0,1], force B[1,0] = t1 < B[0,1] = t2
		for t2 in range(t1 + 1):
			for m in range(n):
				clauses.append("-" + str(get1DIndex(0, 1, 0, m)) + " -" + str(get1DIndex(0, 0, 1, m)) + " -" + str(get1DIndex(1, 1, 0, t1)) + " -" + str(get1DIndex(1, 0, 1, t2)))    
	clauses.append("c Proposition 4")
	## Proposition 4: A < B, in practice it was sufficient to only consider weaker constraint of only checking (0,0), (0,1), (0,2)
	for s1 in range(n): # A[0,0] <= B[0,0]
		for s2 in range(s1): # s1 > s2
			clauses.append("-" + str(get1DIndex(0, 0, 0, s1)) + " -" + str(get1DIndex(1, 0, 0, s2)))
	for s in range(n):  # A[0,0] == B[0,0], then A[1,0] <= B[1,0]
		for t1 in range(n):
			for t2 in range(t1): # t1 > t2
				clauses.append("-" + str(get1DIndex(0, 0, 0, s)) + " -" + str(get1DIndex(1, 0, 0, s)) + " -" + str(get1DIndex(0, 1, 0, t1)) + " -" + str(get1DIndex(1, 1, 0, t2)))    
	for s in range(n):  # A[0,0] == B[0,0] and A[1,0] == B[1,0], then A[2,0] <= B[2,0]
		for t in range(n):
			for r1 in range(n):
				for r2 in range(r1): # r1 > r2
					clauses.append("-" + str(get1DIndex(0, 0, 0, s)) + " -" + str(get1DIndex(1, 0, 0, s)) + " -" + str(get1DIndex(0, 1, 0, t)) + " -" + str(get1DIndex(1, 1, 0, t)) + " -" + str(get1DIndex(0, 2, 0, r1)) + " -" + str(get1DIndex(1, 2, 0, r2)))    

	if addRelationConstraints: # symmetry breaking based off relations
		rows_in_R = [i for i in range(n) if i in R]
		rows_out_R= [i for i in range(n) if i not in R]
		cols_in_R  = [j for j in range(n) if (n + j) in R]
		cols_out_R = [j for j in range(n) if (n + j) not in R]
		A_in_R = [s for s in range(n) if (2*n + s) in R]
		A_out_R= [s for s in range(n) if (2*n + s) not in R]
		B_in_R  = [t for t in range(n) if (3*n + t) in R]
		B_out_R = [t for t in range(n) if (3*n + t) not in R]

		clauses.append("c Proposition 5")
		## Proposition 5: First column of A sorted within row equivalence classes
		row_classes = []
		if len(rows_in_R) > 1:
			row_classes.append(rows_in_R)
		if len(rows_out_R) > 1:
			row_classes.append(rows_out_R)
		
		# Sort within each equivalence class
		for row_class in row_classes:
			for idx in range(len(row_class) - 1):
				i = row_class[idx]
				i_next = row_class[idx + 1]
				for s in range(n): # A[i,0] <= A[i_next,0]
					for t in range(s):
						clauses.append("-" + str(get1DIndex(0, i, 0, s)) + " -" + str(get1DIndex(0, i_next, 0, t)))
	
		clauses.append("c Proposition 6")
		## Proposition 6: First row of A sorted within column equivalence classes
		col_classes = []
		if len(cols_in_R) > 1:
			col_classes.append(cols_in_R)
		if len(cols_out_R) > 1:
			col_classes.append(cols_out_R)
		
		# Sort within each equivalence class
		for col_class in col_classes:
			for idx in range(len(col_class) - 1):
				j = col_class[idx]
				j_next = col_class[idx + 1]
				for s in range(n): # A[0,j] <= A[0,j_next]
					for t in range(s):
						clauses.append("-" + str(get1DIndex(0, 0, j, s)) + " -" + str(get1DIndex(0, 0, j_next, t)))
	
		clauses.append("c Proposition 7")
		## Proposition 7: Symbols in same A-symbol equivalence class sorted in first column
		A_sym_classes = []
		if len(A_in_R) > 1:
			A_sym_classes.append(A_in_R)
		if len(A_out_R) > 1:
			A_sym_classes.append(A_out_R)

		for sym_class in A_sym_classes:
			for idx in range(len(sym_class) - 1):
				s = sym_class[idx]
				s_next = sym_class[idx + 1]
				# If A[0,i] = s, then A[0,i'] != s_next for all i' < i
				for i in range(n): # A[0,i] <= A[0,j]
					for j in range(i):
						clauses.append("-" + str(get1DIndex(0, i, 0, s)) + " -" + str(get1DIndex(0, j, 0, s_next)))
		
		clauses.append("c Proposition 8")
		## Proposition 8: Symbols in same B-symbol equivalence class sorted in first column
		B_sym_classes = []
		if len(B_in_R) > 1:
			B_sym_classes.append(B_in_R)
		if len(B_out_R) > 1:
			B_sym_classes.append(B_out_R)
			
		for sym_class in B_sym_classes: 
			for idx in range(len(sym_class) - 1):
				t = sym_class[idx]
				t_next = sym_class[idx + 1]
				# If B[0,i] = t, then B[0,i'] != t_next for all i' < i
				for i in range(n): # B[0,i] <= B[0,j]
					for j in range(i):
						clauses.append("-" + str(get1DIndex(1, i, 0, t)) + " -" + str(get1DIndex(1, j, 0, t_next)))

if addOrthogonalClauses: # n^4 * (n^2 - 1) / 2 clauses; TODO: replace with myrvold auxiliary matrix
	clauses.append("c Orthogonality")
	for r1 in range(n): # Maintain orthogonality clauses
		for c1 in range(n):
			for r2 in range(r1, n): # Starting at r1 and c2 is to prevent duplicate iterations over the same positions
				c2Start = 0
				if r1 == r2:
					c2Start = c1 + 1 
				for c2 in range(c2Start, n):
					for s1 in range(n):
						for s2 in range(n): # For each symbol pair (s1, s2), ensure it appears at most once across all (row, col) cells (e.g. position pairs)
							clauses.append("-" + str(get1DIndex(0, r1, c1, s1)) + " -" + str(get1DIndex(1, r1, c1, s2)) + " -" + str(get1DIndex(0, r2, c2, s1)) + " -" + str(get1DIndex(1, r2, c2, s2)))

variableCount = largestVariable # get1DIndex(1, n - 1, n - 1, n - 1
clauseCount = len(clauses) - 7

with open(input_path, "w") as f:
	f.write(f"p cnf {variableCount} {clauseCount}\n")
	for clause in clauses:
		f.write(f"{clause} 0\n") # Repeated write is faster than string concat, strings are immutable

dimacs_elapsed = round((time.time() - start_time) * 100)/100
print("Wrote DIMACS CNF file to:", input_path)
	
kissat_time = time.time() # wall time
with open(output_path, "w") as out_file:
	commands = [kissat_path, input_path, proof_path]
	if seed != None: 
		commands.insert(1, "--seed=" + str(seed))
	subprocess.run(commands, stdout=out_file, stderr=subprocess.STDOUT)
	#subprocess.run([drat_path, input_path, proof_path], stdout=out_file, stderr=subprocess.STDOUT)
kissat_elapsed = round((time.time() - kissat_time) * 100)/100

verify_time = time.time()
print("Wrote Kissat output to:", output_path)

with open(output_path, "r") as f:
	outputLatinSquares = [] 
	satisfiable = None
	for y in range(4 * n * n * n):
		outputLatinSquares.append(-1)
	for line in f:
		if line.startswith("s "):
			if "UNSATISFIABLE" in line:
				satisfiable = "UNSAT"
			elif "SATISFIABLE" in line:
				satisfiable = "SAT"
		elif line.startswith("v "):
			values = line[2:].strip().split()
			for val in values:
				if val == '0': # End of variables
					break
				val = int(val)
				if abs(val) <= 4 * n * n * n:
					if val > 0:
						outputLatinSquares[abs(val) - 1] = 1
					else:
						outputLatinSquares[abs(val) - 1] = 0

	print("Result:", satisfiable)
	combinedLatinSquare = []
	for y in range(n*2):
		combinedLatinSquare.append([])
		for x in range(n):
			combinedLatinSquare[y].append(-1)

	for j in range(n*n):
		counter = 0
		rowInfo = [0, 0, 0, 0]
		for i in range(4 * n * j, 4 * n * (j + 1)):
			if outputLatinSquares[i] == 1:
				rowInfo[counter] = (i - counter * n) % (4*n)
				counter += 1
		combinedLatinSquare[rowInfo[0]][rowInfo[1]] = rowInfo[2]
		combinedLatinSquare[rowInfo[0] + n][rowInfo[1]] = rowInfo[3]
		
	if satisfiable == "SAT":
		for row in range(n*2):
			if row == n:
				print("")
			print(combinedLatinSquare[row])
		if checkValid(combinedLatinSquare[0 : n]) and checkValid(combinedLatinSquare[n : n*2]) and checkOrthogonal(combinedLatinSquare):
			print("\nValid solution produced by Kissat for latin squares of order", str(n) + ".")
		else:
			print("\nInvalid solution produced by Kissat")
verify_elapsed = round((time.time() - verify_time) * 100)/100
print("Total elapsed time of script:", round((time.time() - start_time) * 100)/100, "seconds")
print("     Dimacs elapsed time:", dimacs_elapsed, "seconds")
print("     Kissat elapsed time:", kissat_elapsed, "seconds")
print("     Verification elapsed time:", verify_elapsed, "seconds")

# cd /mnt/g/Code/sat\ solver\ stuff/stinson\ xor

