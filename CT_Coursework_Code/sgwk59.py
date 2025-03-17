import itertools
import os
os.chdir(os.path.dirname(os.path.abspath(__file__)))

#Question 6: Parses a DIMACS-formatted CNF file, returning the clause_set.
def load_dimacs(filename):
    clause_set = []
    with open(filename, 'r') as file:
        for line in file:
            line = line.strip()
            if not line or line.startswith('c') or line.startswith('p'):
                continue 

            # Parses the clause and removes the 0 at the end.
            clause = list(map(int, line.split()))
            if clause[-1] == 0:
                clause.pop()
            clause_set.append(clause)
    return clause_set


#Question 7:Enumerate all variable assignments and check for SAT satisfiability.
def simple_sat_solve(clause_set):
    
    # Extract all variable numbers
    used_variables = {abs(lit) for clause in clause_set for lit in clause}
    sorted_variables = sorted(used_variables)
    
    # Exhaust all possible variable assignments
    for values in itertools.product([True, False], repeat=len(sorted_variables)):
        assignment = {var: val for var, val in zip(sorted_variables, values)}

        # Check that the current assignment satisfies all clauses
        if all(any(assignment[abs(lit)] == (lit > 0) for lit in clause) for clause in clause_set):
            return sorted([var if assignment[var] else -var for var in sorted_variables], key=lambda x: abs(x))
            
    return False


#Question 8:Make SAT assignments recursively, trying two Boolean assignments (True and False)
def branching_sat_solve(clause_set,partial_assignment):
    #Condition 1: All clauses are satisfied
    if not clause_set:
        return partial_assignment
    
    # Condition 2: Empty clause found, indicating unsatisfiable
    if any(len(clause) == 0 for clause in clause_set):
        return False
    
    # Pick the first unassigned variable
    first_unassigned = clause_set[0][0]
    
    clause_set_1 = []
    for clause in clause_set:
        if first_unassigned in clause:
            continue
        clause_set_1.append([x for x in clause if x != -first_unassigned])
    result = branching_sat_solve(clause_set_1, partial_assignment + [first_unassigned])
    
    if result:
        return result

    clause_set_2 = []
    for clause in clause_set:
        if -first_unassigned in clause:
            continue
        clause_set_2.append([x for x in clause if x != first_unassigned])
    return branching_sat_solve(clause_set_2, partial_assignment + [-first_unassigned])


#Question 9
def unit_propagate(clause_set):

    new_clause_set = list(clause_set)

    while True:
        unit_clause = None
        # Find the first singleton clause
        for clause in new_clause_set:
            if len(clause) == 1:
                unit_clause = clause
                break
        
        # If there is no singleton clause, propagation ends
        if not unit_clause:
            return new_clause_set

        first_unassigned = unit_clause[0]

        # Remove all clauses containing lit 
        new_clause_set = [clause for clause in new_clause_set if first_unassigned not in clause]

        updated_clause_set = []
        for clause in new_clause_set:
            updated_clause_set.append([x for x in clause if x != -first_unassigned])
        new_clause_set = updated_clause_set


#Question 10:Recursively solving SAT problems
def dpll_sat_solve(clause_set, partial_assignment):
    def apply_assignment(clauses, assignment):
        new_clauses = list(clauses)
        for lit in assignment:
            new_clauses = [clause for clause in new_clauses if lit not in clause]
            temp = []
            for clause in new_clauses:
                temp.append([x for x in clause if x != -lit])
            new_clauses = temp
        return new_clauses

    # Simplify with existing partial_assignment
    clause_set = apply_assignment(clause_set, partial_assignment)

    while True:
        forced_assignments = []
        changed = True
        while changed:
            changed = False
            # Find the first singleton clause
            single_clause = None
            for clause in clause_set:
                if len(clause) == 1:
                    single_clause = clause
                    break
            if single_clause:
                changed = True
                first_unassigned = single_clause[0]
                forced_assignments.append(first_unassigned)
                clause_set = [clause for clause in clause_set if first_unassigned not in clause]
                temp = []
                for clause in clause_set:
                    temp.append([x for x in clause if x != -first_unassigned])
                clause_set = temp
        if not forced_assignments:
            break
        partial_assignment += forced_assignments

    if any(len(clause) == 0 for clause in clause_set):
        return False

    if not clause_set:
        return partial_assignment
    
    first_unassigned = clause_set[0][0]
    r = dpll_sat_solve(clause_set, partial_assignment + [first_unassigned])
    if r:
        return r
    return dpll_sat_solve(clause_set, partial_assignment + [-first_unassigned])


def test():
    print("Testing load_dimacs")
    try:
        dimacs = load_dimacs("sat.txt")
        assert dimacs == [[1],[1,-1],[-1,-2]]
        print("Test passed")
    except:
        print("Failed to correctly load DIMACS file")

    print("Testing simple_sat_solve")
    try:
        sat1 = [[1],[1,-1],[-1,-2]]
        check = simple_sat_solve(sat1)
        assert check == [1,-2] or check == [-2,1]
        print("Test (SAT) passed")
    except:
        print("simple_sat_solve did not work correctly a sat instance")

    try:
        unsat1 = [[1, -2], [-1, 2], [-1, -2], [1, 2]]
        check = simple_sat_solve(unsat1)
        assert (not check)
        print("Test (UNSAT) passed")
    except:
        print("simple_sat_solve did not work correctly an unsat instance")

    print("Testing branching_sat_solve")
    try:
        sat1 = [[1],[1,-1],[-1,-2]]
        check = branching_sat_solve(sat1,[])
        assert check == [1,-2] or check == [-2,1]
        print("Test (SAT) passed")
    except:
        print("branching_sat_solve did not work correctly a sat instance")

    try:
        unsat1 = [[1, -2], [-1, 2], [-1, -2], [1, 2]]
        check = branching_sat_solve(unsat1,[])
        assert (not check)
        print("Test (UNSAT) passed")
    except:
        print("branching_sat_solve did not work correctly an unsat instance")


    print("Testing unit_propagate")
    try:
        clause_set = [[1],[-1,2]]
        check = unit_propagate(clause_set)
        assert check == []
        print("Test passed")
    except:
        print("unit_propagate did not work correctly")


    print("Testing DPLL") #Note, this requires load_dimacs to work correctly
    problem_names = ["sat.txt","unsat.txt"]
    for problem in problem_names:
        try:
            clause_set = load_dimacs(problem)
            check = dpll_sat_solve(clause_set,[])
            if problem == problem_names[1]:
                assert (not check)
                print("Test (UNSAT) passed")
            else:
                assert check == [1,-2] or check == [-2,1]
                print("Test (SAT) passed")
        except:
            print("Failed problem " + str(problem))
    print("Finished tests")

if __name__ == "__main__":
    test() 
