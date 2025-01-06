from pysat.solvers import Solver

def rest_of(s, pos):
    return s[pos:]

def my_fun(clause_set):
    my_vec = []
    my_map = {}

    for v in clause_set:
        converted_to_int = []
        for s in v:
            if s in my_map:
                converted_to_int.append(my_map[s])
            elif s[0] == '!' and rest_of(s, 1) in my_map:
                converted_to_int.append(-1 * my_map[rest_of(s, 1)])
            elif s[0] == '!':
                my_map[rest_of(s, 1)] = len(my_map) + 1
                converted_to_int.append(-1 * my_map[rest_of(s, 1)])
            else:
                my_map[s] = len(my_map) + 1
                converted_to_int.append(my_map[s])
        my_vec.append(converted_to_int)

    return my_vec

def main():
    c1 = ["!a", "b"]
    c2 = ["d", "!c", "!b"]

    test = [c1, c2]

    result = my_fun(test)

    for v in result:
        print("Clause converted:")
        print(" ".join(map(str, v)))
    solver = Solver(name='g3')  # Use the default SAT solver (Glucose3 here)
    

    # Add clauses
    solver.add_clause(result[0])
    solver.add_clause(result[1]) 

    # Check if the formula is satisfiable
    if solver.solve():
        print("SATISFIABLE")
        print("Solution:", solver.get_model())  # Get a satisfying assignment (or not)
    else:
        print("UNSATISFIABLE")

if __name__ == "__main__":
    main()
