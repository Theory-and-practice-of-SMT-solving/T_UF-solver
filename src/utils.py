from theorysolver import *
from pysmt.smtlib.parser import SmtLibParser
from pysat.solvers import Solver
import sys

def run_sat_solver(abstract_clause_set, int_to_term_map):
  solver = Solver(name='g3') # use the default SAT solver (glucose3 here)

  # add the abstract clauses to the sat solver
  for abstract_clause in abstract_clause_set:
    solver.add_clause(abstract_clause)

  if solver.solve():
    sat_assignment = list()
    model = solver.get_model() # get a satisfying assignment (abstract)

    for m in model: # get a satisfying assignment (terms)
      if m >= 0 :
        sat_assignment.append(int_to_term_map[m])
      else:
        sat_assignment.append(Expr(Symbol('not', True), int_to_term_map[(-1*m)]))

    solver.delete() # free resources
    return True, sat_assignment

  else:

    print("Unsat")

    solver.delete() # free resources
    return False, None
  
def framework(abstract_clause_set, term_to_int_map, int_to_term_map):

  while True:
    # get a sat assignment from the sat solver
    is_sat_solver, sat_assignment = run_sat_solver(abstract_clause_set, int_to_term_map)

    if not is_sat_solver:
      return

    # compute the congruence closure and return sat or unsat at the theory level
    graph, constraints, equal_pairs, congruence_closure = create_graphs(sat_assignment)
    ts = TheorySolver(graph, equal_pairs, constraints, congruence_closure)
    is_sat_theory_solver, unsat_core = ts.run_theory_solver()

    if is_sat_theory_solver:
  
      print("Sat")

      return

    # create the new abstract clause using the unsat core
    new_abstract_clause = list()
    for i in unsat_core:
      if i.op.name == 'not':
        new_abstract_clause.append(term_to_int_map[i.args[0]])
      else:
        new_abstract_clause.append((-1)*term_to_int_map[i])

    abstract_clause_set.append(new_abstract_clause)

# parses the file and retrieves the full formula
def run_parser(filename):
  parser = SmtLibParser() 

  try:
    script = parser.get_script_fname(filename)
  except FileNotFoundError:
    print(f"Error: The file '{filename}' was not found.")
    sys.exit(1)
  except Exception as e:
    print(f"Error: Unable to parse the file.")
    print(f"Description: {e}.")
    sys.exit(1)

  formula = script.get_last_formula()
  formula_cnf = formula_preprocessing(formula)

  return formula_cnf