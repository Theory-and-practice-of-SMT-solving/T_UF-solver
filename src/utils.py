from theorysolver import *
from pysmt.smtlib.parser import SmtLibParser
from pysat.solvers import Solver

def run_sat_solver(abstract_clause_set, int_to_term_map):
  solver = Solver(name='g3')  # use the default SAT solver (glucose3 here)
  for abstract_clause in abstract_clause_set:
    solver.add_clause(abstract_clause)

  if solver.solve():
    sat_assignment = list()
    model = solver.get_model() # get a satisfying assignment (abstract)

    #######################################################
    print("SAT ABSTRACTION")
    print(model) 
    print('\n')
    #######################################################

    for m in model: # get a satisfying assignment (terms)
      if m >= 0 :
        sat_assignment.append(int_to_term_map[m])
      else:
        sat_assignment.append(Expr(Symbol('not', True), int_to_term_map[(-1*m)]))

    #######################################################
    print("SAT ASSIGNMENT")
    print(sat_assignment)
    print('\n')
    #######################################################

    solver.delete() # free resources
    return True, sat_assignment

  else: # OLHAR

    #######################################################
    print("UNSATISFIABLE - SAT")
    print('\n')
    #######################################################

    solver.delete() # free resources
    return False, None
  
def framework_CDCL(abstract_clause_set, term_to_int_map, int_to_term_map):

  while True:
    is_sat_solver, sat_assignment = run_sat_solver(abstract_clause_set, int_to_term_map)

    if not is_sat_solver:
      return

    graph, constraints, equal_pairs, congruence_closure = create_graphs(sat_assignment)

    #######################################################
    print("EQUAL PAIRS")
    print(equal_pairs)
    print('\n')
    print("DIFFERENT PAIRS")
    print(constraints)
    print('\n')
    print("GRAPH")
    for i in graph:
      print(f'{i} ----------> SUCESSORS: {graph[i][1]} ----------> PREDECESSORS: {congruence_closure[i][2]}')
    print('\n')
    #######################################################

    ts = TheorySolver(graph, equal_pairs, constraints, congruence_closure)
    is_sat_theory_solver, unsat_core = ts.run_theory_solver()

    if is_sat_theory_solver:
      
      #######################################################
      print("SATISFIABLE - THEORY")
      print('\n')
      #######################################################
      
      return

    #######################################################
    print("UNSATISFIABLE - THEORY")
    print('\n')
    print('UNSAT CORE')
    print(unsat_core)
    #######################################################

    new_abstract_clause = list()
    for i in unsat_core:
      if i.op.name == 'not':
        new_abstract_clause.append(term_to_int_map[i.args[0]])
      else:
        new_abstract_clause.append((-1)*term_to_int_map[i])

    abstract_clause_set.append(new_abstract_clause)

    #######################################################
    print([(-1)*x for x in new_abstract_clause])
    print('\n')
    print("NEW ABSTRACT CLAUSE SET")
    print(abstract_clause_set)
    print('\n')
    #######################################################

def run_parser(filename):
  parser = SmtLibParser() 
  script = parser.get_script_fname(filename)

  formula = script.get_last_formula()
  formula_cnf = formula_preprocessing(formula)

  return formula_cnf