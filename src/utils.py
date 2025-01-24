from expression import *
from theorysolver import *
from pysmt.smtlib.parser import SmtLibParser
from pysat.solvers import Solver

# converting the formula given by pySMT parser to Expr
def convert_to_expr(formula): 
  if formula.is_symbol(): 
    return Expr(Symbol(formula.symbol_name(), False))
  
  elif formula.is_function_application():
    return Expr(Symbol(str(formula.function_name()), True), *[convert_to_expr(arg) for arg in formula.args()])
  
  elif formula.is_equals():
    return Expr(Symbol('equal', True), convert_to_expr(formula.arg(0)), convert_to_expr(formula.arg(1)))
  
  elif formula.is_not(): 
    return Expr(Symbol('not', True), convert_to_expr(formula.arg(0)))
  
  elif formula.is_and(): 
    # making 'and' have only two arguments
    args = [convert_to_expr(arg) for arg in formula.args()]
    while len(args) > 2:
      a = args.pop(0)
      b = args.pop(0)
      args.insert(0, Expr(Symbol('and', True), a, b))
    return Expr(Symbol('and', True), *args)
  
  elif formula.is_or():
    # making 'or' have only two arguments
    args = [convert_to_expr(arg) for arg in formula.args()]
    while len(args) > 2:
        a = args.pop(0)
        b = args.pop(0)
        args.insert(0, Expr(Symbol('or', True), a, b))
    return Expr(Symbol('or', True), *args)
  
  elif formula.is_implies(): 
    return Expr(Symbol('implies', True), convert_to_expr(formula.arg(0)), convert_to_expr(formula.arg(1)))
  
  else:
    raise ValueError(f"Error: {formula}")
  
def formula_preprocessing(formula):
  formula_expr = convert_to_expr(formula)
  formula_nnf = formula_expr.to_nnf()
  formula_cnf = formula_nnf.to_cnf()

  return formula_cnf

def get_clause_set(expr):
  clause_set = []

  def get_clause(node):
    if node.op.name == "or":
      clause = []
      for arg in node.args:
        if arg.op.name == "or":
          clause.extend(get_clause(arg))
        else:
          clause.append(arg)
      return clause
    else:
      return [node]

  def extract_clauses(node):
    if node.op.name == "and":
      for arg in node.args:
        extract_clauses(arg)
    else:
      clause_set.append(get_clause(node))  

  extract_clauses(expr)
  return clause_set

def create_abstraction(clause_set):
  abstract_clause_set = []
  term_to_int_map = {}
  int_to_term_map = {}

  for clause in clause_set:
    converted_to_int = []
    for term in clause:
      if term in term_to_int_map:
        converted_to_int.append(term_to_int_map[term])
      elif term.op.name == "not" and term.args[0] in term_to_int_map:
        converted_to_int.append(-1 * term_to_int_map[term.args[0]])
      elif term.op.name == "not":
        term_to_int_map[term.args[0]] = len(term_to_int_map) + 1
        int_to_term_map[len(term_to_int_map)] = term.args[0]
        converted_to_int.append(-1 * term_to_int_map[term.args[0]])
      else:
        term_to_int_map[term] = len(term_to_int_map) + 1
        int_to_term_map[len(term_to_int_map)] = term
        converted_to_int.append(term_to_int_map[term])
    abstract_clause_set.append(converted_to_int)

  return abstract_clause_set, term_to_int_map, int_to_term_map

def create_vertices(term, graph, congruence_closure, superterm):
  label = term.op.name
  graph[term] = (label, [args for args in term.args])

  equivalence_class = congruence_closure[term][1]
  if term not in equivalence_class:
    equivalence_class.append(term)

  predecessors = congruence_closure[term][2] 
  if superterm is not None and superterm not in predecessors:
    predecessors.add(superterm)

  for arg in term.args:
    create_vertices(arg, graph, congruence_closure, term)
    
def create_graphs(clause):
  graph = defaultdict(tuple) # {v = (label, [sucessors])}
  equal_pairs = list() # pares que sao equivalentes
  constraints = list() # pares que nao podem ser equivalentes
  congruence_closure = defaultdict(lambda: [0, [], set()]) # {v = (rank, [equivalence_class], [predecessors])}

  for term in clause: 
    if term.op.name == 'not': # verifica se o termo vai estar ou não no grafo de restrições
      neg_arg = term.args[0] # not possui apenas 1 argumento
        
      if neg_arg.op.name == 'equal':
        for arg in neg_arg.args:
          create_vertices(arg, graph, congruence_closure, None)
        
        constraints.append([x for x in neg_arg.args])
      else: 
        create_vertices(term.args[0], graph, congruence_closure, None)
        constraints.append([term.args[0], term.args[0]])
    else:
      if term.op.name == "equal":
        for arg in term.args:
          create_vertices(arg, graph, congruence_closure, None)

        # equivalence_class = create_equivalence_class(args, predecessors)
        equal_pairs.append([x for x in term.args])
      else: 
        create_vertices(term, graph, congruence_closure, None)
        # equivalence_class = create_equivalence_class([term, term], predecessors)
        equal_pairs.append([x for x in term.args])
  
  return graph, constraints, equal_pairs, congruence_closure

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

  else:

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
    print(term_to_int_map)
    print("UNSATISFIABLE - THEORY")
    print('\n')
    print('UNSAT CORE')
    # print(unsat_core)
    #######################################################

    new_abstract_clause = list()
    for i in unsat_core:
      if i.op.name == 'not':
        new_abstract_clause.append(term_to_int_map[i.args[0]])
      else:
        new_abstract_clause.append((-1)*term_to_int_map[i])

    abstract_clause_set.append(new_abstract_clause)

    print([(-1)*x for x in new_abstract_clause])
    print('\n')
    print("NEW ABSTRACT CLAUSE SET")
    print(abstract_clause_set)
    print('\n')

def run_parser(filename):
  parser = SmtLibParser() 
  script = parser.get_script_fname(filename)

  formula = script.get_last_formula()
  formula_cnf = formula_preprocessing(formula)

  return formula_cnf