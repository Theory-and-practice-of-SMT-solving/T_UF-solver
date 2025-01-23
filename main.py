from pysmt.shortcuts import Symbol
from pysmt.smtlib.parser import SmtLibParser
from graphviz import Digraph
from pysat.solvers import Solver
from collections import defaultdict
import os

# defines a symbol, that can be a constant (is_function = False) or a function (is_function = True) 
# example of Symbol -----> name = or, is_function = yes
class Symbol:
  def __init__(self, name, is_function):
    self.name = name
    self.is_function = is_function
  
  def __eq__(self, other):
    if not isinstance(other, Symbol):
      return False
    return self.name == other.name and self.is_function == other.is_function
  
  def __hash__(self):
    return hash((self.name, self.is_function))

# defines an arbitrary expression, following the syntax specified in the documentation
# op is a symbol, that can contain args (if it is a function)
# example of Expr -----> op = or, args = (b and c), (e) -> (b and c) or e 
# in the example above, all the args are also Expr
class Expr:
  def __init__(self, op, *args):
    self.op = op
    self.args = args

  def __eq__(self, other):
    if not isinstance(other, Expr):
      return False
    return self.op == other.op and self.args == other.args
  
  def __hash__(self):
    return hash((self.op, self.args))

  # converting from arbitrary expression to negation normal form (NNF)
  def to_nnf(self):
    # it contains only one argument
    if self.op.name == 'not':
      neg_expr = self.args[0] # getting the argument

      if neg_expr.op.name == 'not':
        # not (not x) = x
        return neg_expr.args[0].to_nnf()
      
      # elif neg_expr.op.name == 'equal':
      #   # not (a equal b) = a not equal b
      #   return Expr(Symbol('not equal', True), *(arg.to_nnf() for arg in neg_expr.args))
      
      elif neg_expr.op.name == 'and':
        # not (a and b) = not a or not b
        return Expr(Symbol('or', True), *(Expr(Symbol('not', True), arg).to_nnf() for arg in neg_expr.args))
      
      elif neg_expr.op.name == 'or':
        # not (a or b) = not a and not b
        return Expr(Symbol('and', True), *(Expr(Symbol('not', True), arg).to_nnf() for arg in neg_expr.args))
      
      elif neg_expr.op.name == 'implies':
        # not (a => b) = not (not a or b) = a and not b
        return Expr(Symbol('and', True), neg_expr.args[0].to_nnf(), Expr(Symbol('not', True), neg_expr.args[1]).to_nnf())
      
      else:
        return self
    
    # it contains two arguments
    elif self.op.name == 'implies':
      # (a => b) = not a or b
      return Expr(Symbol('or', True), Expr(Symbol('not', True), self.args[0]).to_nnf(), self.args[1].to_nnf())
    
    elif self.op.name == 'and':
      # a and b
      return Expr(Symbol('and', True), *(arg.to_nnf() for arg in self.args))
    
    elif self.op.name == 'or':
      # a or b
      return Expr(Symbol('or', True), *(arg.to_nnf() for arg in self.args))
    
    else:
      return self
  
  # converting from negation normal form (NNF) to conjunctive normal form (CNF)
  def to_cnf(self):
    if self.op.name == 'or':
      left = self.args[0].to_cnf()
      right = self.args[1].to_cnf()

      # (a and b) or (c and d) = (a or (c and d)) and (b or (c and d))
      # (a and b) or (c or d) = (a or (c or d)) and (b or (c or d))
      # (a and b) or c = (a or c) and (b or c)
      if left.op.name == 'and':
        return Expr(Symbol('and', True), *(Expr(Symbol('or', True), arg, right).to_cnf() for arg in left.args))

      # (a or b) or (c and d) = ((a or b) or c) and ((a or b) or d)
      # a or (b and c) = (a or b) and (a or c)
      elif right.op.name == 'and':
        return Expr(Symbol('and', True), *(Expr(Symbol('or', True), left, arg).to_cnf() for arg in right.args))
      
      else:
        return self
      
    elif self.op.name == 'equal':
      left = self.args[0].to_cnf()
      right = self.args[1].to_cnf()
      return Expr(Symbol('equal', True), left, right)

    # elif self.op.name == 'not equal':
    #   left = self.args[0].to_cnf()
    #   right = self.args[1].to_cnf()
    #   return Expr(Symbol('not equal', True), left, right)

    elif self.op.name == 'and':
      left = self.args[0].to_cnf()
      right = self.args[1].to_cnf()
      return Expr(Symbol('and', True), left, right)

    elif self.op.name == 'not':
      arg = self.args[0].to_cnf()
      return Expr(Symbol('not', True), arg)
    
    else: 
      return self
    
  # printing using prefix notation
  def __str__(self): 
    if self.op.is_function:
      return f"{self.op.name} ({', '.join(map(str, self.args))})"
    else:
      return self.op.name
    
  def __repr__(self):
    return self.__str__() 
  
  # creating a graphical tree
  def to_tree(self, filename):
    tree = Digraph()
    self.add_to_tree(tree, self)

    current_dir = os.path.dirname(os.path.abspath(__file__))
    filepath = os.path.join(current_dir, f'images/{filename}')
    tree.render(filepath, format="png", cleanup=True)

  def add_to_tree(self, tree, node, parent_id=None):
    node_id = str(id(node))
    tree.node(node_id, label=node.op.name)
    if parent_id:
      tree.edge(parent_id, node_id)

    for arg in node.args:
      if isinstance(arg, Expr):
        self.add_to_tree(tree, arg, node_id)
      else:
        leaf_id = str(id(arg))
        tree.node(leaf_id, label=str(arg))
        tree.edge(node_id, leaf_id)

class CongruenceClosure:
  def __init__(self, graph, equal_pairs, constraints, congruence_closure):
    self.graph = graph  # {v = (label, [sucessors])}
    self.representatives = {v: v for v in graph}
    self.equal_pairs = equal_pairs # pares que sao equivalentes
    self.constraints = constraints # pares que nao podem ser equivalentes
    self.congruence_closure = congruence_closure # {v = [rank, [equivalence_class], [predecessors]]}
  
  # returns the unique name of the equivalence class of element
  def find(self, element):  
    if self.representatives[element] != element:
      # path compression: recursively set the representatives to the representatives
      self.representatives[element] = self.find(self.representatives[element])
    return self.representatives[element]

  # combines the equivalence classes of the elements
  # merges their predecessor lists into one
  def union(self, element1, element2):
    root1 = self.find(element1)
    root2 = self.find(element2)

    if root1 == root2:
      return
    
    rank1 = self.congruence_closure[root1][0]
    rank2 = self.congruence_closure[root2][0]
    # union by rank
    if rank1 > rank2:
      greater_representative = root1
      smaller_representative = root2

      self.representatives[root2] = root1
    elif rank1 < rank2:
      greater_representative = root2
      smaller_representative = root1

      self.representatives[root1] = root2
    else:
      # if ranks are the same, arbitrarily choose one as root and increment its rank
      greater_representative = root1
      smaller_representative = root2

      self.representatives[root2] = root1
      self.congruence_closure[root1][0] += 1

    # funde as classes de equivalencias
    greater_equivalence_class = self.congruence_closure[greater_representative][1]
    smaller_equivalence_class = self.congruence_closure[smaller_representative][1]
    greater_equivalence_class.extend(smaller_equivalence_class)

    # funde os predecessores
    greater_predecessor = self.congruence_closure[greater_representative][2]
    smaller_predecessor = self.congruence_closure[smaller_representative][2]
    greater_predecessor.update(smaller_predecessor)

  def congruent(self, u, v):
    # check if two vertices are congruent under the current relation:
    if self.graph[u][0] != self.graph[v][0] or len(self.graph[u][1]) != len(self.graph[v][1]):
      # (the outdegree is gonna be exactly the length of the list of "sons")
      return False
    for i in range(len(self.graph[u][1])):
      if self.find(self.graph[u][1][i]) != self.find(self.graph[v][1][i]):
        return False
    return True
    
  def merge(self, u, v):
    print(f'{u} AND {v} ARE EQUAL') # DEBUGGER
    print('\n')
    # merge the equivalence classes of u and v, updating the congruence closure 
    if self.find(u) == self.find(v): # pegar o representante da classe e fundir os representantes
      return

    predecessors_u = self.congruence_closure[u][2].copy()
    predecessors_v = self.congruence_closure[v][2].copy()

    self.union(u, v)

    self.show() # DEBUGGER
    print('\n') 

    for x in predecessors_u:
      for y in predecessors_v:
        if self.find(x) != self.find(y) and self.congruent(x, y):
          self.merge(x, y)

  def algorithm(self):
    # faz o merge das classes de equivalencias dos pares que sao iguais
    print('START - ALGORITHM') # DEBUGGER
    print('\n')
    self.show() # DEBUGGER
    print('\n')
    for x, y in self.equal_pairs:
      self.merge(x, y)

    print('END - ALGORITHM') # DEBUGGER
    print('\n')

  def show(self): # DEBUGGER
    for i, _ in self.congruence_closure.items():
        print(f'VERTEX: {i} ----------> REPRESENTATIVE: {self.find(i)}')

  # def add(self, element):
  #   if element not in self.representatives:
  #     self.representatives[element] = element
  #     self.rank[element] = 0

  # def connected(self, element1, element2):        
  #   # vê se estão no mesmo set
  #   return self.find(element1) == self.find(element2)

  def is_sat(self):
    # cria classes de equivalencias
    self.algorithm()
    # check if the final result is SAT under the set of constraints.
    for u, v in self.constraints:
      if self.find(u) == self.find(v):
        print(f'{u} AND {v} ARE EQUAL, BUT THEY SHOULD BE DIFFERENT')
        print('\n')
        return False
    return True

####################################################################################

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

  return abstract_clause_set, int_to_term_map

# def create_equivalence_class(terms, predecessors):
#   all_predecessors = set()
#   for term in terms:
#     all_predecessors = all_predecessors | predecessors[term]
  
#   equivalence_class = (terms, all_predecessors)
#   return equivalence_class

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

######################################## MAIN ########################################

def main():
  # main
  parser = SmtLibParser() 
  script = parser.get_script_fname("testCase01.smt2")

  formula = script.get_last_formula() 
  expr = convert_to_expr(formula) 

  nnf_expr = expr.to_nnf() 
  nnf_expr.to_tree('nnf_tree')

  cnf_expr = nnf_expr.to_cnf() 
  cnf_expr.to_tree('cnf_tree')

  clause_set = get_clause_set(cnf_expr)

  # print('\n')
  # print(f"original formula: {formula}")
  # print(f"intermediate formula: {expr}")
  # print('\n')
  # print(f"NNF formula: {nnf_expr}")
  # print(f"CNF formula: {cnf_expr}")
  # print('\n')
  # print(f'Clause Set: {clause_set}')
  # print('\n')

  # relation_graph, restriction_graph = create_graphs(clause_set)
  abstract_clause_set, int_to_term_map = create_abstraction(clause_set)

  print('\n')
  print("CLAUSE SET")
  print(clause_set)
  print('\n')
  print("ABSTRACT CLAUSE SET")
  print(abstract_clause_set)
  print("\n")

  # print(f'Abstraction: {abstraction}')
  # print('\n')
  # print(f'Mapping: {my_map}')
  # print('\n')

  solver = Solver(name='g3')  # Use the default SAT solver (Glucose3 here)
  for abstract_clause in abstract_clause_set:
    solver.add_clause(abstract_clause)

  if solver.solve():
    sat_assignment = []
    model = solver.get_model()
    print("SAT ABSTRACTION")
    print(model) # Get a satisfying assignment (or not)
    print('\n')

    # Agora, vamos criar o grafo de conjunções que precisamos:
    for m in model:
      if m >= 0 :
        sat_assignment.append(int_to_term_map[m])
      else:
        sat_assignment.append(Expr(Symbol('not', True), int_to_term_map[(-1*m)])) # acredito que vai ser importante no fim das contas

    print("SAT ASSIGNMENT")
    print(sat_assignment)
    print('\n')
  else:
    print("UNSATISFIABLE")
    print('\n')

  graph, constraints, equal_pairs, congruence_closure = create_graphs(sat_assignment)


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

  # x = sat_assignment[0].args[0]
  # j = sat_assignment[1].args[0]

  # print(predecessors[x], predecessors[j], predecessors[x] == predecessors[j])
  # create_equivalence_class()
  # print(relation)
  # print(create_equivalence_class(relation[1], predecessors))

  # print(f"RELATION")
  # print(relation_graph)
  # print("\n")
  # print(f"RESTRICTION")
  # print(restriction)
  # print('\n')
  # print("LABELS")
  # print(labels)
  # print('\n')
  # print("RELATION")
  # print(relation)
  # print('\n')

  cc = CongruenceClosure(graph, equal_pairs, constraints, congruence_closure)
  is_sat = cc.is_sat()
  print(is_sat)

  # for key in labels:
  #   cc.add(key)
  # for u, v in relation:
  #   cc.union(u, v)
  # for u, v in relation:
  #   cc.merge(u, v)

  # sat_res = cc.is_sat(restriction)
  # print(f"The result is: {sat_res}")
    
  # classes = defaultdict(list)
  # for vertex in relation_graph:
  #   classes[cc.find(vertex)].append(vertex)

  # print("Equivalence classes:")
  # for eq_class in classes.values():
  #   print(eq_class)

  # aux = defaultdict(lambda: (0, [], set()))
  # aux[1][1].extend([1, 2])
  # print(aux)

if __name__ == "__main__":
  main()
