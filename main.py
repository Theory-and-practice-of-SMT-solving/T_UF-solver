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
    def __init__(self, graph, labels):
        self.graph = graph  # Adjacency list representation of the graph {v: [successors]}
        self.labels = labels  # Labels of the vertices {v: label} (like explained in the article)
        self.parent = {v: v for v in graph}  # Disjoint-set parent
        self.rank = {v: 0 for v in graph}  # Rank for union by rank (one of the optimizations)
        self.merge_history = []  # To track the history of merges for conflict tracing

    def find(self, element):  
        if self.parent[element] != element:
            # Path compression: recursively set the parent to the representative
            self.parent[element] = self.find(self.parent[element])
        return self.parent[element]

    def union(self, element1, element2):
        root1 = self.find(element1)
        root2 = self.find(element2)

        if root1 != root2:
            # Union by rank:
            if self.rank[root1] > self.rank[root2]:
                self.parent[root2] = root1
            elif self.rank[root1] < self.rank[root2]:
                self.parent[root1] = root2
            else:
                # If ranks are the same, arbitrarily choose one as root and increment its rank
                self.parent[root2] = root1
                self.rank[root1] += 1

            # Record the merge for backtracking
            self.merge_history.append((element1, element2))

    def add(self, element):
        if element not in self.parent:
            self.parent[element] = element
            self.rank[element] = 0

    def connected(self, element1, element2):        
        # Check if two elements are in the same equivalence class
        return self.find(element1) == self.find(element2)

    def congruent(self, u, v):
        # Check if two vertices are congruent under the current relation:
        if self.labels[u] != self.labels[v] or len(self.graph[u]) != len(self.graph[v]):
            # The outdegree must match
            return False
        for i in range(len(self.graph[u])):
            if self.find(self.graph[u][i]) != self.find(self.graph[v][i]):
                return False
        return True

    def merge(self, u, v):
        # Merge the equivalence classes of u and v, updating the congruence closure:
        if self.find(u) == self.find(v):
            return

        predecessors_u = {x for x in self.graph if u in self.graph[x]}
        predecessors_v = {x for x in self.graph if v in self.graph[x]}

        self.union(u, v)

        for x in predecessors_u:
            for y in predecessors_v:
                if self.find(x) != self.find(y) and self.congruent(x, y):
                    self.merge(x, y)

    def is_sat(self, constraints):
        # Check if the result is SAT under the set of constraints and return an unsat core if not
        unsat_core = []

        for u, v in constraints:
            if not self.congruent(u, v):  # If u and v are not congruent, skip
                continue
            # Conflict detected: add the disequality to the unsat core
            unsat_core.append((u, v))
            return False, self.trace_unsat_core(unsat_core)
        return True, None

    def trace_unsat_core(self, conflicts):
        # Trace the unsat core using the merge history and the initial conflicts
        unsat_core = set(conflicts)
        # Backtrack through the merge history to identify contributing equations
        for u, v in reversed(self.merge_history):
            if not self.reproduces_conflict(unsat_core):
            # (u, v) é essencial para o conflito; adiciona de volta
                unsat_core.add((u, v))

        return list(unsat_core)

        return list(unsat_core)

    def reproduces_conflict(self, core):
        # Check if a given core reproduces the conflict
        temp_cc = CongruenceClosure(self.graph, self.labels)
        for u, v in core:
            temp_cc.merge(u, v)
        for u, v in core:
            if temp_cc.congruent(u, v):
                return True
        return False

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
  abstract_clause = []
  my_map = {}
  another_map = {}

  for clause in clause_set:
    converted_to_int = []
    for s in clause:
      if s in my_map:
        converted_to_int.append(my_map[s])
      elif s.op.name == "not" and s.args[0] in my_map:
        converted_to_int.append(-1 * my_map[s.args[0]])
      elif s.op.name == "not":
        my_map[s.args[0]] = len(my_map) + 1
        another_map[len(my_map)] = s.args[0]
        converted_to_int.append(-1 * my_map[s.args[0]])
      else:
        my_map[s] = len(my_map) + 1
        another_map[len(my_map)] = s
        converted_to_int.append(my_map[s])
    abstract_clause.append(converted_to_int)

  return abstract_clause, another_map

def create_graphs(clause):
  relation_graph = defaultdict(list) # we are gonna need this a the graph for congruence closure
  constraints = []
  relation = []
  labels = {} # I forgot to add that before, but it is requested in the article
  for term in clause: 
    if term.op.name == 'not': # verifica se o termo vai estar ou não no grafo de restrições
      neg_arg = term.args[0] # not possui apenas 1 argumento
        
      if neg_arg.op.name == 'equal':
        restriction = [x for x in neg_arg.args] # cria uma lista com os argumentos
        key = (restriction[0]) # adiciona a chave como sendo parte da igualdade em si com o index da clause q está
        constraints.append((key, restriction[1]))
        labels[key] = key
        labels[restriction[1]] = restriction[1] # atualiza a label
      else: 
        key = (term)
        labels[key] = key
        constraints.append((key,key))
    else:
      if term.op.name == "equal":
        equiv = [x for x in term.args] # cria uma lista com os argumentos
        key = (equiv[0]) # adiciona a chave como sendo parte da igualdade em si com o index da clause q está
        relation_graph[key].append(equiv[1])
        relation.append((key,equiv[1]))
        labels[key] = key
        labels[equiv[1]] = equiv[1]
      else: 
        key = (term)
        labels[key] = key
        relation.append((key,key))
        relation_graph[key].append("")
  
  return relation_graph, constraints, relation, labels

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
  abstract_clause, another_map = create_abstraction(clause_set)

  print('\n')
  print("CLAUSE SET")
  print(clause_set)
  print('\n')
  print("ABSTRACT CLAUSE")
  print(abstract_clause)
  print("\n")

  # print(f'Abstraction: {abstraction}')
  # print('\n')
  # print(f'Mapping: {my_map}')
  # print('\n')

  solver = Solver(name='g3')  # Use the default SAT solver (Glucose3 here)
  for i in abstract_clause:
    solver.add_clause(i)


  if solver.solve():
    aux = []
    model = solver.get_model()
    print("Solution:", model)  # Get a satisfying assignment (or not)
    # Agora, vamos criar o grafo de conjunções que precisamos:
    for m in model:
      if m >= 0 :
        aux.append(another_map[m])
      else :
        aux.append(Expr(Symbol('not', True), another_map[(-1*m)])) # acredito que vai ser importante no fim das contas
    print(aux)
  else:
    print("UNSATISFIABLE")

  relation_graph, restriction, relation, labels = create_graphs(aux)

  print(f"RELATION")
  print(relation_graph)
  print("\n")
  print(f"RESTRICTION")
  print(restriction)
  print('\n')
  print("LABELS")
  print(labels)
  print('\n')
  print("RELATION")
  print(relation)
  print('\n')

  cc = CongruenceClosure(relation_graph, labels)
  for key in labels:
    cc.add(key)
  for u, v in relation:
    cc.union(u, v)
  for u, v in relation:
    cc.merge(u, v)

  sat_res = cc.is_sat(restriction)
  print(f"The result is: {sat_res}")
    
  classes = defaultdict(list)
  for vertex in relation_graph:
    classes[cc.find(vertex)].append(vertex)

  print("Equivalence classes:")
  for eq_class in classes.values():
    print(eq_class)

if __name__ == "__main__":
  main()
