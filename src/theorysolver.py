from expression import *
from collections import defaultdict

class TheorySolver:
  def __init__(self, graph, equal_pairs, constraints, congruence_closure):
    self.graph = graph  # {v = (label, [sucessors])}
    self.representatives = {v: v for v in graph}
    self.equal_pairs = equal_pairs # pares que sao equivalentes
    self.constraints = constraints # pares que nao podem ser equivalentes
    self.congruence_closure = congruence_closure # {v = [rank, [equivalence_class], [predecessors]]}
    self.merge_history = defaultdict(tuple) # to track the history of merges for conflict tracing [(equality): (justification)]
  
  # returns the unique name of the equivalence class of element
  def find(self, element):  
    if self.representatives[element] != element:
      # path compression: recursively set the representatives to the representatives
      self.representatives[element] = self.find(self.representatives[element])
      
    return self.representatives[element]

  # combines the equivalence classes of the elements (update representatives)
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

      self.representatives[smaller_representative] = greater_representative
    elif rank1 < rank2:
      greater_representative = root2
      smaller_representative = root1

      self.representatives[smaller_representative] = greater_representative
    else:
      # if ranks are the same, arbitrarily choose one as root and increment its rank
      greater_representative = root1
      smaller_representative = root2

      self.representatives[smaller_representative] = greater_representative
      self.congruence_closure[greater_representative][0] += 1

    # merge the equivalence classes
    greater_equivalence_class = self.congruence_closure[greater_representative][1]
    smaller_equivalence_class = self.congruence_closure[smaller_representative][1]
    greater_equivalence_class.extend(smaller_equivalence_class)

    # merge the predecessors
    greater_predecessor = self.congruence_closure[greater_representative][2]
    smaller_predecessor = self.congruence_closure[smaller_representative][2]
    greater_predecessor.update(smaller_predecessor)

  def congruent(self, u, v):
    # check if two vertices are congruent under the current relation:
    if self.graph[u][0] != self.graph[v][0] or len(self.graph[u][1]) != len(self.graph[v][1]):
      return False
    
    for i in range(len(self.graph[u][1])):
      if self.find(self.graph[u][1][i]) != self.find(self.graph[v][1][i]):
        return False
      
    return True
    
  # merge the equivalence classes of u and v
  def merge(self, u, v, justification, is_original):

    if self.find(u) == self.find(v): 
      return

    predecessors_u = self.congruence_closure[u][2].copy()
    predecessors_v = self.congruence_closure[v][2].copy()

    self.union(u, v)
    # record the merge for backtracking
    self.merge_history[(u, v, is_original)] = justification

    for x in predecessors_u:
      for y in predecessors_v:
        if self.find(x) != self.find(y) and self.congruent(x, y):
          self.merge(x, y, (u, v), False)

  def run_theory_solver(self):

    # merge the equivalence classes of equal pairs
    for x, y in self.equal_pairs:
      self.merge(x, y, None, True)

    # check if the final result is SAT under the set of constraints.
    for u, v in self.constraints:
      if self.find(u) == self.find(v):

        # DELETAR DEPOIS
        #######################################################
        print('\n')
        print(f'{u} AND {v} ARE EQUAL')
        print('BUT THEY SHOULD BE DIFFERENT')
        print('\n')
        #######################################################

        conflict = (u, v)
        unsat_core = self.trace_unsat_core(conflict)
        return False, unsat_core
      
    return True, None

  def trace_unsat_core(self, conflict):
    unsat_core = list()
    conflict_term = Expr(Symbol('equal', True), conflict[0], conflict[1])
    conflict_term = Expr(Symbol('not', True), conflict_term)
    
    unsat_core.append(conflict_term)
    if self.merge_history:
      # searches for the first pair of terms that are equivalent to the conflicting terms.
      for (x, y, z) in self.merge_history:
        if z and self.find(x) == self.find(conflict[0]) and self.find(y) == self.find(conflict[0]):
          equality = Expr(Symbol('equal', True), x, y)
          unsat_core.append(equality)
          justification = self.merge_history[(x, y, z)]

          # DELETAR DEPOIS
          #######################################################
          print(f'EQUALITY ADDED TO UNSAT CORE: {x}, {y}')
          print(f'JUSTIFICATION: {justification}')
          print('\n')
          #######################################################
          
          break

      # searches for the first pair of terms that are equivalent to the justification.
      while justification != None:
        for (x, y, z) in self.merge_history:
          if z and self.find(x) == self.find(justification[0]) and self.find(y) == self.find(justification[0]):
            equality = Expr(Symbol('equal', True), x, y)
            unsat_core.append(equality)
            justification = self.merge_history[(x, y, z)]

            # DELETAR DEPOIS
            #######################################################
            print(f'EQUALITY ADDED TO UNSAT CORE: {x}, {y}')
            print(f'JUSTIFICATION: {justification}')
            print('\n')
            #######################################################

            break
    return unsat_core

################################################################ AUXILIARY FUNCTIONS

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
    else:
      if term.op.name == "equal":
        for arg in term.args:
          create_vertices(arg, graph, congruence_closure, None)

        equal_pairs.append([x for x in term.args])
      else:
        create_vertices(term, graph, congruence_closure, None)
  
  return graph, constraints, equal_pairs, congruence_closure