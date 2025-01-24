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
  def merge(self, u, v, justification):

    #######################################################
    print(f'{u} AND {v} ARE EQUAL')
    print('\n')
    #######################################################

    if self.find(u) == self.find(v): 

      #######################################################
      print('THEY ALREADY BELONG TO THE SAME CLASS')
      print('\n')
      #######################################################
      
      return

    predecessors_u = self.congruence_closure[u][2].copy()
    predecessors_v = self.congruence_closure[v][2].copy()

    self.union(u, v)
    # record the merge for backtracking
    self.merge_history[(u, v)] = justification

    #######################################################
    self.show()
    print('\n')
    #######################################################

    for x in predecessors_u:
      for y in predecessors_v:
        if self.find(x) != self.find(y) and self.congruent(x, y):
          self.merge(x, y, (u, v))

  def run_theory_solver(self):

    #######################################################
    print("--------------------------------------------------------------------------------")
    print('START - ALGORITHM')
    print('\n')
    self.show()
    print('\n')
    #######################################################

    # merge the equivalence classes of equal pairs
    for x, y in self.equal_pairs:
      self.merge(x, y, None)

    #######################################################
    print('END - ALGORITHM')
    print('\n')
    #######################################################

    # check if the final result is SAT under the set of constraints.
    for u, v in self.constraints:
      if self.find(u) == self.find(v):

        #######################################################
        print(f'{u} AND {v} ARE EQUAL')
        print('\n')
        print('BUT THEY SHOULD BE DIFFERENT')
        print('\n')
        print("--------------------------------------------------------------------------------")
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
    # searches for the first pair of terms that are equivalent to the conflicting terms.
    for (x, y) in self.merge_history:
      if self.find(x) == self.find(conflict[0]) and self.find(y) == self.find(conflict[0]):
        equality = Expr(Symbol('equal', True), x, y)
        unsat_core.append(equality)
        # print(equality)

        justification = self.merge_history[(x, y)]
        break
    
    while justification != None:
      print(justification)
      print('aqui, no lado direito da equação é uma igualdade derivada')
      # backtrack through the merge history to identify contributing equations
      unsat_core.append(justification)
      justification = self.merge_history[justification]

    # print(unsat_core)
    return unsat_core
  
  #######################################################
  def show(self):
    for i, _ in self.congruence_closure.items():
        print(f'VERTEX: {i} ----------> REPRESENTATIVE: {self.find(i)}')
  #######################################################