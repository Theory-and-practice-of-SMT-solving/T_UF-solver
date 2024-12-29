from pysmt.shortcuts import Symbol
from pysmt.smtlib.parser import SmtLibParser
from graphviz import Digraph
import os

# defines a symbol, that can be a constant (is_function = False) or a function (is_function = True) 
# examples of Symbol object -----> name = or, is_function = yes
class Symbol:
  def __init__(self, name, is_function):
    self.name = name
    self.is_function = is_function

# defines an arbitrary expression, following the syntax specified in the documentation
# op is a symbol, that can contain args (if it is a function)
# example of Expr object -----> op = or, args = [(b and c), (e)] -> (b and c) or e 
# in the example above, all the args are also Expr objects
class Expr:
  def __init__(self, op, *args):
    self.op = op
    self.args = args

  # converting from arbitrary expression to negation normal form (NNF)
  def to_nnf(self):
    # it contains only one argument
    if self.op.name == 'not':
      neg_expr = self.args[0] # getting the argument

      if neg_expr.op.name == 'not':
        # not (not x) = x
        return neg_expr.args[0].to_nnf()
      
      elif neg_expr.op.name == 'equal':
        # not (a equal b) = a not equal b
        return Expr(Symbol('not equal', True), *(arg.to_nnf() for arg in neg_expr.args))
      
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

    elif self.op.name == 'not equal':
      left = self.args[0].to_cnf()
      right = self.args[1].to_cnf()
      return Expr(Symbol('not equal', True), left, right)

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

# main
parser = SmtLibParser() 
script = parser.get_script_fname("testCase05.smt2")

formula = script.get_last_formula() 
expr = convert_to_expr(formula) 

nnf_expr = expr.to_nnf() 
nnf_expr.to_tree('nnf_tree')

cnf_expr = nnf_expr.to_cnf() 
cnf_expr.to_tree('cnf_tree')

clause_set = get_clause_set(cnf_expr)

print('\n')
print(f"original formula: {formula}")
print(f"intermediate formula: {expr}")
print('\n')
print(f"NNF formula: {nnf_expr}")
print(f"CNF formula: {cnf_expr}")
print('\n')
print(f'Clause Set: {clause_set}')
print('\n')

# tarefas
# 1) modificar to_nnf e to_cnf para utilizar iteração ao invés de recursão
