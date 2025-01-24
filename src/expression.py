from graphviz import Digraph
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