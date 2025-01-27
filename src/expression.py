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

################################################################ AUXILIARY FUNCTIONS

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
  
  elif formula.is_iff():
    left = convert_to_expr(formula.arg(0))  
    right = convert_to_expr(formula.arg(1)) 
    # a <=> b = (a => b) and (b => a)
    return Expr(Symbol('and', True), Expr(Symbol('implies', True), left, right), Expr(Symbol('implies', True), right, left))
  
  if formula.is_ite():
    condition = convert_to_expr(formula.arg(0))
    true_expr = convert_to_expr(formula.arg(1))
    false_expr = convert_to_expr(formula.arg(2))

    neg_condition = Expr(Symbol('not', True), condition)
    return Expr(Symbol('or', True), Expr(Symbol('and', True), condition, true_expr), Expr(Symbol('and', True), neg_condition, false_expr))
  
  else:
    raise ValueError(f"Error: {formula}")
  
# preprocesses a logical formula by converting it to CNF
def formula_preprocessing(formula):
  formula_expr = convert_to_expr(formula)

  formula_nnf = formula_expr.to_nnf()
  formula_cnf = formula_nnf.to_cnf()

  return formula_cnf

# extracts the set of clauses from a CNF formula
def get_clause_set(formula_cnf):
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

  extract_clauses(formula_cnf)
  return clause_set

# creates an abstraction by converting terms in the clause set to integers
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