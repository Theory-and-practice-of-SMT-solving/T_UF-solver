from utils import *
import sys
import os

def main():
  # check if the correct number of arguments are passed
  if len(sys.argv) < 2:
    print("Usage: main.py filename")
    print("Error: the following arguments are required: filename")
    sys.exit(1)
  else:
    filename = sys.argv[1]

    # get the absolute path of the file
    filename = os.path.abspath(filename)
  
  # parse the formula from the given file
  formula_cnf = run_parser(filename)

  # extract the set of clauses
  clause_set = get_clause_set(formula_cnf)
  
  # create an abstraction of the clauses, mapping each term to an integer
  abstract_clause_set, term_to_int_map, int_to_term_map = create_abstraction(clause_set)

  # run the framework, which solves the problem iteratively using the SAT and theory solvers  
  framework(abstract_clause_set, term_to_int_map, int_to_term_map)

if __name__ == "__main__":
  main()
