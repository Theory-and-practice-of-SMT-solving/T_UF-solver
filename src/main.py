from utils import *
import sys
import os

def main():

  if len(sys.argv) < 2:
    print("Usage: main.py filename")
    print("Error: the following arguments are required: filename")
    sys.exit(1)
  else:
    filename = sys.argv[1]

    # get the absolute path of the file
    filename = os.path.abspath(filename)

  formula_cnf = run_parser(filename)
  clause_set = get_clause_set(formula_cnf)
  abstract_clause_set, term_to_int_map, int_to_term_map = create_abstraction(clause_set)

  framework(abstract_clause_set, term_to_int_map, int_to_term_map)

if __name__ == "__main__":
  main()
