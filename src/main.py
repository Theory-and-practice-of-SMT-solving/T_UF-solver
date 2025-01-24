from utils import *

def main():
  base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
  tests_dir = os.path.join(base_dir, "tests")
  filename = os.path.join(tests_dir, "testCase01.smt2") # nome do arquivo de teste que está na pasta tests

  formula_cnf = run_parser(filename)
  clause_set = get_clause_set(formula_cnf)
  abstract_clause_set, term_to_int_map, int_to_term_map = create_abstraction(clause_set)

  #######################################################
  print('\n')
  print("CLAUSE SET")
  print(clause_set)
  print('\n')
  print("ABSTRACT CLAUSE SET")
  print(abstract_clause_set)
  print("\n")
  #######################################################

  framework_CDCL(abstract_clause_set, term_to_int_map, int_to_term_map)

if __name__ == "__main__":
  main()
