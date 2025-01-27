# T_UF-solver

A solver for the Theory of Uninterpreted Functions

Group:

- Sarah Azevedo Pereira
- Wesley Marques Daniel Chaves

# Instructions

1. Create and activate a virtual environment to ensure the project's dependencies are isolated:

   - Windows:

     ```bash
     python -m venv name-venv
     name-venv\Scripts\activate
     ```

   - Linux/Mac:
     ```bash
     python3 -m venv name-venv
     source name-venv/bin/activate
     ```

2. Install the project dependencies listed in the `requirements.txt` file:

   ```bash
   pip install -r requirements.txt
   ```

3. Run the project:

   ```bash
   python src/main.py filename
   ```

4. Deactivate the virtual environment when finished:
   ```bash
   deactivate
   ```

## Structure

```plaintext
project/
│
├── src/
│ ├── main.py
│ ├── expression.py
│ ├── theorysolver.py
│ └── utils.py
│
├── requirements.txt
└── README.md
```
