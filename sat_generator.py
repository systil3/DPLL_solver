import random
import numpy as np

def generate_sat_input(num_variables, num_clauses):
    # Generate comments
    comments = [f"c This is a random SAT instance with {num_variables} variables and {num_clauses} clauses"]

    # Generate the header line
    header = f"p cnf {num_variables} {num_clauses}"

    # Generate clauses
    clauses = []
    for _ in range(num_clauses):
        clause = []

        num_lit_clause = random.randint(4, 5)
        indices = [i for i in range(num_lit_clause)]
        literals = random.sample(range(1, num_variables + 1), num_lit_clause)
        literals = np.array([lit for lit in literals])
        signs = np.random.choice([-1, 1], size=num_lit_clause, p=[0.5, 0.5])
        clause.extend(literals * signs)
        clause.append(0)
        clauses.append(" ".join(map(str, clause)))

    # Combine comments, header, and clauses
    sat_input = "\n".join(comments + [header] + clauses)

    return sat_input

def save_sat_input(sat_input, filename):
    with open(filename, "w") as file:
        file.write(sat_input)

# Example usage
num_variables = 400
num_clauses = 2000
directory = './sat_inputs_large/'
for i in range(10):
    filename = f"input_{num_variables}vars_{num_clauses}clauses_{i}.cnf"
    sat_input = generate_sat_input(num_variables, num_clauses)
    save_sat_input(sat_input, directory + filename)
    print(f"SAT input saved to {filename}")