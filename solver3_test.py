from solver import *
import sys
import os

BATCH = 10
def read_cnf_from_file(filename):
    with open(filename, 'r') as file:
        comments = ""
        lines = file.readlines()
        comment_len = 0
        for line in lines:
            line = line.split(" ")
            comment_len += 1
            # comment
            if line[0] == "c":
                comments += line[0] + '\n'
            elif line[0] == "p":
                # format : p cnf k n
                assert len(line) == 4
                assert line[1] == "cnf"
                k, n = int(line[2]), int(line[3])
                break

        Formula = []
        for i in range(n-1):
            line = lines[i + comment_len]
            line = line.split(" ")

            # increasing order (by abs)
            indexes = line[:-1]
            indexes.sort(key=lambda x: abs(int(x)))

            clause = Clause(cid=i, parentid=i)
            for j in indexes:
                clause.addLiteral(
                    Literal(abs(int(j)) - 1, True if j[0] == '-' else False))
            Formula.append(clause)

        return Formula, n, k

if __name__ == '__main__':
    directory = './sat_inputs_small'
    files = os.listdir(directory)
    start_time = time.time()

    for filename in files:
        Formula, n, k = read_cnf_from_file(directory + '/' + filename)

        for i in range(BATCH):
            solve_result = solve(Formula, n, k)
            solution = solve_result[0]
            #assert solve_result[1] == True

            s = "SATISFIABLE" if solve_result[1] else "UNSATISFIABLE"
            print(f"s {s}")
            if s == "SATISFIABLE":
                print("v ", end='')
                ret = ""
                for assignment in solution.values():
                    if assignment.value == False:
                        ret += str(assignment.ind+1) + " "
                print(f"{ret}0")
    end_time = time.time()
    elapsed_time = end_time - start_time

    print(f"total computation time ({len(files) * BATCH} iterations):", round(elapsed_time, 3), "sec")
    print(f"average computation time : {round(elapsed_time / (len(files) * BATCH), 3)} sec")