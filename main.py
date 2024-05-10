from solver import *
import sys

if __name__ == '__main__':
    comments = ""
    while True:
        line = sys.stdin.readline().split(" ")

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
    for i in range(n):
        line = sys.stdin.readline().split(" ")

        # increasing order (by abs)
        indexes = line[:-1]
        assert line[-1] == '0\n'
        indexes.sort(key = lambda x : abs(int(x)))

        clause = Clause()
        for j in indexes:
            clause.addLiteral(
                Literal(abs(int(j))-1, True if j[0] == '-' else False))
        Formula.append(clause)


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
    sys.exit(0)