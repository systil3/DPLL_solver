import asyncio
import aiofiles
import os
import time
from solver import *

BATCH = 10

async def read_cnf_from_file(filename):
    async with aiofiles.open(filename, 'r') as file:
        comments = ""
        lines = await file.readlines()
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
            clause = Clause(literals=None, cid=i, parentid=i)
            for j in indexes:
                clause.addLiteral((abs(int(j)) - 1, True if j[0] == '-' else False))
            Formula.append(clause)

        return Formula, n, k

async def process_files(directory):
    files = os.listdir(directory)
    start_time = time.time()

    for filename in files:
        Formula, n, k = await read_cnf_from_file(directory + '/' + filename)
        print(f"testing file {filename}")
        for i in range(BATCH):
            solve_result = solve(Formula.copy(), n, k)
            solution = solve_result[0]
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

if __name__ == '__main__':
    directory = './sat_inputs_small'
    asyncio.run(process_files(directory))