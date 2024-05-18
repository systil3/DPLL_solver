import concurrent
import copy
import random
import time

TYPE_DECISION = 0
TYPE_IMPLIED = 1
print_clause = False
print_assign = False
print_process = False
DECISION_NAIVE = 0
DECISION_OPPOSITE = 5
DECISION_GREEDY_APPEARANCE = 1
DECISION_GREEDY_SIZE = 2
DECISION_DFS = 3
DECISION_RESTART = 4

DECISION_ALL = 10

DECISION_MODE = 2

num_of_clauses = -1

elapsed_time_copy = 0
elapsed_time_unit_prop = 0

decisions = {
    0: 'naive' ,
    1: 'greedy_appearance' ,
    2: 'greedy_size',
    3: 'dfs' ,
    4: 'restart',
    5: 'opposite',
    10: 'everything'
}
class Assignment:
    def __init__(self, ind, value, assignmentType):
        self.ind = ind
        self.value = value
        # pi -> bi by a decision strategy is a decision assignment
        # pi -c-> bi by a unit propagation on a clause c is an implied assignment
        self.assignmentType = assignmentType
        self.impliedClause = None

    def setImpliedClause(self, c):
        self.impliedClause = c

def printAssignments(A):
    ret = ""
    for a in A.values():
        if a.value == True:
            ret += f"p{a.ind} : 1, "
        else:
            ret += f"p{a.ind} : 0, "
    print(ret.rstrip(","))

class Clause:
    def __init__(self, literals, cid, parentid):
        # {index : literal} structure
        self.literals = {} if literals is None else literals
        # used in memorial for unit propagation
        # if cid == -1, it says that this clause is not from original input
        self.cid = cid
        # if the clauses is originated from a certain assign,
        # parent should be a cid of original clause.
        # else (if from original input), cid == parent.
        self.parentid = parentid
        self.length = len(self.literals) if literals is not None else 0

    def __str__(self):
        ret = ""
        for l in self.literals.values():
            pre = "~" if l[1] else ""
            ret += f"{pre}{l[0]}, "
        return ret.rstrip(",") + "|"

    def isUnitClause(self):
        return self.length == 1

    def isEmpty(self):
        return self.literals == {}

    def isInvolved(self, ind):
        return ind in self.literals.keys()

    def getSign(self, ind):
        if ind not in self.literals.keys():
            return 0
        return -1 if self.literals[ind][1] else 1

    def getSize(self):
        if self.literals is None:
            return 0
        else:
            return len(self.literals.keys())
    def __cmp__(self, other):
        return self.getSize() >= other.getSize()
    def getIndexOfLiterals(self):
        # set of indexes
        return set(self.literals.keys())

    def makeAssign(self, A : dict[int, (int, bool)]):
        start_time = time.time()
        ret_literals = self.literals.copy()
        global elapsed_time_copy
        elapsed_time_copy += time.time() - start_time

        for i, assignment in A.items():
            # if a variable(index i) is in clause
            if i in self.literals.keys():
                assert assignment.value is not None
                if (assignment.value == False and self.literals[i][1]) \
                        or (assignment.value == True and not self.literals[i][1]):
                    return None, True
                else:
                    ret_literals.pop(i)
                    if ret_literals == {}:
                        # confilct if it becomes an empty clause
                        return None, False

        # return remaining variables
        return Clause(ret_literals, cid=-1, parentid=self.parentid), True

    def addLiteral(self, l : (int, bool)):
        #assert l not in self.getIndexOfLiterals() #todo
        self.literals[l[0]] = l

    def removeLiteral(self, index):
        if index in self.literals.keys():
            del self.literals[index]
            self.length -= 1
        else:
            raise KeyError

def printClauses(clauses):
    print("".join(map(str, clauses)))

def find_clause_with_cid(clauses : list[Clause], cid):
    assert cid != -1 and cid < num_of_clauses
    clause = clauses[cid]
    assert clause.cid == cid
    return clause

def resolvent(c1 : Clause, c2 : Clause, ind):
    l1 = c1.getIndexOfLiterals()
    l2 = c2.getIndexOfLiterals()
    # common indexes - should be size 1
    # else, resolution cannot be defined
    intersect = l1 & l2
    #print(f"resolution : {c1} and {c2} for variable {ind}")

    comp = set()
    for i in intersect:
        assert c1.isInvolved(i) and c2.isInvolved(i)
        if c1.literals[i][1] != c2.literals[i][1]:
            comp.add(i)
    assert len(comp) == 1

    # exclude complementary literals
    # include common literals only once
    c = Clause(literals=None, cid=-1, parentid=c1.parentid)
    for l in l1 - comp:
        c.addLiteral(c1.literals[l])
    for l in l2 - intersect:
        c.addLiteral(c2.literals[l])

    return c

def assign(F, clauses, A):
    ret_clauses = []
    is_conflict = False
    conflict_clauses = []

    for clause in F:
        ret_clause = clause.makeAssign(A)
        if ret_clause == (None, False):
            #when conflict
            is_conflict = True
            parent_clause = find_clause_with_cid(clauses, clause.parentid)
            for ind in parent_clause.getIndexOfLiterals():
                assert ind in A.keys()
            conflict_clauses.append(parent_clause)

        #when clause is already satisfied, we can just ignore it
        elif ret_clause != (None, True):
            ret_clauses.append(ret_clause[0])

    return ret_clauses, is_conflict, conflict_clauses

# n is the number of clauses
# k is the number of variables
def solve(clauses : list[Clause], n, k):
    """
    :param clauses:
    :param n: num of clauses
    :param k: num of variables
    :return: (Assignments(if satisfiable), isSat (true / false)
    """

    print(f"Starting to solve SAT with method {decisions[DECISION_MODE]}...")
    #Initialise A to the empty list of assignments
    global num_of_clauses
    global elapsed_time_copy
    global elapsed_time_unit_prop
    F = copy.deepcopy(clauses)
    A = {}
    order = [] # list of order that the variables' value is allocated
    free_inds = set([i for i in range(k)]) # list of all variable indices which is not allocated.
    former_states = [None for i in range(k+1)] # former state memory, for opposite method
    num_of_clauses = n

    # for restart
    recent_buffer_size = n // 5 if n >= 5 else 1
    recent_buffer = []
    recent_avg = 0
    conflict_buffer = []
    conflict_buffer_size = 24
    minimal_conflict_level = 20
    minimal_conflict_number = 0

    while True:
        # Unit Propagation.
        # While there is a unit clause {L} in F|A, add L->1 to A.
        if print_process:
            print("------------------------------------------------------------")

        F, is_conflict, conflict_clauses = assign(F, clauses, A)

        if print_clause:
            print("clause lists : ")
            for clause in F:
                print(clause)

        if F == [] and is_conflict == False:
            print("found satisfying assignment")
            print(f"elapsed time to copy : {elapsed_time_copy}")
            return A, True

        # unit propagation.
        start_time = time.time()
        print(len(F))
        # Optimize the data structures for faster access
        # random.shuffle(F)
        unit_clauses = [clause for clause in F if clause.isUnitClause()]
        while (not is_conflict) and unit_clauses:
            for clause in unit_clauses:
                L = list(clause.literals.values())[0]
                ind = L[0]

                parent = find_clause_with_cid(clauses, clause.parentid)
                if ind in A.keys():
                    continue
                assert parent.isInvolved(ind)

                # Set assignment based on unit clause
                value = not L[1]
                A[ind] = Assignment(ind, value, TYPE_IMPLIED)
                A[ind].setImpliedClause(parent)
                if print_assign:
                    print(f"assigning new from unit prop: {ind}, {A[ind].value}")

                # Record the assignment and update structures
                order.append(ind)
                free_inds.remove(ind)

                # Handle decision modes and recent buffer
                recent_buffer.append(value)
                if len(recent_buffer) < recent_buffer_size:
                    recent_buffer.append(value)
                    recent_avg += value / recent_buffer_size
                else:
                    recent_buffer.append(value)
                    recent_avg += (value - recent_buffer[0]) / recent_buffer_size
                    recent_buffer.pop(0)

                # Assign and check for conflicts immediately
            F, is_conflict, conflict_clauses = assign(clauses, clauses, A)
            if F == [] and not is_conflict:
                print("found satisfying assignment")
                print(f"elapsed time to copy: {elapsed_time_copy}")
                print(f"elapsed time for unit prop: {elapsed_time_unit_prop}")
                return A, True
            if is_conflict:
                if print_process:
                    print("conflict occurred from assigning")
                break

            # Re-check unit clauses after changes
            unit_clauses = [clause for clause in F if clause.isUnitClause()]
            if not unit_clauses and print_process:
                print("unit propagation complete, with no conflict")

        elapsed_time_unit_prop += time.time() - start_time

        if print_clause:
            print("assign result - ", end="")
            print(f"empty clause : {is_conflict} ")

        # If F|A contains an empty clause,
        # Find a clause C by learning procedure & add it to F.
        # do the following:
        if is_conflict:
            if print_process:
                print("enter conflict handling")
                print(f"conflict clause : {conflict_clauses[0]}")
            if print_assign:
                printAssignments(A)
            # Suppose A = {p1->b1, ... , pk->bk} leads to conflict.
            # Pick any conflict clause D_k+1 under A.
            #assert len(A) == k

            i = len(A)
            Di = conflict_clauses[0]
            conflict_level = len(order)
            if print_process:
                print(f"conflict level : {conflict_level}")
            if len(conflict_buffer) < conflict_buffer_size:
                minimal_conflict_number += int(conflict_level < minimal_conflict_level)
                conflict_buffer.append(conflict_level)
            else:
                minimal_conflict_number += int(conflict_level < minimal_conflict_level) \
                                             - int(conflict_buffer[0] < minimal_conflict_level)
                conflict_buffer = conflict_buffer[1:] + [conflict_level]
            for a in A.values():
                former_states[a.ind] = a.value

            values = list(A.values())
            while i > 0:
                # D means Di+1 in this loop
                # If pi -> bi is a decision assignment or pi is not mentioned in Di+1,
                # set Di = Di+1.

                item = values[i-1]
                ind = item.ind
                if item.assignmentType == TYPE_DECISION or not Di.isInvolved(ind):
                    i -= 1
                # If pi -Ci-> bi is an implied assignment and pi is mentioned in Di+1,
                # define Di to be a resolvent of Ci and Di+1 with respect to pi.
                elif item.assignmentType == TYPE_IMPLIED and Di.isInvolved(ind):
                    Ci = item.impliedClause
                    assert Ci.isInvolved(ind)
                    Di = resolvent(Ci, Di, ind)
                    i -= 1
                else:
                    raise ValueError

            # The final clause D1 is the learned clause.
            # A learned clause is added to F.
            # If a learned clause is empty, return UNSAT.
            learned_clause = Di
            if learned_clause.isEmpty():
                if print_process:
                    print("learned clause empty, returning unsat")
                print(f"elapsed time to copy : {elapsed_time_copy}")
                print(f"elapsed time for unit prop : {elapsed_time_unit_prop}")
                return {}, False

            # should set the cid to ++num_of_clauses
            # so that it can be used in another backtracking
            num_of_clauses += 1
            learned_clause.cid = num_of_clauses-1
            learned_clause.parentid = num_of_clauses-1
            # add learned clause
            clauses.append(learned_clause) #todo
            F.sort(key=lambda c: c.getSize())

            # Go back to the last moment when all other variables of D1 was
            # eliminated and D1 became a unit clause.
            # need a memorial data structure (list 'order')
            remove_inds = None
            assert list(A.keys()) == order
            if print_process:
                print(f"learned clause : {learned_clause}")
                #print(f"order : {order}")

            learned_inds = learned_clause.getIndexOfLiterals()
            l = len(learned_inds)

            if l != 1:
                for i, order_ind in enumerate(order):
                    if order_ind in learned_inds:
                        learned_inds.remove(order_ind)
                        l -= 1
                        if l <= 1: # right time
                            remove_inds = order[i+1:]
                            break
            else:
                i = order.index(list(learned_inds)[0])
                remove_inds = order[i:]

            if print_process:
                print(f"removed variable {remove_inds} from A to go to unit propagation")

            # remove some variable allocation from assignment
            # to make D1 a unit clause

            assert remove_inds is not None
            for remove_ind in remove_inds:
                free_inds.add(remove_ind)
                order.pop(-1)
                A.pop(remove_ind)

            # should re-initialize F
            F = assign(clauses, clauses, A)[0]
            F.sort(key=lambda c : c.getSize())

        else:
            # if not in conflict nor successful, make a decision
            if print_process:
                print("enter decision strategy")
            #printAssignments(A)
            if DECISION_MODE in (DECISION_NAIVE, DECISION_GREEDY_SIZE, DECISION_OPPOSITE):
                # naive : make a var with the random free index with random value
                # todo : propose a better strategy
                decision_ind = random.sample(sorted(free_inds), 1)[0]
                assert decision_ind not in A.keys()

                if DECISION_MODE == DECISION_NAIVE:
                    rand = random.random()
                    value = rand > 0.5
                    A[decision_ind] = Assignment(decision_ind, value, TYPE_DECISION)
                elif DECISION_MODE == DECISION_GREEDY_SIZE:
                    # greedy : select the remaining clause with minimal size
                    # and make all the variable's value according to the sign of it in the clause
                    #F.sort(key=lambda c : c.getSize())
                    min_clause = F[0]
                    #decision_ind = random.choice(list(min_clause.getIndexOfLiterals()))
                    decision_ind = list(min_clause.getIndexOfLiterals())[0]
                    decision_lit = min_clause.literals[decision_ind]
                    value = not decision_lit[1]
                    A[decision_ind] = Assignment(decision_ind, value, TYPE_DECISION)

                elif DECISION_MODE == DECISION_OPPOSITE:
                    if former_states[decision_ind] is not None:
                        value = not former_states[decision_ind]
                    else:
                        rand = random.random()
                        value = rand > 0.5
                    A[decision_ind] = Assignment(decision_ind, value, TYPE_DECISION)

                if print_assign:
                    print(f"assigning new from strategy : {decision_ind}, {value}")
                order.append(decision_ind)
                free_inds.remove(decision_ind)

                #to_restart = random.random() < 0.2

                if len(recent_buffer) < recent_buffer_size:
                    recent_buffer.append(value)
                    recent_avg += value / recent_buffer_size
                else:
                    recent_buffer.append(value)
                    recent_avg += (value - recent_buffer[0]) / recent_buffer_size
                    recent_buffer.pop(0)
                    variance = sum((x - recent_avg) ** 2 for x in recent_buffer) / len(recent_buffer)
                    to_restart = False
                    # have to restart when low variance
                    if variance < 0.25:
                        print(f"restarting search due to low variance")
                        to_restart = True
                    if minimal_conflict_number > conflict_buffer_size // 4:
                        print(f"restarting search due to many low level conflicts")
                        to_restart = True
                    if to_restart and is_conflict:
                        # should flush everything
                        F = clauses[:]
                        elapsed_time_copy += time.time() - start_time
                        A = {}
                        order = []
                        free_inds = set([i for i in range(k)])
                        recent_buffer = []
                        conflict_buffer = []
                        minimal_conflict_number = 0

            # ----------------- todo. modify these to fit the tree structure ---------------------

            elif DECISION_MODE == DECISION_GREEDY_APPEARANCE:
                # greedy : make true when normal appearance > negation appearance
                # make false when opposite situation
                #decision_ind = random.sample(sorted(free_inds), 1)[0]
                decision_ind = sorted(free_inds)[0]
                assert decision_ind not in A.keys()
                normal_app, neg_app = 0, 0
                for remain_clause in F:
                    if remain_clause.getSign(decision_ind) == 1:
                        normal_app += 1
                    if remain_clause.getSign(decision_ind) == -1:
                        neg_app += 1
                rand = random.random()
                A[decision_ind] = Assignment(decision_ind,
                        True if rand < normal_app / (normal_app+neg_app) else False, TYPE_DECISION)
                order.append(decision_ind)
                free_inds.remove(decision_ind)
