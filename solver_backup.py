import copy
import random
import threading
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

DECISION_MODE = 5

num_of_clauses = -1

decisions = {
    0: 'naive' ,
    1: 'greedy_appearance' ,
    2: 'greedy_size',
    3: 'dfs' ,
    4: 'restart',
    5: 'opposite',
    10: 'everything'
}

class Literal:
    def __init__(self, ind, isNegation):
        self.ind = ind
        self.isNegation = isNegation

    def __eq__(self, other):
        return self.ind == other.ind and self.isNegation == other.isNegation

    def __cmp__(self, other):
        return self.ind >= other.ind
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
            ret += f"p{a.ind+1} : 1, "
        else:
            ret += f"p{a.ind+1} : 0, "
    print(ret.rstrip(","))

class Clause:
    def __init__(self, literals : dict[int, Literal] = None, cid = -1, parentid = -1):
        # {index : literal} structure
        self.literals = {} if literals is None else literals
        # used in memorial for unit propagation
        # if cid == -1, it says that this clause is not from original input
        self.cid = cid
        # if the clauses is originated from a certain assign,
        # parent should be a cid of original clause.
        # else (if from original input), cid == parent.
        self.parentid = parentid

    def __str__(self):
        ret = ""
        for l in self.literals.values():
            pre = "~" if l.isNegation else ""
            ret += f"{pre}{l.ind+1}, "
        return ret.rstrip(",") + "|"

    def isUnitClause(self):
        return len(self.literals.keys()) == 1

    def isEmpty(self):
        return self.literals == {}

    def isInvolved(self, ind):
        return ind in self.literals.keys()

    def getSign(self, ind):
        if ind not in self.literals.keys():
            return 0
        return -1 if self.literals[ind].isNegation else 1

    def getSize(self):
        return len(self.literals.keys())

    def __cmp__(self, other):
        return self.getSize() >= other.getSize()

    def getIndexOfLiterals(self):
        # set of indexes
        return set(self.literals.keys())

    def makeAssign(self, A : dict[Assignment]):
        ret_literals = self.literals.copy()
        for i, assignment in A.items():
            # if a variable(index i) is in clause
            if i in self.literals.keys():
                assert assignment.value is not None
                if (assignment.value == False and self.literals[i].isNegation) \
                        or (assignment.value == True and not self.literals[i].isNegation):
                    return None, True
                else:
                    ret_literals.pop(i)
                    if ret_literals == {}:
                        # confilct if it becomes an empty clause
                        return None, False

        # return remaining variables
        return Clause(ret_literals, cid=-1, parentid=self.parentid), True

    def addLiteral(self, l : Literal):
        #assert l not in self.getIndexOfLiterals() #todo
        self.literals[l.ind] = l

def printClauses(clauses):
    print("".join(map(str, clauses)))

def find_clause_with_cid(clauses : list[Clause], cid):
    assert cid != -1
    for clause in clauses:
        if clause.cid == cid:
            return clause

    raise KeyError

def resolvent(c1 : Clause, c2 : Clause):
    l1 = c1.getIndexOfLiterals()
    l2 = c2.getIndexOfLiterals()
    # common indexes - should be size 1
    # else, resolution cannot be defined
    intersect = l1 & l2
    #print(f"resolution : {c1} and {c2}")

    comp = set()
    for i in intersect:
        assert c1.isInvolved(i) and c2.isInvolved(i)
        if c1.literals[i].isNegation != c2.literals[i].isNegation:
            comp.add(i)
    assert len(comp) == 1

    # exclude complementary literals
    # include common literals only once
    c = Clause()
    for l in l1 - comp:
        c.addLiteral(c1.literals[l])
    for l in l2 - intersect:
        c.addLiteral(c2.literals[l])

    return c

def assign(F, clauses, A):
    ret_clauses = []
    is_conflict = False
    conflict_clauses = []

    for clause in clauses:
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
    F = clauses[:]
    A = {}
    order = [] # list of order that the variables' value is allocated
    free_inds = [i for i in range(k)] # list of all variable indices which is not allocated.
    former_states = [None for i in range(k+1)] # former state memory, for opposite method
    num_of_clauses = n

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
        print("------------------------------------------------------------")

        if print_clause:
            print("clause lists : ")
            for clause in F:
                print(clause)

        # should consider no unit prop
        F, is_conflict, conflict_clauses = assign(F, clauses, A)
        if F == [] and is_conflict == False:
            print("found satisfying assignment")
            return A, True

        while not is_conflict:
            has_unit_clause = False
            random.shuffle(F)
            for clause in F:
                if clause.isUnitClause():
                    L = list(clause.literals.values())[0]
                    has_unit_clause = True
                    assert L.ind not in A.keys()

                    if clause.cid == -1:
                        parent = find_clause_with_cid(clauses, clause.parentid)
                    else:
                        parent = clause

                    # conflict when the constraint not fits with current A
                    # if in conflict, a learned clause should be added.
                    A[L.ind] = Assignment(L.ind, False, TYPE_IMPLIED) if L.isNegation \
                        else Assignment(L.ind, True, TYPE_IMPLIED)
                    A[L.ind].setImpliedClause(parent)
                    if print_assign:
                        print(f"assigning new from unit prop : {L.ind}, {A[L.ind].value}")

                    value = A[L.ind].value
                    order.append(L.ind)
                    free_inds.remove(L.ind)
                    former_states[L.ind] = value

                    if DECISION_MODE == DECISION_RESTART or DECISION_MODE == DECISION_ALL:
                        if len(recent_buffer) < recent_buffer_size:
                            recent_buffer.append(value)
                        else:
                            recent_buffer = recent_buffer[1:] + [value]
                            recent_avg += (value - recent_buffer[0]) / recent_buffer_size

                    F, is_conflict, conflict_clauses = assign(clauses, clauses, A)
                    # if not conflict and no clause returned from assignment, return A.
                    if F == [] and is_conflict == False:
                        print("found satisfying assignment")
                        return A, True
                    if is_conflict == True:
                        if print_process:
                            print("conflict occurred from assigning")
                    break

            #repeat until F has no unit clause
            if not has_unit_clause:
                if print_process:
                    print("unit propagation complete, with no conflict")
                break

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

            if DECISION_MODE == DECISION_RESTART or DECISION_MODE == DECISION_ALL:
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

            while i > 0:
                # D means Di+1 in this loop
                # If pi -> bi is a decision assignment or pi is not mentioned in Di+1,
                # set Di = Di+1.

                item = list(A.values())[i-1]
                ind = item.ind
                if item.assignmentType == TYPE_DECISION or not Di.isInvolved(ind):
                    i -= 1
                # If pi -Ci-> bi is an implied assignment and pi is mentioned in Di+1,
                # define Di to be a resolvent of Ci and Di+1 with respect to pi.
                elif item.assignmentType == TYPE_IMPLIED and Di.isInvolved(ind):
                    Ci = item.impliedClause
                    Di = resolvent(Ci, Di)
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
                return {}, False

            # should set the cid to ++num_of_clauses
            # so that it can be used in another backtracking
            num_of_clauses += 1
            learned_clause.cid = num_of_clauses
            learned_clause.parentid = num_of_clauses
            # add learned clause
            clauses.append(learned_clause) #todo

            # Go back to the last moment when all other variables of D1 was
            # eliminated and D1 became a unit clause.
            # need a memorial data structure (list 'order')
            remove_inds = None
            assert list(A.keys()) == order
            if print_process:
                print(f"learned clause : {learned_clause}")
                print(f"order : {order}")

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
                free_inds.append(remove_ind)
                order.pop(-1)
                A.pop(remove_ind)

            # should re-initialize F
            F = assign(clauses, clauses, A)[0]

        else:
            # if not in conflict nor successful, make a decision
            if print_process:
                print("enter decision strategy")
            #printAssignments(A)
            if DECISION_MODE == DECISION_NAIVE:
                # naive : make a var with the random free index with random value
                # todo : propose a better strategy
                decision_ind = random.choice(free_inds)
                assert decision_ind not in A.keys()
                rand = random.random()
                value = rand > 0.5
                A[decision_ind] = Assignment(decision_ind, value, TYPE_DECISION)

                if print_assign:
                    print(f"assigning new from strategy : {decision_ind}, {value}")
                order.append(decision_ind)
                free_inds.remove(decision_ind)
                former_states[decision_ind] = value

            elif DECISION_MODE == DECISION_OPPOSITE:
                decision_ind = random.choice(free_inds)
                assert decision_ind not in A.keys()
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
                former_states[decision_ind] = value

            # ----------------- todo. modify these to fit the tree structure ---------------------

            elif DECISION_MODE == DECISION_GREEDY_APPEARANCE:
                # greedy : make true when normal appearance > negation appearance
                # make false when opposite situation
                decision_ind = random.choice(free_inds)
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
                former_states[decision_ind] = value

            elif DECISION_MODE == DECISION_GREEDY_SIZE:
                # greedy : select the remaining clause with minimal size
                # and make all the variable's value according to the sign of it in the clause
                min_clause = F[0]
                for decision_lit in min_clause.literals.values():
                    decision_ind = decision_lit.ind
                    A[decision_ind] = Assignment(decision_ind,
                            True if not decision_lit.isNegation else False, TYPE_DECISION)
                    order.append(decision_ind)
                    free_inds.remove(decision_ind)
                    former_states[decision_ind] = value

            elif DECISION_MODE == DECISION_RESTART:
                decision_ind = random.choice(free_inds)
                assert decision_ind not in A.keys()
                if former_states[decision_ind] is not None:
                    value = not former_states[decision_ind]
                else:
                    rand = random.random()
                    value = rand > 0.5

                assert decision_ind not in A.keys()
                A[decision_ind] = Assignment(decision_ind, value, TYPE_DECISION)
                if print_assign:
                    print(f"assigning new from strategy : {decision_ind}, {value}")
                order.append(decision_ind)
                free_inds.remove(decision_ind)
                former_states[decision_ind] = value

                if len(recent_buffer) < recent_buffer_size:
                    recent_buffer.append(value)
                    recent_avg = sum(recent_buffer) / recent_buffer_size

                else:
                    recent_buffer = recent_buffer[1:] + [value]
                    recent_avg += (value - recent_buffer[0]) / recent_buffer_size
                    variance = sum((x - recent_avg) ** 2 for x in recent_buffer) / len(recent_buffer)
                    to_restart = False
                    # have to restart when low variance

                    if variance < 0.25:
                        print(variance)
                        print(f"restarting search due to low variance")
                        to_restart = True
                    if minimal_conflict_number > conflict_buffer_size // 4:
                        print(f"restarting search due to many low level conflicts")
                        to_restart = True

                    if to_restart:
                        # should flush everything
                        F = clauses[:]
                        A = {}
                        order = []
                        free_inds = [i for i in range(k)]
                        recent_buffer = []
                        conflict_buffer = []
                        minimal_conflict_number = 0
