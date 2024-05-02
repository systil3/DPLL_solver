import copy
import random

TYPE_DECISION = 0
TYPE_IMPLIED = 1

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
            ret += f"p{a.ind} : 1, "
        else:
            ret += f"p{a.ind} : 0, "
    print(ret.rstrip(","))

def printClauses(clauses):
    return "".join(map(str, clauses))
class Clause:
    def __init__(self, literals : dict[int, Literal] = None):
        # {index : literal} structure
        self.literals = {} if literals is None else literals

    def __str__(self):
        ret = ""
        for l in self.literals.values():
            pre = "~" if l.isNegation else ""
            ret += f"{pre}{l.ind}, "
        return ret.rstrip(",") + "|"

    def isUnitClause(self):
        return len(self.literals.keys()) == 1

    def isEmpty(self):
        return self.literals == {}

    def isInvolved(self, ind):
        return ind in self.literals.keys()

    def getIndexOfLiterals(self):
        # set of indexes
        return set(self.literals.keys())

    def makeAssign(self, A : list[Assignment]):

        ret_literals = copy.deepcopy(self.literals)
        for i, assign in enumerate(A):
            # if a variable(index i) is in clause
            if i in self.literals.keys():
                if (A[i].value == False and self.literals[i].isNegation) \
                        or (A[i].value == True and not self.literals[i].isNegation):
                    return None, True
                else:
                   ret_literals.pop(i)

            if ret_literals == {}:
                # confilct if it becomes an empty clause
                return None, False

        # return remaining variables
        return Clause(ret_literals), True

    def addLiteral(self, l : Literal):
        #assert l not in self.getIndexOfLiterals() #todo
        self.literals[l.ind] = l

def resolvent(c1 : Clause, c2 : Clause):
    l1 = c1.getIndexOfLiterals()
    l2 = c2.getIndexOfLiterals()
    # common indexes
    intersect = l1 & l2

    comp = set()
    for i in intersect:
        assert c1.isInvolved(i) and c2.isInvolved(i)
        if c1.literals[i].isNegation != c2.literals[i].isNegation:
            comp.add(i)

    # exclude complementary literals
    # include common literals only once
    c = Clause()
    for l in l1 - comp:
        c.addLiteral(c1.literals[l])
    for l in l2 - intersect:
        c.addLiteral(c2.literals[l])

    return c

def assign(clauses, A):
    ret_clauses = []
    contains_empty_clause = False
    conflict_clauses = []

    for clause in clauses:
        ret_clause = clause.makeAssign(A)
        if ret_clause == (None, False):
            #when confilct
            #add an empty clause
            contains_empty_clause = True
            ret_clauses.append(Clause())
            conflict_clauses.append(clause)

        #when clause is already satisfied, we can just ignore it
        elif ret_clause != (None, True):
            ret_clauses.append(ret_clause[0])

    return ret_clauses, contains_empty_clause, conflict_clauses

# n is the number of clauses
# k is the number of variables
def solve(clauses : list[Clause], n, k):
    """
    :param clauses:
    :param n: num of clauses
    :param k: num of variables
    :return: (Assignments(if satisfiable), isSat (true / false)
    """

    #Initialise A to the empty list of assignments
    F = clauses
    A = {}
    order = [] #list of order that the variables' value is allocated

    while True:
        # Unit Propagation.
        # While there is a unit clause {L} in F|A, add L->1 to A.
        print("clause lists : ")
        for clause in F:
            print(clause)

        for clause in F:
            if clause.isUnitClause():
                L = list(clause.literals.values())[0]

                # conflict when the constraint not fits with current A
                # if in conflict, a learned clause should be added.
                A[L.ind] = Assignment(L.ind, False, TYPE_IMPLIED) if L.isNegation \
                    else Assignment(L.ind, True, TYPE_IMPLIED)
                A[L.ind].setImpliedClause(clause)
                order.append(L.ind)

        # If F|A contains no clauses, stop & output A.
        print("assignment : ", end='')
        printAssignments(A)

        # todo : find out if this way is correct
        assign_result = assign(clauses, A)
        F = assign_result[0]  #

        print("assign result : ", end="")
        #printClauses(assign_result[0])
        print(f"empty clause : {assign_result[1]} ")

        if assign_result[0] == []:
            print("found satisfying assignment")
            return A, True
        is_conflict = assign_result[1]

        # If F|A contains an empty clause,
        # Find a clause C by learning procedure & add it to F.
        # do the following:
        if is_conflict:
            print("enter conflict handling")
            # Suppose A = {p1->b1, ... , pk->bk} leads to conflict.
            # Pick any conflict clause D_k+1 under A.
            conflict_clauses = assign_result[2]
            #assert len(A) == k
            i = len(A)
            Di = conflict_clauses[-1]

            while i > 0:
                # D means Di+1 in this loop
                # If pi -> bi is a decision assignment or pi is not mentioned in Di+1,
                # set Di = Di+1.

                # regarding i as from 0 to len(A) only works at the current temporary
                # decision strategy. todo : find another method when apply other strategy
                ind = A[i-1].ind
                if A[i-1].assignmentType == TYPE_DECISION or not Di.isInvolved(ind):
                    i -= 1
                # If pi -Ci-> bi is an implied assignment and pi is mentioned in Di+1,
                # define Di to be a resolvent of Ci and Di+1 with respect to pi.
                elif A[i-1].assignmentType == TYPE_IMPLIED and Di.isInvolved(ind):
                    Ci = A[i-1].impliedClause
                    Di = resolvent(Ci, Di)
                    i -= 1
                else:
                    raise ValueError

            # The final clause D1 is the learned clause.
            # A learned clause is added to F.
            # If a learned clause is empty, return UNSAT.
            learned_clause = Di
            if learned_clause.isEmpty():
                print("learned clause empty, returning unsat")
                return {}, False
            print(f"added learned clause : {learned_clause}\n")
            F.append(learned_clause)

            # Go back to the last moment when all other variables of D1 was
            # eliminated and D1 became a unit clause.
            # need a memorial data structure (list 'order')
            remove_inds = None
            print(f"order : {order}")
            learned_inds = learned_clause.getIndexOfLiterals()
            for i, order_ind in enumerate(order):
                if order_ind in learned_inds:
                    if len(learned_inds) > 1:
                        learned_inds.remove(order_ind)
                    else: # right time
                        remove_inds = order[i:]

            print(f"removed variable {remove_inds} from A to go to unit propagation")
            # remove some variable allocation from assignment
            # to make D1 a unit clause
            assert remove_inds is not None
            for remove_ind in remove_inds:
                order.pop(-1)
                A.pop(remove_ind)

        # if not in conflict nor successful, make a decision
        else:
            # temporarily, make a var with the smallest index with random value
            # todo : propose a better strategy
            decision_ind = 0
            while True:
                if decision_ind not in A.keys():
                    rand = random.random()
                    A[decision_ind] = Assignment(decision_ind,
                        True if rand > 0.5 else False, TYPE_DECISION)
                    order.append(decision_ind)
                    break
                decision_ind += 1
                if decision_ind >= k:
                    break


