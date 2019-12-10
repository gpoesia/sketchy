from enum import Enum, auto

class Nonterminals(Enum):
    FUNCTION = auto()
    STMTLIST = auto()
    STMT = auto()
    ASSIGNMENT = auto()
    ASSERTION = auto()
    IF = auto()
    FOR = auto()
    BVEXPR = auto()
    BVOP2 = auto()
    BVOP1 = auto()
    BOOLEXPR = auto()
    BOOLOP2 = auto()
    BOOLOP1 = auto()
    BVCOMP = auto()
    PHI = auto()



