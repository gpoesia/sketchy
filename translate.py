from enum import Enum, auto

class NT(Enum):
    FUNCTION = auto()   # PARAMLIST x STMTLIST 
    STMTLIST = auto()   # [ASSIGNMENT + ASSERTION + IF + FOR]
    PARAMLIST = auto()  # [Name]
    ASSIGNMENT = auto() # Name x BVEXPR
    ASSERTION = auto()  # BOOLEXPR
    IF = auto()         # BoolExpr x STMTLIST [x STMTLIST]
    FOR = auto()        # Name x BVLit x BVLit x STMTLIST 
    BVEXPR = auto()     # BVOp2 BVEXPR BVEXPR + BVOp1 BVEXPR + Name + BVLit
    BOOLEXPR = auto()   # BoolOp1 BOOLEXPR + BoolOp2 BOOLEXPR BOOLEXPR + BVComp BOOLEXPR BOOLEXPR
    PHI = auto()        # Name x BoolExpr x BVEXPR x BVEXPR 

class Node(object):
    def __init__(self, kind, args):
        self.kind = kind
        self.args = args
    
class Name: 
    def __init__(self, Name):
        self.Name = Name

class BVLit:
    def __init__(self, BVLit):
        self.BVLit = BVLit

class BVOp1(Enum):
    BVNOT = auto()
    BVNEG = auto()

class BVOp2(Enum):
    BVADD = auto()
    BVMUL = auto()
    BVSUB = auto()
    BVUDIV = auto()
    BVAND = auto()
    BVOR  = auto()
    BVXOR = auto()
    BVUREM = auto()
    BVSHL = auto()
    BVLSHR = auto()

class BVComp(Enum):
    BVULT = auto()
    BVEQ  = auto()
    
class BoolOp1(Enum):
    NOT = auto()

class BoolOp2(Enum):
    AND = auto()
    OR  = auto()


Node(NT.FUNCTION, (Node(NT.PARAMLIST, [Name("a"), Name("b")]), 
                  Node(NT.STMTLIST, [Node(NT.ASSIGNMENT, (Name("a"), Name("b")))])))



# "function " PARAMLIST "{" STMTLIST "}"
# [ASSIGNMENT + ASSERTION + IF + FOR]
# [Name]
# Name  "=" BVEXPR
# "assert" BOOLEXPR
# "if (" BoolExpr ") {" STMTLIST "} [ else {" STMTLIST "}]"
# "for (" Name "from " BVLit "to" BVLit "{" STMTLIST "}"
# BVOp2 BVEXPR BVEXPR + BVOp1 BVEXPR + Name + BVLit
# BoolOp1 BOOLEXPR + BoolOp2 BOOLEXPR BOOLEXPR + BVComp BOOLEXPR BOOLEXPR
# Name "= phi(" BoolExpr "," BVEXPR "," BVEXPR ")"
