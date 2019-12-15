from enum import Enum, auto

class NT(Enum):
    FUNCTION = auto()   # [PARAMLIST, STMTLIST]
    STMTLIST = auto()   # [(ASSIGNMENT + ASSERTION + IF + FOR)+]
    PARAMLIST = auto()  # [(Name)+]
    ASSIGNMENT = auto() # [Name, BVEXPR]
    ASSERTION = auto()  # [BOOLEXPR]
    IF = auto()         # [BoolExpr, STMTLIST, STMTLIST?]
    FOR = auto()        # [Name, BVLit, BVLit, STMTLIST]
    BVEXPR = auto()     # [BVOp2, BVEXPR, BVEXPR] + [BVOp1, BVEXPR] + [Name] + [BVLit] + [BVHOLE] + [PHI]
    BOOLEXPR = auto()   # [BoolOp1, BOOLEXPR] + [BoolOp2, BOOLEXPR, BOOLEXPR] + [BVComp, BOOLEXPR, BOOLEXPR] + [BOOLHOLE] + [PHI]
    BVHOLE = auto()     # [Num]
    BOOLHOLE = auto()   # [Num]
    PHI = auto()        # [BoolExpr, Name, Name]

class Node(object):
    def __init__(self, kind, args):
        self.kind = kind
        self.args = args

class Name:
    def __init__(self, name):
        self.name = name

class BVLit:
    def __init__(self, bvlit):
        self.bvlit = bvlit

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


class Visitor:
    def visit(self, Node, is_leaving):
        raise NotImplemented


class ASTUnroller(Visitor):
    def __init__(self):
        self.unrolled_node = {}
    def visit(self, node, is_leaving):
        if (isinstance(node, Node) and is_leaving):
            if (node.kind != NT.FOR):
                self.unrolled_node[node] = Node(node.kind, [self.unrolled_node[x] for x in node.args])
            else:
                var_name = node.args[0]
                lower = node.args[1]
                upper = node.args[2]
                for_body = node.args[3]
                self.unrolled_node[node] = Node(NT.STMTLIST, [])
                for val in range(lower.bvlit, upper.bvlit):
                    conc = ASTConcretizer(var_name.name, BVLit(val))
                    walk(self.unrolled_node[for_body], conc)
                    self.unrolled_node[node].args.append(conc.modified_node[self.unrolled_node[for_body]])
        else:
            self.unrolled_node[node] = node


def walk(ast, v):
    v.visit(ast, False)
    if isinstance(ast, Node):
        for ch in ast.args:
            walk(ch, v)
        v.visit(ast, True)
