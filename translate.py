from enum import Enum, auto

class NT(Enum):
    FUNCTION = auto()   # [PARAMLIST, STMTLIST]
    STMTLIST = auto()   # [(ASSIGNMENT + ASSERTION + IF + FOR)+]
    PARAMLIST = auto()  # [(Name)+]
    ASSIGNMENT = auto() # [Name, BVEXPR]
    ASSERTION = auto()  # [BOOLEXPR]
    IF = auto()         # [BoolExpr, STMTLIST, STMTLIST?]
    FOR = auto()        # [Name, BVLit, BVLit, STMTLIST]
    BVEXPR = auto()     # [BVOp2, BVEXPR, BVEXPR] + [BVOp1, BVEXPR] + [Name] + [BVLit]
    BOOLEXPR = auto()   # [BoolOp1, BOOLEXPR] + [BoolOp2, BOOLEXPR, BOOLEXPR] + [BVComp, BOOLEXPR, BOOLEXPR]
    PHI = auto()        # [Name, BoolExpr, BVEXPR, BVEXPR]

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

class ASTPrinter(Visitor):
    def __init__(self):
        self.str_repr = {}
    def visit(self, node, is_leaving):
        if (isinstance(node, Node) and is_leaving):
            if (node.kind == NT.FUNCTION ):
                self.str_repr[node] = (
                        "function (" + 
                        self.str_repr[node.args[0]] +
                        ") {" +
                        self.str_repr[node.args[1]] +
                        "}")
            if (node.kind == NT.STMTLIST ):
                self.str_repr[node] = "; ".join(
                        [self.str_repr[a] for a in node.args] + [""])
            if (node.kind == NT.PARAMLIST):
                self.str_repr[node] = ", ".join(
                        self.str_repr[a] for a in node.args)
            if (node.kind == NT.ASSIGNMENT):
                self.str_repr[node] = (
                        self.str_repr[node.args[0]] + 
                        " = " +
                        self.str_repr[node.args[1]])
            if (node.kind == NT.ASSERTION):
                self.str_repr[node] = "assert " + self.str_repr[node.args[0]]
            if (node.kind == NT.IF       ):
                self.str_repr[node] = (
                        "if (" + 
                        self.str_repr[node.args[0]] +
                        ") {" +
                        self.str_repr[node.args[1]] +
                        " }" +
                        ("" if len(node.args) == 2
                            else (
                                " else { " + 
                                self.str_repr[node.args[2]] + 
                                "}"
                                )))
            if (node.kind == NT.FOR      ):
                self.str_repr[node] = (
                        "for (" + 
                        self.str_repr[node.args[0]] +
                        " from " +
                        self.str_repr[node.args[1]] +
                        " to " +
                        self.str_repr[node.args[2]] +
                        ") { " +
                        self.str_repr[node.args[3]] +
                        " }")
            if (node.kind == NT.BVEXPR   ):
                if (isinstance(node.args[0], Name) or 
                        isinstance(node.args[0], BVLit)):
                    self.str_repr[node] = self.str_repr[node.args[0]]
                elif isinstance(node.args[0], BVOp1):
                    self.str_repr[node] = (
                        self.str_repr[node.args[0]] + 
                        " " +
                        self.str_repr[node.args[1]])
                elif isinstance(node.args[0], BVOp2):
                    self.str_repr[node] = (
                        self.str_repr[node.args[0]] + 
                        " " +
                        self.str_repr[node.args[1]] + 
                        " " +
                        self.str_repr[node.args[2]])
            if (node.kind == NT.BOOLEXPR ):
                if isinstance(node.args[0], BoolOp1):
                    self.str_repr[node] = (
                        self.str_repr[node.args[0]] + 
                        " " +
                        self.str_repr[node.args[1]])
                else:
                    self.str_repr[node] = (
                        self.str_repr[node.args[0]] + 
                        " " +
                        self.str_repr[node.args[1]] + 
                        " " +
                        self.str_repr[node.args[2]])
            if (node.kind == NT.PHI      ):
                self.str_repr[node] = (
                        self.str_repr[node.args[0]] +
                        " = phi(" +
                        self.str_repr[node.args[1]] +
                        ", " +
                        self.str_repr[node.args[2]] +
                        ")")
        elif isinstance(node, Name):
            self.str_repr[node] = node.name
        elif isinstance(node, BVLit):
            self.str_repr[node] = str(node.bvlit)
        else:
            self.str_repr[node] = str(node)

class ASTConcretizer(Visitor):
    def __init__(self, name, val):
        self.modified_node = {}
        self.name = name
        self.val = val
    def visit(self, node, is_leaving):
        if (isinstance(node, Node) and is_leaving):
            self.modified_node[node] = Node(node.kind, [self.modified_node[x] for x in node.args])
        elif (isinstance(node, Name) and node.name == self.name):
            self.modified_node[node] = self.val
        else:
            self.modified_node[node] = node

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

a = Node(NT.FUNCTION, (Node(NT.PARAMLIST, [Name("a"), Name("b")]), 
                  Node(NT.STMTLIST, [
                      Node(NT.ASSIGNMENT, (Name("a"), 
                          Node(NT.BVEXPR, [Name("b")]))),
                      Node(NT.ASSIGNMENT, [
                          Name("b"), 
                          Node(NT.BVEXPR, [
                              BVOp2.BVADD,
                              Node(NT.BVEXPR, [Name("b")]),
                              Node(NT.BVEXPR, [Name("c")])
                              ])])])))


# test 
#p = ASTPrinter()
#walk(a, p)
#print(p.str_repr[a])
#
#conc = ASTConcretizer("c", BVLit(3))
#walk(a, conc)
#n = conc.modified_node[a]
#
#p2 = ASTPrinter()
#walk(n, p2)
#print(p2.str_repr[n])




b = Node(NT.FUNCTION, [Node(NT.PARAMLIST, [Name("a")]),
                       Node(NT.STMTLIST, [
                                Node(NT.ASSIGNMENT, [Name("b"), BVLit(10)]),
                                Node(NT.FOR, 
                                    [Name("c"), BVLit(1), BVLit(4), 
                                        Node(NT.STMTLIST, 
                                            [Node(NT.ASSIGNMENT, 
                                             [Name("b"), Node(NT.BVEXPR, 
                                                            [Name("c")])])])])
                           ])])

p = ASTPrinter()
walk(b, p)
print(p.str_repr[b])

unr = ASTUnroller()
walk(b, unr)
walk(unr.unrolled_node[b], p)
print(p.str_repr[unr.unrolled_node[b]])



