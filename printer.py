from translate import *

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
            if (node.kind == NT.BVEXPR):
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
                elif isinstance(node.args[0], Node) and node.args[0].kind == NT.BVHOLE:
                    self.str_repr[node] = self.str_repr[node.args[0]]
            if (node.kind == NT.BOOLEXPR ):
                if isinstance(node.args[0], BoolOp1):
                    self.str_repr[node] = (
                        self.str_repr[node.args[0]] +
                        " " +
                        self.str_repr[node.args[1]])
                elif isinstance(node.args[0], Node) and node.args[0].kind == NT.BOOLHOLE:
                    self.str_repr[node] = self.str_repr[node.args[0]]
                else:
                    self.str_repr[node] = (
                        self.str_repr[node.args[0]] +
                        " " +
                        self.str_repr[node.args[1]] +
                        " " +
                        self.str_repr[node.args[2]])
            if (node.kind == NT.PHI      ):
                self.str_repr[node] = (
                        "phi(" +
                        self.str_repr[node.args[0]] +
                        ", " +
                        self.str_repr[node.args[1]] +
                        ", " +
                        self.str_repr[node.args[2]] +
                        ")" )
            if (node.kind == NT.BVHOLE ):
                self.str_repr[node] = "?"+str(node.args[0])+"?"
            if (node.kind == NT.BOOLHOLE ):
                self.str_repr[node] = "?"+str(node.args[0])+"?"
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
