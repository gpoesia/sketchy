from translate import *

class ConstraintVisitor(Visitor):
    def __init__(self):
        self.constraint_str = {}
        self.hole_vars = {}
    def createHoleConstraints(self, node):
        s = ""
        for v in self.hole_vars[node]:
            s.append("(declare-const hole_"+str(v.args[0])+" (_ BitVec 32))\n")
        return s
    def visit(self, node, is_leaving):
        if (isinstance(node, Node) and is_leaving):
            if (node.kind == NT.FUNCTION):
                self.constraint_str[node] = (
                        "(assert (forall ("+
                        self.constraint_str[node.args[0]]+")" +
                        self.constraint_str[node.args[1]]+"))")
            elif (node.kind == NT.PARAMLIST):
                self.constraint_str[node] = "\n".join(["("+x.name+" (_ BitVec 32))" for x in node.args])
            elif (node.kind == NT.STMTLIST): #STMTLIST = [(ASSIGNMENT + ASSERTION)]
                self.constraint_str[node] = "\n".join(["("+self.constraint_str[x]+")" for x in node.args])
            elif (node.kind == NT.ASSIGNMENT):
                self.constraint_str[node] = (
                        "let (("+
                        node.args[0].name+" ("+
                        self.constraint_str[node.args[1]]+")))")
            elif (node.kind == NT.ASSERTION):
                self.constraint_str[node] = self.constraint_str[node.args[0]]
            elif (node.kind == NT.BVEXPR):
                if (isinstance(node.args[0], Name) or
                        isinstance(node.args[0], Name)):
                    self.constraint_str[node] = node.args[0].name
                elif (isinstance(node.args[0], Name) or
                        isinstance(node.args[0], BVLit)):
                    self.constraint_str[node] = node.args[0].bvlit
                elif isinstance(node.args[0], BVOp1):
                    operation_symbol = node.args[0].name.lower()
                    self.constraint_str[node] = (
                        operation_symbol + " " +
                        self.constraint_str[node.args[1]])
                elif isinstance(node.args[0], BVOp2):
                    operation_symbol = node.args[0].name.lower()
                    self.constraint_str[node] = (
                        operation_symbol + " " +
                        self.constraint_str[node.args[1]] + " " +
                        self.constraint_str[node.args[2]])

                elif isinstance(node.args[0], Node) and node.args[0].kind == NT.BVHOLE:
                    self.constraint_str[node] = "hole_"+self.constraint_str[node.args[0]]
            elif (node.kind == NT.BOOLEXPR ):
                if isinstance(node.args[0], BoolOp1):
                    operation_symbol = node.args[0].name.lower()
                    self.constraint_str[node] = (
                        operation_symbol + " " +
                        self.constraint_str[node.args[1]])
                elif isinstance(node.args[0], BoolOp2):
                    operation_symbol = node.args[0].name.lower()
                    self.constraint_str[node] = (
                        operation_symbol + " " +
                        self.constraint_str[node.args[1]] + " " +
                        self.constraint_str[node.args[2]])
                elif isinstance(node.args[0], Node) and node.args[0].kind == NT.BOOLHOLE:
                    self.constraint_str[node] = "hole_"+self.constraint_str[node.args[0]]
            elif (node.kind == NT.PHI):
                self.constraint_str[node] = (
                    "ite "+
                    self.constraint_str[node.args[0]]+" "+
                    self.constraint_str[node.args[1]]+" "+
                    self.constraint_str[node.args[2]])
            elif (node.kind == NT.BVHOLE):
                self.constraint_str[node] = "hole_"+str(node.args[0])
            elif (node.kind == NT.BOOLHOLE):
                self.constraint_str[node] = "hole_"+str(node.args[1])
            else:
                print(str(node), node.kind, node.args)
                self.constraint_str[node] = str(node)
