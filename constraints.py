from translate import *

class ConstraintVisitor(Visitor):
    def __init__(self):
        self.constraint_str = {}
        self.bool_hole_vars = set()
        self.bv_hole_vars = set()
    def createHoleConstraints(self):
        s = ""
        for v in self.bool_hole_vars:
            s += "(declare-const "+v+" Bool)\n"
        for v in self.bv_hole_vars:
            s += "(declare-const "+v+" (_ BitVec 32))\n"
        return s
    def outputConstraints(self, node):
        return ("(set-logic UFBV)\n" +
                self.createHoleConstraints() +
                self.constraint_str[node] +"\n"+
                "(check-sat)\n" +
                "(get-model)")
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
                print('statements', node.args)
                self.constraint_str[node] = (
                    "\n"+"\n".join([self.constraint_str[x] for x in node.args])
                        + ')'*len(list(filter(lambda x:x.kind == NT.ASSIGNMENT, node.args)))
                    )
            elif (node.kind == NT.ASSIGNMENT):
                print(node.kind, node.args[0].name, node.args)
                self.constraint_str[node] = (
                        "(let (("+
                        node.args[0].name+" "+
                        self.constraint_str[node.args[1]]+"))")
            elif (node.kind == NT.ASSERTION):
                self.constraint_str[node] = self.constraint_str[node.args[0]]
            elif (node.kind == NT.BVEXPR):
                if (isinstance(node.args[0], Name)):
                    self.constraint_str[node] = node.args[0].name
                elif (isinstance(node.args[0], BVLit)):
                    self.constraint_str[node] = node.args[0].bvlit
                elif isinstance(node.args[0], BVOp1):
                    operation_symbol = node.args[0].name.lower()
                    self.constraint_str[node] = (
                        "("+operation_symbol + " " +
                        self.constraint_str[node.args[1]]+")")
                elif isinstance(node.args[0], BVOp2):
                    operation_symbol = node.args[0].name.lower()
                    self.constraint_str[node] = (
                        "(" + operation_symbol + " " +
                        self.constraint_str[node.args[1]] + " " +
                        self.constraint_str[node.args[2]] + ")")
                elif isinstance(node.args[0], Node):
                    self.constraint_str[node] = self.constraint_str[node.args[0]]
            elif (node.kind == NT.BOOLEXPR ):
                if isinstance(node.args[0], BoolOp1):
                    operation_symbol = node.args[0].name.lower()
                    self.constraint_str[node] = (
                        "("+operation_symbol + " " +
                        self.constraint_str[node.args[1]]+")")
                elif isinstance(node.args[0], BoolOp2):
                    operation_symbol = node.args[0].name.lower()
                    self.constraint_str[node] = (
                        "("+operation_symbol + " " +
                        self.constraint_str[node.args[1]] + " " +
                        self.constraint_str[node.args[2]]+")")
                elif isinstance(node.args[0], BVComp):
                    operation_symbol = '=' if node.args[0] == BVComp.BVEQ else node.args[0].name.lower()
                    self.constraint_str[node] = (
                        "("+operation_symbol + " " +
                        self.constraint_str[node.args[1]] + " " +
                        self.constraint_str[node.args[2]]+")")
                elif isinstance(node.args[0], Node):
                    self.constraint_str[node] = self.constraint_str[node.args[0]]
            elif (node.kind == NT.PHI):
                self.constraint_str[node] = (
                    "(ite "+
                    self.constraint_str[node.args[0]]+" "+
                    node.args[1].name+" "+
                    node.args[2].name+")")
            elif (node.kind == NT.BVHOLE):
                hole_name = "hole_"+str(node.args[0])
                self.constraint_str[node] = hole_name
                self.bv_hole_vars.add(hole_name)
            elif (node.kind == NT.BOOLHOLE):
                hole_name = "hole_"+str(node.args[0])
                self.constraint_str[node] = hole_name
                self.bool_hole_vars.add(hole_name)
            else:
                print(str(node), node.kind, node.args)
                self.constraint_str[node] = str(node)
