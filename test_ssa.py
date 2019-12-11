from ssa import *
from examples import *

EXAMPLE = IF_TRUE

ssa_visitor = SSAVisitor()
walk(EXAMPLE, ssa_visitor)
p = ASTPrinter()
walk(ssa_visitor.ssa_node[EXAMPLE], p)
print(p.str_repr[ssa_visitor.ssa_node[EXAMPLE]])
