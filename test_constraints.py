from translate import *
from ssa import *
from constraints import *
from examples import *
import subprocess

EXAMPLE = LINEAR_COMBINATION

ssa_node = ssa(EXAMPLE)

#print_visitor_2 = ASTPrinter()
#walk(ssa_node, print_visitor_2)
#print(print_visitor_2.str_repr[ssa_node])

constraint_visitor = ConstraintVisitor()
walk(ssa_node, constraint_visitor)
constraints = constraint_visitor.outputConstraints(ssa_node)
print(constraints)
