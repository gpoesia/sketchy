from translate import *
from printer import *
from ssa import *
from constraints import *
from examples import *
import subprocess

EXAMPLE = IF_TRUE

linear_combo_ssa_node = ssa(EXAMPLE)

# print_visitor_2 = ASTPrinter()
# walk(linear_combo_ssa_node, print_visitor_2)

constraint_visitor = ConstraintVisitor()
walk(linear_combo_ssa_node, constraint_visitor)
constraints = constraint_visitor.outputConstraints(linear_combo_ssa_node)
print(constraints)

#with open('out.smt','w') as f:
#    f.write(constraints)
#print(subprocess.check_output(['z3','-smt2','out.smt']))
