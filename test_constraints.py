from translate import *
from ssa import *
from constraints import *
import subprocess

print_visitor_1 = ASTPrinter()
walk(LINEAR_COMBINATION, print_visitor_1)
print(print_visitor_1.str_repr[LINEAR_COMBINATION]+"\n")

ssa_visitor = SSAVisitor()
walk(LINEAR_COMBINATION, ssa_visitor)
linear_combo_ssa_node = ssa_visitor.ssa_node[LINEAR_COMBINATION]

print_visitor_2 = ASTPrinter()
walk(linear_combo_ssa_node, print_visitor_2)
print(print_visitor_2.str_repr[linear_combo_ssa_node]+"\n")

constraint_visitor = ConstraintVisitor()
walk(linear_combo_ssa_node, constraint_visitor)
constraints = constraint_visitor.outputConstraints(linear_combo_ssa_node)

with open('out.smt','w') as f:
    f.write(constraints)
print(subprocess.check_output(['z3','-smt2','out.smt']))
