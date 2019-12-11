from translate import *
from ssa import *
from constraints import *

ssa_visitor = SSAVisitor()
walk(LINEAR_COMBINATION, ssa_visitor)
linear_combo_ssa_node = ssa_visitor.ssa_node[LINEAR_COMBINATION]

print_visitor = ASTPrinter()
walk(linear_combo_ssa_node, print_visitor)
print(print_visitor.str_repr[linear_combo_ssa_node])

constraint_visitor = ConstraintVisitor()
walk(linear_combo_ssa_node, constraint_visitor)
print(constraint_visitor.constraint_str[LINEAR_COMBINATION])
