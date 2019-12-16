from translate import *
from printer import *
from ssa import *
from constraints import *
from examples import *
import subprocess

for example in [LINEAR_COMBINATION, IF_TRUE,IF_FALSE, IF_TRUE_ELSE_NOTHING]:
    print_visitor_1 = ASTPrinter()
    walk(example, print_visitor_1)
    print(print_visitor_1.str_repr[example]+"\n")

    ssa_visitor = SSAVisitor()
    walk(example, ssa_visitor)
    ssa_node = ssa_visitor.ssa_node[example]

    print_visitor_2 = ASTPrinter()
    walk(ssa_node, print_visitor_2)
    print(print_visitor_2.str_repr[ssa_node]+"\n")

    constraint_visitor = ConstraintVisitor()
    walk(ssa_node, constraint_visitor)
    constraints = constraint_visitor.outputConstraints(ssa_node)
    print(constraints)

    with open('out.smt','w') as f:
        f.write(constraints)
    print(subprocess.check_output(['z3','-smt2','out.smt']))
