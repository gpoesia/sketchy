from translate import *
from ssa import *
from constraints import *
from examples import *
import subprocess

for EXAMPLE in [LINEAR_COMBINATION, IF_TRUE, IF_FALSE, IF_TRUE_ELSE_NOTHING]:
    ssa_node = ssa(EXAMPLE)
    # print_visitor_2 = ASTPrinter()
    # walk(ssa_node, print_visitor_2)
    constraint_visitor = ConstraintVisitor()
    walk(ssa_node, constraint_visitor)
    constraints = constraint_visitor.outputConstraints(ssa_node)
    #print(constraints)
    with open('out.smt','w') as f:
        f.write(constraints)
    print(subprocess.check_output(['z3','-smt2','out.smt']))
