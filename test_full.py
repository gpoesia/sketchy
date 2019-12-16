from translate import *
from ssa import *
from parser import *
from constraints import *
from examples import *
import subprocess

for EXAMPLE in [LINEAR_COMBINATION, IF_TRUE, IF_FALSE, IF_TRUE_ELSE_NOTHING]:
    example_node = Parser.parse_string(EXAMPLE)
    ssa_node = ssa(example_node)
    # print_visitor = ASTPrinter()
    # walk(ssa_node, print_visitor)
    # print(print_visitor.str_repr[ssa_node])
    constraint_visitor = ConstraintVisitor()
    walk(ssa_node, constraint_visitor)
    constraints = constraint_visitor.outputConstraints(ssa_node)
    #print(constraints)
    with open('out.smt','w') as f:
        f.write(constraints)
    print(subprocess.check_output(['z3','-smt2','out.smt']))
