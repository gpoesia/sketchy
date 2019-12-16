from translate import *
from ssa import *
from parser import *
from constraints import *
from examples import *
import subprocess

for EXAMPLE in [POPCOUNT]:  #[LINEAR_COMBINATION, IF_TRUE, IF_FALSE, IF_TRUE_ELSE_NOTHING]:
    example_node = Parser.parse_string(EXAMPLE)
    ssa_node = ssa(example_node)
    print_node(ssa_node)
    constraint_visitor = ConstraintVisitor()
    walk(ssa_node, constraint_visitor)
    constraints = constraint_visitor.outputConstraints(ssa_node)
    #print(constraints)
    with open('out.smt','w') as f:
        f.write(constraints)
    print(subprocess.check_output(['z3','-smt2','out.smt']))
