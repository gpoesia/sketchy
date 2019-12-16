from ssa import *
from parser import *
from examples import *

for prog in EXAMPLES:
    example_node = Parser.parse_string(prog)
    ssa_visitor = SSAVisitor()
    walk(example_node, ssa_visitor)
    print_node(ssa_visitor.ssa_node[example_node])
