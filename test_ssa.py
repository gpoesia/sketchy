from ssa import *
from parser import *
from examples import *

EXAMPLE = Parser.parse_string(IF_TRUE_ELSE_NOTHING)

ssa_visitor = SSAVisitor()
walk(EXAMPLE, ssa_visitor)
print_node(ssa_visitor)
