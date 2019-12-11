from translate import *
from ssa import *
from constraints import *

LINEAR_COMBINATION = Node(NT.FUNCTION, [
    Node(NT.PARAMLIST, [Name("x"), Name("y")]),
    Node(NT.STMTLIST, [
        Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [
            BVOp2.BVADD,
            Node(NT.BVEXPR, [Name("x")]),
            Node(NT.BVEXPR, [Name("y")]),
            ])]),
        Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [
            BVOp2.BVADD,
            Node(NT.BVEXPR, [Name("x")]),
            Node(NT.BVEXPR, [Name("y")]),
            ])]),
        Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [
            BVOp2.BVADD,
            Node(NT.BVEXPR, [Name("x")]),
            Node(NT.BVEXPR, [Name("y")]),
            ])]),

        Node(NT.ASSIGNMENT, [Name("z"), Node(NT.BVEXPR, [
            BVOp2.BVADD,
            Node(NT.BVEXPR, [
                BVOp2.BVMUL,
                Node(NT.BVEXPR, [Name("x")]),
                Node(NT.BVEXPR, [Node(NT.BVHOLE, [0])])
            ]),
            Node(NT.BVEXPR, [
                BVOp2.BVMUL,
                Node(NT.BVEXPR, [Name("y")]),
                Node(NT.BVEXPR, [Node(NT.BVHOLE, [1])])
            ]),
        ])]),
        Node(NT.ASSERTION, [
            Node(NT.BOOLEXPR, [
                BVComp.BVEQ,
                Node(NT.BVEXPR, [Name("x")]),
                Node(NT.BVEXPR, [Name("z")]),
                ]),
        ]),
    ])
])


ssa_visitor = SSAVisitor()
walk(LINEAR_COMBINATION, ssa_visitor)
linear_combo_ssa_node = ssa_visitor.ssa_node[LINEAR_COMBINATION]

print_visitor = ASTPrinter()
walk(linear_combo_ssa_node, print_visitor)
print(print_visitor.str_repr[linear_combo_ssa_node])

constraint_visitor = ConstraintVisitor()
walk(linear_combo_ssa_node, constraint_visitor)
print(constraint_visitor.constraint_str[LINEAR_COMBINATION])
