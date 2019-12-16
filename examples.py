from translate import *
from ssa import *
from constraints import *

LINEAR_COMBINATION = Node(NT.FUNCTION, [
    Node(NT.PARAMLIST, [Name("x"), Name("y")]),
    Node(NT.STMTLIST, [
        Node(NT.ASSIGNMENT, [Name("x_old"), Node(NT.BVEXPR, [Name("x")])]),
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
                Node(NT.BVEXPR, [Name("x_old")]),
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

IF_TRUE = Node(NT.FUNCTION, [
    Node(NT.PARAMLIST, [Name("x"), Name("y")]),
    Node(NT.STMTLIST, [
        Node(NT.IF, [
            Node(NT.BOOLEXPR, [Node(NT.BOOLHOLE, [0])]),
            Node(NT.STMTLIST, [
                Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [Name("y")])]),
            ]),
        ]),
        Node(NT.ASSERTION, [
            Node(NT.BOOLEXPR, [
                BVComp.BVEQ,
                Node(NT.BVEXPR, [Name("x")]),
                Node(NT.BVEXPR, [Name("y")]),
                ]),
        ]),
    ]),
])

IF_TRUE_ELSE_NOTHING = Node(NT.FUNCTION, [
    Node(NT.PARAMLIST, [Name("x"), Name("y")]),
    Node(NT.STMTLIST, [
        Node(NT.IF, [
            Node(NT.BOOLEXPR, [Node(NT.BOOLHOLE, [0])]),
            Node(NT.STMTLIST, [
                Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [Name("y")])]),
            ]),
            Node(NT.STMTLIST, [
                Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [Name("x")])]),
            ]),
        ]),
        Node(NT.ASSERTION, [
            Node(NT.BOOLEXPR, [
                BVComp.BVEQ,
                Node(NT.BVEXPR, [Name("x")]),
                Node(NT.BVEXPR, [Name("y")]),
                ]),
        ]),
    ]),
])

IF_FALSE = Node(NT.FUNCTION, [
    Node(NT.PARAMLIST, [Name("x"), Name("y")]),
    Node(NT.STMTLIST, [
        Node(NT.ASSIGNMENT, [Name("x_old"), Node(NT.BVEXPR, [Name("x")])]),
        Node(NT.IF, [
            Node(NT.BOOLEXPR, [Node(NT.BOOLHOLE, [0])]),
            Node(NT.STMTLIST, [
                Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [Name("y")])]),
            ]),
        ]),
        Node(NT.ASSERTION, [
            Node(NT.BOOLEXPR, [
                BVComp.BVEQ,
                Node(NT.BVEXPR, [Name("x")]),
                Node(NT.BVEXPR, [Name("x_old")]),
                ]),
        ]),
    ]),
])
