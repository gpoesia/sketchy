from translate import *
from ssa import *
from constraints import *

LINEAR_COMBINATION = """
    function (x, y) {
        x_old := x;
        x := + x y;
        x := + x y;
        x := + x y;
        z := + (* x_old ?0n) (((* y ?1n)));
        assert == x z;
    }
"""

IF_TRUE = """
    function (x, y) {
        if (?0b) {x := y;  };
        assert == x y;
    }
"""

IF_FALSE = """
    function (x, y) {
        x_old := x;
        if (?0b) {x := y;  };
        assert == x x_old;
    }
"""

IF_TRUE_ELSE_NOTHING = """
    function (x, y) {
        if (?0b) {x := y;  } else { x := x; };
        assert == x y;
    }
"""

POPCOUNT = """
    function (x) {
        c_naive := 0;
        for (i from 0 to 32) {
            if (not == 0 (& (<< 1 i) x)) {
                c_naive := + 1 c_naive;
            };
        };
        c := x;
        c := + (& c ?1n) (& (>> c 1) ?1n);
        c := + (& c ?2n) (& (>> c 2) ?2n);
        c := + (& c ?3n) (& (>> c 4) ?3n);
        c := + (& c ?4n) (& (>> c 8) ?4n);
        c := + (& c ?5n) (& (>> c 16) ?5n);
        assert == c c_naive;
    }
"""

def gen_popcount2(bw):
    p = """
    function (x) {{
        c_naive := 0;
        for (i from 0 to {}) {{
            c_naive := + c_naive (>> (& x (<< 1 i)) i);
        }};
        c := x;
        """.format(bw)
    i = 0
    while 2**i < bw:
        p += """
        c := + (& c ?{0}n) (& (>> c {1}) ?{0}n);
        """.format(i, 2**i)
        i += 1

    p += """
        assert == c c_naive;
    }"""
    return p

def gen_reverse(bw):
    p = """
    function (x) {{
        r_naive := 0;
        for (i from 0 to {0}) {{
            s := + 1 * 2 i;
            r_naive := | r_naive (>> (& x (<< 1 (+ {0} i))) s);
            r_naive := | r_naive (<< (& x (<< 1 (- {1} i))) s);
        }};
        r := x;
    """.format(bw // 2, bw // 2 - 1)

    i = 0
    while 2**i < bw:
        p += """
        r := | (>> (& r ?{0}n) {1}) (<< (& r ?{2}n) {1});
        """.format(2*i, 2**i, 2*i + 1)
        i += 1
    p += """
        assert == r r_naive;
    }"""
    return p

POPCOUNT2 = gen_popcount2(BITVECTOR_SIZE)
REVERSE = gen_reverse(BITVECTOR_SIZE)

EXAMPLES = [REVERSE, POPCOUNT2, LINEAR_COMBINATION, IF_TRUE, IF_FALSE, IF_TRUE_ELSE_NOTHING, POPCOUNT]

#LINEAR_COMBINATION = Node(NT.FUNCTION, [
#    Node(NT.PARAMLIST, [Name("x"), Name("y")]),
#    Node(NT.STMTLIST, [
#        Node(NT.ASSIGNMENT, [Name("x_old"), Node(NT.BVEXPR, [Name("x")])]),
#        Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [
#            BVOp2.BVADD,
#            Node(NT.BVEXPR, [Name("x")]),
#            Node(NT.BVEXPR, [Name("y")]),
#            ])]),
#        Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [
#            BVOp2.BVADD,
#            Node(NT.BVEXPR, [Name("x")]),
#            Node(NT.BVEXPR, [Name("y")]),
#            ])]),
#        Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [
#            BVOp2.BVADD,
#            Node(NT.BVEXPR, [Name("x")]),
#            Node(NT.BVEXPR, [Name("y")]),
#            ])]),
#
#        Node(NT.ASSIGNMENT, [Name("z"), Node(NT.BVEXPR, [
#            BVOp2.BVADD,
#            Node(NT.BVEXPR, [
#                BVOp2.BVMUL,
#                Node(NT.BVEXPR, [Name("x_old")]),
#                Node(NT.BVEXPR, [Node(NT.BVHOLE, [0])])
#            ]),
#            Node(NT.BVEXPR, [
#                BVOp2.BVMUL,
#                Node(NT.BVEXPR, [Name("y")]),
#                Node(NT.BVEXPR, [Node(NT.BVHOLE, [1])])
#            ]),
#        ])]),
#        Node(NT.ASSERTION, [
#            Node(NT.BOOLEXPR, [
#                BVComp.BVEQ,
#                Node(NT.BVEXPR, [Name("x")]),
#                Node(NT.BVEXPR, [Name("z")]),
#                ]),
#        ]),
#    ])
#])
#
#IF_TRUE = Node(NT.FUNCTION, [
#    Node(NT.PARAMLIST, [Name("x"), Name("y")]),
#    Node(NT.STMTLIST, [
#        Node(NT.IF, [
#            Node(NT.BOOLEXPR, [Node(NT.BOOLHOLE, [0])]),
#            Node(NT.STMTLIST, [
#                Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [Name("y")])]),
#            ]),
#        ]),
#        Node(NT.ASSERTION, [
#            Node(NT.BOOLEXPR, [
#                BVComp.BVEQ,
#                Node(NT.BVEXPR, [Name("x")]),
#                Node(NT.BVEXPR, [Name("y")]),
#                ]),
#        ]),
#    ]),
#])
#
#IF_TRUE_ELSE_NOTHING = Node(NT.FUNCTION, [
#    Node(NT.PARAMLIST, [Name("x"), Name("y")]),
#    Node(NT.STMTLIST, [
#        Node(NT.IF, [
#            Node(NT.BOOLEXPR, [Node(NT.BOOLHOLE, [0])]),
#            Node(NT.STMTLIST, [
#                Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [Name("y")])]),
#            ]),
#            Node(NT.STMTLIST, [
#                Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [Name("x")])]),
#            ]),
#        ]),
#        Node(NT.ASSERTION, [
#            Node(NT.BOOLEXPR, [
#                BVComp.BVEQ,
#                Node(NT.BVEXPR, [Name("x")]),
#                Node(NT.BVEXPR, [Name("y")]),
#                ]),
#        ]),
#    ]),
#])
#
#IF_FALSE = Node(NT.FUNCTION, [
#    Node(NT.PARAMLIST, [Name("x"), Name("y")]),
#    Node(NT.STMTLIST, [
#        Node(NT.ASSIGNMENT, [Name("x_old"), Node(NT.BVEXPR, [Name("x")])]),
#        Node(NT.IF, [
#            Node(NT.BOOLEXPR, [Node(NT.BOOLHOLE, [0])]),
#            Node(NT.STMTLIST, [
#                Node(NT.ASSIGNMENT, [Name("x"), Node(NT.BVEXPR, [Name("y")])]),
#            ]),
#        ]),
#        Node(NT.ASSERTION, [
#            Node(NT.BOOLEXPR, [
#                BVComp.BVEQ,
#                Node(NT.BVEXPR, [Name("x")]),
#                Node(NT.BVEXPR, [Name("x_old")]),
#                ]),
#        ]),
#    ]),
#])
