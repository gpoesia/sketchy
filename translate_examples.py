from translate import *

a = Node(NT.FUNCTION, (Node(NT.PARAMLIST, [Name("a"), Name("b")]),
                  Node(NT.STMTLIST, [
                      Node(NT.ASSIGNMENT, (Name("a"),
                          Node(NT.BVEXPR, [Node(NT.BVHOLE, [1])]))),
                      Node(NT.ASSIGNMENT, [
                          Name("b"),
                          Node(NT.BVEXPR, [
                              BVOp2.BVADD,
                              Node(NT.BVEXPR, [Name("b")]),
                              Node(NT.BVEXPR, [Name("c")])
                              ])])])))



# test
p = ASTPrinter()
walk(a, p)
print(p.str_repr[a])

conc = ASTConcretizer("c", BVLit(3))
walk(a, conc)
n = conc.modified_node[a]

p2 = ASTPrinter()
walk(n, p2)
print(p2.str_repr[n])




b = Node(NT.FUNCTION, [Node(NT.PARAMLIST, [Name("a")]),
                       Node(NT.STMTLIST, [
                                Node(NT.ASSIGNMENT, [Name("b"), BVLit(10)]),
                                Node(NT.FOR,
                                    [Name("c"), BVLit(1), BVLit(4),
                                        Node(NT.STMTLIST,
                                            [Node(NT.ASSIGNMENT,
                                             [Name("b"), Node(NT.BVEXPR,
                                                            [Name("c")])])])])
                           ])])

p = ASTPrinter()
walk(b, p)
print(p.str_repr[b])

unr = ASTUnroller()
walk(b, unr)
walk(unr.unrolled_node[b], p)
print(p.str_repr[unr.unrolled_node[b]])
