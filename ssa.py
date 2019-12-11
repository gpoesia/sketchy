# AST transform that puts programs in SSA form

import collections
from translate import *
from examples import *

class SSAVisitor(Visitor):
    def __init__(self):
        # Number of static assignments to that variable seen so far.
        self.definition_counter = collections.defaultdict(int)
        # Name of the live definition of each variable before a node.
        self.prev_definition = collections.defaultdict(dict)
        # Name of the last definition of each variable in a node.
        self.last_definition = collections.defaultdict(dict)
        # Node in SSA form.
        self.ssa_node = {}

    def format_name(self, name, definition_id):
        return "{}_{}".format(name, definition_id)

    def visit(self, node, is_leaving):
        if isinstance(node, Node) and not is_leaving:
            if node.kind == NT.IF:
                self.prev_definition[node] = dict(self.definition_counter)
                self.prev_definition[node.args[1]] = self.prev_definition[node]

                if len(node.args) == 3:
                    self.prev_definition[node.args[2]] = self.prev_definition[node]
            # The if branches have their prev_definition set by the parent,
            # so they don't redefine it here.
            elif node not in self.prev_definition:
                self.prev_definition[node] = dict(self.definition_counter)
        elif isinstance(node, Node) and is_leaving:
            if node.kind == NT.IF:
                pass
            elif node.kind == NT.ASSIGNMENT:
                new_name = self.format_name(
                            node.args[0].name,
                            self.definition_counter[node.args[0].name])

                self.ssa_node[node] = Node(NT.ASSIGNMENT, [
                    Name(new_name),
                    self.ssa_node[node.args[1]]
                    ])

                self.last_definition[node.args[0].name] = new_name
                self.definition_counter[node.args[0].name] += 1
            elif node.kind == NT.PARAMLIST:
                names = []
                for name in node.args:
                    self.last_definition[name.name] = self.format_name(name.name, 0)
                    self.definition_counter[name.name] = 1
                    names.append(Name(self.last_definition[name.name]))
                self.ssa_node[node] = Node(NT.PARAMLIST, names)
            else:
                children = []

                for a in node.args:
                    children.append(self.ssa_node[a])
                    for k, v in self.last_definition[a].items():
                        self.last_definition[node][k] = v

                self.ssa_node[node] = Node(node.kind, children)
        elif isinstance(node, Name):
            self.ssa_node[node] = Name(self.last_definition[node.name])
        else:
            self.ssa_node[node] = node
