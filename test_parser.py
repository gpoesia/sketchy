from parser import *
from examples import *

P1 = """
    function (x, y) {
        x := * ?1n y;
        z := + y y;
        assert == x z;
    }
"""

#print(Tokenizer.tokenize(P1))
#print(Parser.parse_string(P1))
#print_node(Parser.parse_string(P1))

for prog in EXAMPLES:
    print_node(Parser.parse_string(prog))
