from parser import *

P1 = """
    function (x, y) {
        x := * ?1n y;
        z := + y y;
        assert == x z;
    }
"""

print(Tokenizer.tokenize(P1))
print(Parser.parse_string(P1))
