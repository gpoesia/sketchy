from parser import *

P1 = """
    function (x, y) {
        x := * ?1n y;
        z := + y y;
        assert == x z;
    }
"""

#print(Tokenizer.tokenize(P1))
#print(Parser.parse_string(P1))

LINEAR_COMBINATION_PROGRAM = """
    function (x, y) {
        x_old := x;
        x := + x y;
        x := + x y;
        x := + x y;
        z := + (* x_old ?0n) (* y ?1n);
        assert = x z;
    }
"""

print(Tokenizer.tokenize(LINEAR_COMBINATION_PROGRAM))
print(Parser.parse_string(LINEAR_COMBINATION_PROGRAM))
