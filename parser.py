# Simple lexer and recursive descent parser for sketchy.

from enum import Enum, auto
import re
from translate import *

class TokenType(Enum):
    OPEN_PARENTHESIS = auto()
    CLOSE_PARENTHESIS = auto()
    OPEN_CURLY_BRACKET = auto()
    CLOSE_CURLY_BRACKET = auto()
    COMMA = auto()
    SEMICOLON = auto()
    ASSIGNMENT = auto()

    OP_BV_ADD = auto()
    OP_BV_MUL = auto()
    OP_BV_SUB = auto()
    OP_BV_UDIV = auto()
    OP_BV_AND = auto()
    OP_BV_OR  = auto()
    OP_BV_XOR = auto()
    OP_BV_UREM = auto()
    OP_BV_SHL = auto()
    OP_BV_LSHR = auto()

    OP_BV_NOT = auto()
    OP_BV_NEG = auto()

    OP_BV_ULT = auto()
    OP_BV_EQ = auto()

    OP_BOOL_NOT = auto()
    OP_BOOL_AND = auto()
    OP_BOOL_OR = auto()

    NAME = auto()
    NUMBER = auto()
    BOOLEAN_HOLE = auto()
    NUMBER_HOLE = auto()

    KW_FUNCTION = auto()
    KW_FOR = auto()
    KW_IF = auto()
    KW_ELSE = auto()
    KW_ASSERT = auto()
    KW_FROM = auto()
    KW_TO = auto()

class Token:
    def __init__(self, type, value=None, **props):
        self.type = type
        self.value = value
        self.props = props

    def __repr__(self):
        if self.value is not None:
            return str(self.type) + '(' + str(self.value) + ')'
        return str(self.type)

    def has_prop(self, p):
        return p in self.props

    def get_prop(self, p):
        return self.props.get(p)

class Tokenizer:
    def check_for(self, string, token_type, **props):
        if ''.join(self.s[self.i:self.i + len(string)]) == string:
            self.tokens.append(Token(token_type, None, **props))
            self.i += len(string)
            return True
        return False

    def consume_name(self):
        name = []

        while re.match('[a-zA-Z0-9_]', self.s[self.i]):
            name.append(self.s[self.i])
            self.i += 1

        return ''.join(name)

    def consume_number(self):
        n = 0

        while re.match('[0-9]', self.s[self.i]):
            n = 10*n + int(self.s[self.i])
            self.i += 1

        return n

    def tokenize_string(self, s):
        'Transform a string into a list of tokens (aka the whole lexical analyzer)'

        # Add an extra special character to avoid a bunch of bounds checking.
        EOF = '<EOF>'
        s = list(s) + [EOF]

        self.s = s
        self.i = 0
        self.tokens = []

        while self.i < len(s):
            if s[self.i] == EOF:
                break

            if (self.check_for('(', TokenType.OPEN_PARENTHESIS) or
                    self.check_for(')', TokenType.CLOSE_PARENTHESIS) or
                    self.check_for('{', TokenType.OPEN_CURLY_BRACKET) or
                    self.check_for('}', TokenType.CLOSE_CURLY_BRACKET) or
                    self.check_for(',', TokenType.COMMA) or
                    self.check_for(';', TokenType.SEMICOLON) or
                    self.check_for(')', TokenType.CLOSE_PARENTHESIS) or
                    self.check_for(':=', TokenType.ASSIGNMENT) or
                    self.check_for('+', TokenType.OP_BV_ADD, bvop2=BVOp2.BVADD) or
                    self.check_for('*', TokenType.OP_BV_MUL, bvop2=BVOp2.BVMUL) or
                    self.check_for('-', TokenType.OP_BV_SUB, bvop2=BVOp2.BVSUB) or
                    self.check_for('/', TokenType.OP_BV_UDIV, bvop2=BVOp2.BVUDIV) or
                    self.check_for('&', TokenType.OP_BV_AND, bvop2=BVOp2.BVAND) or
                    self.check_for('|', TokenType.OP_BV_OR, bvop2=BVOp2.BVOR) or
                    self.check_for('^', TokenType.OP_BV_XOR, bvop2=BVOp2.BVXOR) or
                    self.check_for('%', TokenType.OP_BV_UREM, bvop2=BVOp2.BVUREM) or
                    self.check_for('<<', TokenType.OP_BV_SHL, bvop2=BVOp2.BVSHL) or
                    self.check_for('>>', TokenType.OP_BV_LSHR, bvop2=BVOp2.BVLSHR) or
                    self.check_for('!', TokenType.OP_BV_NOT, bvop1=BVOp1.BVNOT) or
                    self.check_for('~', TokenType.OP_BV_NEG, bvop1=BVOp1.BVNEG) or
                    self.check_for('<', TokenType.OP_BV_ULT, bvcomp=BVComp.BVULT) or
                    self.check_for('==', TokenType.OP_BV_EQ, bvcomp=BVComp.BVEQ) or
                    self.check_for('not', TokenType.OP_BOOL_NOT, boolop1=BoolOp1.NOT) or
                    self.check_for('and', TokenType.OP_BOOL_AND, boolop2=BoolOp2.AND) or
                    self.check_for('or', TokenType.OP_BOOL_OR, boolop2=BoolOp2.OR) or
                    self.check_for('function', TokenType.KW_FUNCTION) or
                    self.check_for('for', TokenType.KW_FOR) or
                    self.check_for('if', TokenType.KW_IF) or
                    self.check_for('else', TokenType.KW_ELSE) or
                    self.check_for('assert', TokenType.KW_ASSERT) or
                    self.check_for('from', TokenType.KW_FROM) or
                    self.check_for('to', TokenType.KW_TO)):
                continue

            if s[self.i].isdigit():
                self.tokens.append(Token(TokenType.NUMBER, self.consume_number()))
                continue

            if s[self.i].isalpha() or s[self.i] == '_':
                self.tokens.append(Token(TokenType.NAME, self.consume_name()))
                continue

            if s[self.i] == '?':
                self.i += 1
                hole_number = self.consume_number()
                t = TokenType.BOOLEAN_HOLE if s[self.i] == 'b' else TokenType.NUMBER_HOLE
                self.i += 1
                self.tokens.append(Token(t, hole_number))
                continue

            if s[self.i].isspace():
                self.i += 1
            else:
                raise ValueError("Unknown token at " + ''.join(s[self.i:self.i+50]))

        return self.tokens

    @staticmethod
    def tokenize(s):
        return Tokenizer().tokenize_string(s)

class Parser:

    def consume(self, token_type=None, prop=None, optional=False):
        t = self.tokens[self.i]
        self.i += 1

        if token_type is not None:
            if t.type != token_type:
                if optional:
                    self.i -= 1
                    return False
                self.raise_error('Expected {}, found {}'.format(token_type, t))
            return t.value

        if prop is not None:
            if not t.has_prop(prop):
                if optional:
                    self.i -= 1
                    return False
                self.raise_error('Expected prop {} in {}'.format(prop, t))
            return t.get_prop(prop)

    def lookahead(self):
        if self.i == len(self.tokens):
            return None
        return self.tokens[self.i].type

    def lookahead_has_prop(self, prop):
        if self.i == len(self.tokens):
            return False
        return self.tokens[self.i].has_prop(prop)

    def parse_function(self):
        self.consume(TokenType.KW_FUNCTION)
        self.consume(TokenType.OPEN_PARENTHESIS)

        paramlist = Node(NT.PARAMLIST, [])

        while self.lookahead() != TokenType.CLOSE_PARENTHESIS:
            self.consume(TokenType.COMMA, optional=True)
            paramlist.args.append(self.consume(TokenType.NAME))

        self.consume(TokenType.CLOSE_PARENTHESIS)
        stmtlist = self.parse_statement_list()

        return Node(NT.FUNCTION, [paramlist, stmtlist])

    def parse_statement_list(self):
        self.consume(TokenType.OPEN_CURLY_BRACKET)
        stmts = []

        while self.lookahead() != TokenType.CLOSE_CURLY_BRACKET:
            stmts.append(self.parse_statement())
            self.consume(TokenType.SEMICOLON)

        self.consume(TokenType.CLOSE_CURLY_BRACKET)

        return Node(NT.STMTLIST, stmts)

    def parse_bv_expression(self):
        if self.lookahead() == TokenType.OPEN_PARENTHESIS:
            self.consume(TokenType.OPEN_PARENTHESIS)
            e = self.parse_bv_expression()
            self.consume(TokenType.CLOSE_PARENTHESIS)
            return e

        if self.lookahead_has_prop('bvop1'):
            bvop1 = self.consume(prop='bvop1')
            expr = self.parse_bv_expression()
            return Node(NT.BVEXPR, [bvop1, expr])

        if self.lookahead_has_prop('bvop2'):
            bvop2 = self.consume(prop='bvop2')
            expr1 = self.parse_bv_expression()
            expr2 = self.parse_bv_expression()
            return Node(NT.BVEXPR, [bvop2, expr1, expr2])

        if self.lookahead() == TokenType.NAME:
            return Node(NT.BVEXPR, [Name(self.consume(TokenType.NAME))])

        if self.lookahead() == TokenType.NUMBER:
            return Node(NT.BVEXPR, [BVLit(self.consume(TokenType.NUMBER))])

        if self.lookahead() == TokenType.NUMBER_HOLE:
            return Node(NT.BVEXPR, [self.parse_bv_hole()])

        self.raise_error()

    def parse_boolean_expression(self):
        if self.lookahead() == TokenType.OPEN_PARENTHESIS:
            self.consume(TokenType.OPEN_PARENTHESIS)
            e = self.parse_boolean_expression()
            self.consume(TokenType.CLOSE_PARENTHESIS)
            return e

        if self.lookahead_has_prop('boolop1'):
            boolop1 = self.consume(prop='boolop1')
            expr = self.parse_boolean_expression()
            return Node(NT.BOOLEXPR, [boolop1, expr])

        if self.lookahead_has_prop('boolop2'):
            boolop2 = self.consume(prop='boolop2')
            expr1 = self.parse_boolean_expression()
            expr2 = self.parse_boolean_expression()
            return Node(NT.BOOLEXPR, [boolop2, expr1, expr2])

        if self.lookahead_has_prop('bvcomp'):
            bvcomp = self.consume(prop='bvcomp')
            expr1 = self.parse_bv_expression()
            expr2 = self.parse_bv_expression()
            return Node(NT.BOOLEXPR, [bvcomp, expr1, expr2])

        if self.lookahead() == TokenType.BOOLHOLE:
            return Node(NT.BOOLEXPR, [self.parse_boolhole()])

        self.raise_error()

    def parse_if(self):
        self.consume(TokenType.KW_IF)
        self.consume(TokenType.OPEN_PARENTHESIS)
        condition = self.parse_boolean_expression()
        self.consume(TokenType.CLOSE_PARENTHESIS)
        then_body = self.parse_statement_list()

        if self.lookahead() == TokenType.KW_ELSE:
            self.consume(TokenType.TokenType.KW_ELSE)
            else_body = self.parse_statement_list()
            return Node(NT.IF, [condition, then_body, else_body])
        else:
            return Node(NT.IF, [condition, then_body])

    def parse_for(self):
        self.consume(TokenType.KW_FOR)
        self.consume(TokenType.OPEN_PARENTHESIS)
        name = self.consume(TokenType.NAME)
        self.consume(TokenType.KW_FROM)
        left_limit = self.consume(TokenType.NUMBER)
        self.consume(TokenType.KW_TO)
        right_limit = self.consume(TokenType.NUMBER)
        self.consume(TokenType.CLOSE_PARENTHESIS)
        stmts = self.parse_statement_list()
        return Node(NT.FOR, name, BVLit(left_limit), BVLit(right_limit), stmts)

    def parse_assertion(self):
        self.consume(TokenType.KW_ASSERT)
        expr = self.parse_boolean_expression()
        return Node(NT.ASSERTION, [expr])

    def parse_statement(self):
        if self.lookahead() == TokenType.KW_ASSERT:
            return self.parse_assertion()
        if self.lookahead() == TokenType.KW_IF:
            return self.parse_if()
        if self.lookahead() == TokenType.KW_FOR:
            return self.parse_for()
        if self.lookahead() == TokenType.NAME:
            return self.parse_assignment()
        self.raise_error()

    def parse_bv_hole(self):
        return Node(NT.BVHOLE, [self.consume(TokenType.NUMBER_HOLE)])

    def parse_boolhole(self):
        return Node(NT.BOOLHOLE, [self.consume(TokenType.BOOLEAN_HOLE)])

    def parse_assignment(self):
        name = self.consume(TokenType.NAME)
        self.consume(TokenType.ASSIGNMENT)
        expr = self.parse_bv_expression()
        return Node(NT.ASSIGNMENT, [name, expr])

    def parse(self, tokens):
        self.tokens = tokens
        self.i = 0
        return self.parse_function()

    @staticmethod
    def parse_string(s):
        return Parser().parse(Tokenizer.tokenize(s))
