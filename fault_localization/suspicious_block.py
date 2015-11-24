__author__ = 'Afsoon Afzal'

from pycparser import c_parser, c_ast, parse_file


class FaultLocalization():
    def __init__(self, program):
        self.program = program

    def line_to_block(self, line_number):
        parser = c_parser.CParser()
        ast = parser.parse(self.program, filename='<none>')
        return


if __name__ == "__main__":
    fl = FaultLocalization("hello world;")
