__author__ = 'Afsoon Afzal'

from pycparser import c_parser, c_ast, parse_file
from process_program import ProcessProgram


class FaultLocalization():
    def __init__(self, program):
        self.program = program

    def line_to_block(self, line_number):
        parser = c_parser.CParser()
        ast = parser.parse(self.program.processed_text, filename='<none>')
        ast.show()

    def traverse_tree(self, line_number, ast):
        return


if __name__ == "__main__":
    pp = ProcessProgram('median.c')
    print pp.processed_text
    fl = FaultLocalization(pp)
    fl.line_to_block(1)
