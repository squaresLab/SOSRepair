__author__ = 'Afsoon Afzal'

from pycparser import c_parser, c_ast, parse_file
from process_program import ProcessProgram
from pycparser.c_ast import If


class FaultLocalization():
    def __init__(self, program):
        self.program = program

    def line_to_block(self, line_number):
        parser = c_parser.CParser()
        ast = parser.parse(self.program.processed_text, filename='<none>')
        ast.show()
        return self.traverse_tree(line_number, ast)

    def traverse_tree(self, line_number, ast):
        block = (1, self.program.total_lines)
        current = ast
        children = ast.children()
        cond = True
        while(cond):
            print block
            for temp, child in children:
                print child.coord.line
                if child.coord.line > line_number:
                    temp_block = (current.coord.line, child.coord.line)
                    if temp_block[1] - temp_block[0] < 6:
                        cond = False
                    else:
                        block = temp_block
                    if isinstance(current, If):
                        cond = False
                    break
                current = child
            children = current.children()

        return block


if __name__ == "__main__":
    pp = ProcessProgram('median.c')
    print pp.processed_text
    fl = FaultLocalization(pp)
    print fl.line_to_block(19)
