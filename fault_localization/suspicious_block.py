__author__ = 'Afsoon Afzal'

from clang.cindex import *
from settings import *

Config.set_library_file(LIBCLANG_PATH)


class SuspiciousBlock():
    def __init__(self, line_number, block, node, function):
        self.line_number = line_number
        self.block = block
        self.node = node
        self.function = function



class FaultLocalization():
    def __init__(self, filename):
        self.filename = filename
        self.root = None

    def line_to_block(self, line_number):
        index = Index.create()
        self.root = index.parse(self.filename)
        return self.traverse_tree(line_number, self.root.cursor)

    def traverse_tree(self, line_number, ast):
        assert (isinstance(ast, Cursor))
        block = (1, 10000000)
        current = ast
        children = ast.get_children()
        function = None
        cond = True
        while cond:
            for child in children:
                cond = True
                if str(child.location.file) != self.filename:
                    continue
                print block
                print str(child.spelling) + " " + str(child.location.file)
                print child.location.line
                if child.location.line > line_number:
                    temp_block = (current.location.line, child.location.line)
                    if current.kind == CursorKind.IF_STMT:
                        cond = False
                    elif temp_block[1] - temp_block[0] < 4:
                        cond = False
                        if block[1] - block[0] > 6:
                            block = (temp_block[1] - 6, temp_block[1])
                        break
                    block = temp_block
                    break
                current = child
                if child.kind == CursorKind.FUNCTION_DECL:
                    function = child
            children = current.get_children()

        return SuspiciousBlock(line_number, block, current, function)


if __name__ == "__main__":
    fl = FaultLocalization('src/fdevent_freebsd_kqueue.c')
    sb = fl.line_to_block(57)
    print str(sb.block) + " " + str(sb.node.kind) + " " + str(sb.node.type.kind) + " " + str(sb.function.spelling)
