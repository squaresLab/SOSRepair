__author__ = 'Afsoon Afzal'

from clang.cindex import *


class FaultLocalization():
    def __init__(self, filename):
        Config.set_library_file('/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib/libclang.dylib')
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
        cond = True
        while(cond):
            cond = False
            for child in children:
                cond = True
                print block
                #print str(child.spelling) + " " + str(child.location.file)
                if str(child.location.file) != self.filename:
                    continue
                #print child.location.line
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
            children = current.get_children()



        return block


if __name__ == "__main__":
    fl = FaultLocalization('src/joblist.c')
    print fl.line_to_block(54)
