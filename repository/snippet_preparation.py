__author__ = 'Afsoon Afzal'

from clang.cindex import *
from settings import *

Config.set_library_file(LIBCLANG_PATH)


class CodeSnippet:
    def __init__(self, filename):
        self.filename = filename
        self.root = None

    def detach_snippets(self):
        index = Index.create()
        self.root = index.parse(self.filename)
        return self.traverse_tree(self.root.cursor)

    def traverse_tree(self, ast):
        assert (isinstance(ast, Cursor))
        current = ast
        from_line = -1
        children = ast.get_children()
        function = None
        blocks = []
        for child in children:
            if str(child.location.file) != self.filename:
                continue
            print str(child.spelling) + " " + str(child.location.file)
            print child.location.line
            if from_line < 0:
                from_line = child.location.line
                blocks.append(child)
                continue
            dist = child.location.line - from_line
            if dist < 3:
                blocks.append(child)
            elif dist > 7:
                while (child.location.line - from_line) > 7:
                    if len(blocks) == 1:  # means it's a large block
                        self.traverse_tree(blocks[0])
                        blocks.remove(0)
                        break
                    else:
                        blocks.remove(0)
                        if len(blocks) > 0:
                            from_line = blocks[0].location.line
                        else:
                            break
            if len(blocks) > 0:
                from_line = blocks[0].location.line
            while 7 >= (child.location.line - from_line) >= 3:
                vars = self.find_vars(blocks)
                self.write_file(blocks, vars)
                blocks.remove(0)
                if len(blocks) > 0:
                    from_line = blocks[0].location.line
                else:
                    break
            blocks.append(child)
            from_line = blocks[0].location.line

    @staticmethod
    def find_vars(blocks):
        return []

    @staticmethod
    def write_file(blocks, vars):
        return True


if __name__ == "__main__":
    fl = CodeSnippet('median.c')
    fl.detach_snippets()
