__author__ = 'Afsoon Afzal'

from clang.cindex import *
from settings import *
from utils.file_process import number_of_lines

Config.set_library_file(LIBCLANG_PATH)


class CodeSnippet:
    def __init__(self, filename):
        self.filename = filename
        self.root = None
        self.number_of_lines = number_of_lines(filename)

    def detach_snippets(self):
        index = Index.create()
        self.root = index.parse(self.filename)
        return self.traverse_tree(self.root.cursor, self.number_of_lines)

    def traverse_tree(self, ast, end_of_file):
        assert (isinstance(ast, Cursor))
        from_line = -1
        blocks = []
        children = list(ast.get_children())
        children.append(end_of_file)
        for child in children:
            cursor = False
            if isinstance(child, Cursor):
                cursor = True
            if cursor and str(child.location.file) != self.filename:
                continue
            line = child.location.line if cursor else child
            print line
            if from_line < 0:
                from_line = line
                blocks.append(child)
                continue
            dist = line - from_line
            if dist > 7:
                while (line - from_line) > 7:
                    if len(blocks) == 1:  # means it's a large block
                        self.traverse_tree(blocks[0], line)
                        blocks.pop(0)
                        break
                    else:
                        blocks.pop(0)
                        if len(blocks) > 0:
                            from_line = blocks[0].location.line
                        else:
                            break
            while 7 >= (line - from_line) >= 3:
                vars = self.find_vars(blocks)
                self.write_file(blocks, vars)
                blocks.pop(0)
                if len(blocks) > 0:
                    from_line = blocks[0].location.line
                else:
                    break
            if cursor:
                blocks.append(child)
                from_line = blocks[0].location.line



    @staticmethod
    def find_vars(blocks):
        return []

    @staticmethod
    def write_file(blocks, vars):
        return True


if __name__ == "__main__":
    fl = CodeSnippet('../median.c')
    fl.detach_snippets()
