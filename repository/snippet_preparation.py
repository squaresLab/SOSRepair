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
            if cursor and (str(child.location.file) != self.filename or child.kind == CursorKind.DECL_STMT):
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
                self.write_file(from_line, line, vars)
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
        variables = set({})
        for block in blocks:
            for i in block.walk_preorder():
                if (i.kind == CursorKind.UNEXPOSED_EXPR or i.kind == CursorKind.DECL_REF_EXPR) and\
                                i.displayname != '':
                    if i.type.kind == TypeKind.FUNCTIONPROTO or\
                            (i.type.kind == TypeKind.POINTER and i.type.get_pointee().kind == TypeKind.FUNCTIONPROTO):
                        continue
                    variables.add((i.displayname, i.type.spelling))
        return variables

    def write_file(self, from_line, to_line, variables):
        s = '''#include <klee/klee.h>
#include <stdio.h>
#include <string.h>


struct s{
'''
        for name, type in variables:
            s += type + " " + name + ";\n"
        s += '''
        };

struct s foo('''
        i = 0
        for name, type in variables:
            s += type + " " + name
            if i < len(variables) -1:
                s += ', '
            i += 1
        s += '){\n'
        with open(self.filename, 'r') as f:
            i = 1
            for line in f:
                if from_line <= i < to_line:
                    s += line
                elif i >= to_line:
                    break
                i += 1
        s += 'struct s afs_ret;\n'
        for name, type in variables:
            s += 'afs_ret.' + name + " = " + name + ";\n"
        s += '''
        return afs_ret;
        }
        int main(){
	    struct s ret;
	    '''
        for name, type in variables:
            s += type + " " + name + ";\n"
            s += type + " " + name + "_afs;\n"
        for name, type in variables:
            s += 'klee_make_symbolic(&' + name + ', sizeof(' + name + '), "' + name + '");\n'
            s += 'klee_make_symbolic(&' + name + '_afs, sizeof(' + name + '_afs), "' + name + '_afs");\n'
        s += 'ret = foo('
        i = 0
        for name, type in variables:
            s += name
            if i < len(variables) -1:
                s += ', '
            i += 1
        s += ');\n'
        for name, type in variables:
            s += 'klee_assume(' + name +'_afs == ret.'+ name+');\n'
        s += '''
        return 0;
        }
        '''
        print s
        return s

if __name__ == "__main__":
    fl = CodeSnippet('../median.c')
    fl.detach_snippets()
