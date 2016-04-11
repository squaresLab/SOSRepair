__author__ = 'Afsoon Afzal'

from os import path
from clang.cindex import *
from clang.cindex import BinaryOperator
from settings import *
from utils.file_process import number_of_lines
from utils.klee import *

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
            if dist > LARGEST_SNIPPET:
                while (line - from_line) > LARGEST_SNIPPET:
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
            while LARGEST_SNIPPET >= (line - from_line) >= SMALLEST_SNIPPET:
                vars = self.find_vars(blocks)
                outputs = self.find_outputs(blocks)
                func_calls = self.find_function_calls(blocks)
                code_snippet = self.write_file(from_line, line, vars, outputs, func_calls)
                print outputs
#                self.symbolic_execution()
                blocks.pop(0)
                if len(blocks) > 0:
                    from_line = blocks[0].location.line
                else:
                    break
            if cursor:
                blocks.append(child)
                from_line = blocks[0].location.line


    @staticmethod
    def find_outputs(snippet_blocks):
        outputs = {}
        for block in snippet_blocks:
            for node in block.walk_preorder():
                if node.kind == CursorKind.RETURN_STMT:
                    for i in node.get_children():
                        return i.type.spelling
                if node.kind ==  CursorKind.BINARY_OPERATOR and node.binary_operator == BinaryOperator.Assign:
                    #Find the first child as the left-hand side
                    for i in node.walk_preorder():
                        if i.kind == CursorKind.DECL_REF_EXPR or i.kind == CursorKind.UNEXPOSED_EXPR:
                            outputs[i.displayname] = {'line': i.location.line, 'type': i.type.spelling}
                            break
                elif node.kind == CursorKind.DECL_REF_EXPR or node.kind == CursorKind.UNEXPOSED_EXPR:
                    if node.displayname in outputs and node.location.line > outputs[node.displayname]['line']:
                        outputs.pop(node.displayname)
        return outputs

    @staticmethod
    def find_function_calls(snippet_blocks):
        function_calls = set([])
        for block in snippet_blocks:
            for node in block.walk_preorder():
                if node.kind == CursorKind.CALL_EXPR:
                    function_calls.add((node.displayname, node.referenced.location.file.name))
        return function_calls


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

    def write_file(self, from_line, to_line, variables, outputs, function_calls):
        s = '''#include <klee/klee.h>
#include <stdio.h>
#include <string.h>
'''
        for temp, func in function_calls:
            s += "#include '" + func +"'\n"
        if isinstance(outputs, str):
            s += outputs + ' foo('
        elif len(outputs) == 1:
            s += outputs[outputs.keys()[0]]['type'] + ' foo('
        else:
            s += '''
struct s{
'''
            for name in outputs.keys():
                s += outputs[name]['type'] + " " + name + ";\n"
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
        code_snippet = ''
        with open(self.filename, 'r') as f:
            i = 1
            for line in f:
                if from_line <= i < to_line:
                    code_snippet += line
                elif i >= to_line:
                    break
                i += 1
        s += code_snippet

        if isinstance(outputs, str):
            s += '''
            }
            int main(){
            '''
            s += outputs + ' ret;\n'
            s += 'klee_make_symbolic(&ret, sizeof(ret), "return_value");\n'
        elif len(outputs) == 1:
            s += 'return ' + outputs.keys()[0] + ';\n'
            s += '''
            int main(){
            '''
            s += outputs[outputs.keys()[0]]['type'] + ' ret;\n'
            s += 'klee_make_symbolic(&ret, sizeof(ret), "'+ outputs.keys()[0] +'");\n'
        else:
            s += 'struct s afs_ret;\n'
            for name in outputs.keys():
                s += 'afs_ret.' + name + " = " + name + ";\n"
            s += '''
        return afs_ret;
        }
        int main(){
	    struct s ret;
	    '''
            for name in outputs.keys():
                s += outputs[name]['type'] + " " + name + "_afs;\n"
                s += 'klee_make_symbolic(&' + name + '_afs, sizeof(' + name + '_afs), "' + name + '_afs");\n'


        for name, type in variables:
            s += type + " " + name + ";\n"
            s += 'klee_make_symbolic(&' + name + ', sizeof(' + name + '), "' + name + '");\n'


        foo = 'foo('
        i = 0
        for name, type in variables:
            foo += name
            if i < len(variables) -1:
                foo += ', '
            i += 1
        foo += ')'
        if isinstance(outputs, str) or len(outputs) == 1:
            s += 'klee_assume(ret == ' + foo + ');\n'
        else:
            s += 'ret = ' + foo + ';\n'
            for name in outputs.keys():
                s += 'klee_assume(' + name +'_afs == ret.'+ name+');\n'

        s += '''
        return 0;
        }
        '''
        print s
        # with open('snippet.c', 'w') as f:
        #     f.write(s)
        return code_snippet

    def symbolic_execution(self, filename='snippet.c'):
        if not path.exists(filename):
            raise IOError
        if not compile_clang(filename):
            return False
        number_of_paths = run_klee(filename)
        if not number_of_paths:
            return False
        print "Number of paths generated by KLEE: " + str(number_of_paths)
        return True



if __name__ == "__main__":
    fl = CodeSnippet('../median.c')
    fl.detach_snippets()
