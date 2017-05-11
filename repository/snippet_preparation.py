__author__ = 'Afsoon Afzal'

import logging
from os import path
import re
from clang.cindex import *
from clang.cindex import BinaryOperator
from settings import LIBCLANG_PATH, LARGEST_SNIPPET, SMALLEST_SNIPPET, VALID_TYPES, MAKE_OUTPUT
from utils.file_process import number_of_lines, find_extra_compile_args, find_includes
from utils.klee import *
from repository.db_manager import DatabaseManager

Config.set_library_file(LIBCLANG_PATH)
logger = logging.getLogger(__name__)


class CodeSnippetManager:
    """
    Finds and prepares code snippets to be inserted into the DB
    """
    def __init__(self, filename):
        self.filename = filename
        self.root = None
        self.number_of_lines = number_of_lines(filename)
        self.db_manager = DatabaseManager()
        self.extra_args = []
        self.includes = ''

    def detach_snippets(self):
        logger.debug('Snippet file: ' + self.filename)
        index = Index.create()
        self.extra_args = find_extra_compile_args(MAKE_OUTPUT, self.filename[:-8])  # Removing _trans.c
        logger.debug("Extra args: %s" % str(self.extra_args))
        self.root = index.parse(self.filename, self.extra_args)
        for i in self.root.get_includes():
            if i.depth == 1:
                self.includes += '#include "' + str(i.include) + '"\n'
        return self.traverse_tree(self.root.cursor, self.number_of_lines)

    def traverse_tree(self, ast, end_of_file):
        """
        Finds all the snippets in the accepted range of lines. Runs symbolic execution on it and stores the results
        into the DB
        """
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
            if cursor and (child.kind == CursorKind.DEFAULT_STMT or child.kind == CursorKind.CASE_STMT):
                blocks = [child,]
                continue
            line = child.location.line if cursor else child
            if from_line < 0:
                from_line = line
                blocks.append(child)
                continue
            dist = line - from_line
            while (line - from_line) > LARGEST_SNIPPET or blocks[0].kind == CursorKind.DEFAULT_STMT or blocks[0].kind == CursorKind.CASE_STMT:
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
            while LARGEST_SNIPPET >= (line - from_line) >= SMALLEST_SNIPPET and len(blocks) > 0:
                try:
                    vars, labels = self.find_vars(blocks)
                    outputs = self.find_outputs(blocks)
                    logger.debug("Vars and outputs: %s and %s" % (str(vars), str(outputs)))
                    if (vars != -1 and outputs != -1) and (len(vars) != 0 or len(outputs) != 0):
                        func_calls = self.find_function_calls(blocks, vars)
                        logger.debug("Functions: %s" % str(func_calls))
                        source = self.write_file(blocks, vars, outputs, func_calls, labels)
                        logger.debug("Source, line, from_line: %s, %d, %d" % (str(source), line, from_line)) 
                        code_snippet = CodeSnippet(source, vars, outputs, self.filename, func_calls)
                        res = self.symbolic_execution(code_snippet)
                        if res:
                            self.db_manager.insert_snippet(code_snippet)
                        del code_snippet
                except Exception as e:
                    logger.error("Something wrong in snippet preparation: %s" % str(e))
                if len(blocks) == 1:
                    self.traverse_tree(blocks[0], line)
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
        """
        Finds all the output variables. We consider a variable as output if it was written to but not read later.
        """
        outputs = {}
        for block in snippet_blocks:
            for node in block.walk_preorder():
                if node.kind == CursorKind.RETURN_STMT:
                    for i in node.get_children():
                        return i.type.spelling
                if (node.kind == CursorKind.BINARY_OPERATOR and node.binary_operator == BinaryOperator.Assign) or \
                        node.kind == CursorKind.COMPOUND_ASSIGNMENT_OPERATOR:
                    # Find the first child as the left-hand side
                    for i in node.walk_preorder():
                        if i.kind == CursorKind.DECL_REF_EXPR or i.kind == CursorKind.UNEXPOSED_EXPR:
                            temp = i.type.spelling
                            if '[' in temp:
                                temp = i.type.element_type.spelling + ' *'
                            temp = temp.replace('const', '')
                            temp = temp.replace('unsigned', '')
                            if temp == 'char' or temp.find('int') != -1:
                                outputs[i.displayname] = {'line': i.location.line, 'type': 'int'}
                            elif str(temp).replace('*', '').strip() in VALID_TYPES:
                                outputs[i.displayname] = {'line': i.location.line, 'type': temp.strip()}
                            else:
                                final_type = i.type
                                while True:
                                    if final_type.kind == TypeKind.POINTER:
                                        final_type = final_type.get_pointee()
                                        continue
                                    if final_type.kind == TypeKind.INCOMPLETEARRAY or final_type.kind == TypeKind.CONSTANTARRAY:
                                        final_type = final_type.element_type
                                        continue
                                    break
                                print final_type.get_declaration().extent
                                outputs[i.displayname] = {'line': i.location.line, 'type': temp.strip(),
                                                          'declaration': final_type.get_declaration().extent.start.file.name}
                            # if str(temp).replace('*', '').strip() not in VALID_TYPES:
                            #     if str(temp).replace('*', '').strip() == 'FILE' and i.displayname in ['stderr', 'stdout', 'stdin']:
                            #         logger.debug("std outs found, skipping")
                            #         continue
                            #     logger.debug("Unrecognized type for output %s" % temp)
                            #     return -1
                            # if temp == 'char':
                            #     outputs[i.displayname] = {'line': i.location.line, 'type': 'int'}
                            # else:
                            #     outputs[i.displayname] = {'line': i.location.line, 'type': temp.strip()}
                            break
                elif node.kind == CursorKind.DECL_REF_EXPR or node.kind == CursorKind.UNEXPOSED_EXPR:
                    if node.displayname in outputs and node.location.line > outputs[node.displayname]['line']:
                        outputs.pop(node.displayname)
                elif node.kind == CursorKind.MEMBER_REF_EXPR and node.displayname != '':
                    if node.displayname in outputs and node.location.line == outputs[node.displayname]['line']:
                        outputs.pop(node.displayname)
        return outputs

    @staticmethod
    def find_function_calls(snippet_blocks, variables):
        """
        Finds all function calls in the snippet
        """
        variables = [i[0] for i in variables]
        function_calls = []
        for block in snippet_blocks:
            for node in block.walk_preorder():
                if node.kind == CursorKind.CALL_EXPR:
                    if node.referenced:
                        args = set({})
                        for c in node.walk_preorder():
                            logger.debug("Function just for debug: %s, %s, %s" % (str(c.displayname), str(c.kind), str(c.type.kind)))
                            if (c.kind == CursorKind.UNEXPOSED_EXPR or c.kind == CursorKind.DECL_REF_EXPR or c.kind == CursorKind.MEMBER_REF_EXPR) and \
                                    c.displayname in variables:
                                args.add(c.displayname)
                        logger.debug("Function args %s %s" % (str(args), str(variables)))
                        function_calls.append((node.displayname, node.referenced.location.file.name,
                                            {'line': (node.extent.start.line, node.extent.end.line),
                                             'column': (node.extent.start.column, node.extent.end.column),
                                             'args': args}))
        return function_calls

    @staticmethod
    def find_vars(blocks):
        """
        Finds all variables in the snippet
        """
        variables = set({})
        labels = set({})
        for block in blocks:
            logger.debug("Block: %s, %s, %s" % (str(block.displayname), str(block.kind), str(block.type.kind)))
            logger.debug("Block extent: %s" % str(block.extent))
            for i in block.walk_preorder():
                logger.debug("Just for debug: %s, %s, %s" % (str(i.displayname), str(i.kind), str(i.type.kind)))
                if i.kind == CursorKind.LABEL_REF and i.displayname != '':
                    labels.add((i.displayname, 'ref'))
                    continue
                if i.kind == CursorKind.MEMBER_REF_EXPR and i.displayname != '':
                    for var in list(variables):
                        v, t = var[0], var[1]
                        if v == i.displayname: # and t == i.type.spelling.replace('*', '').replace('const', '').strip():
                            variables.remove(var)
                            break
                if (i.kind == CursorKind.UNEXPOSED_EXPR or i.kind == CursorKind.DECL_REF_EXPR) and \
                        i.displayname != '':
                    #logger.debug("Just for debug: %s, %s" % (str(i.displayname), str(i.type.kind))) 
                    if i.type.kind == TypeKind.FUNCTIONPROTO or i.type.kind == TypeKind.FUNCTIONNOPROTO or\
                            (i.type.kind == TypeKind.POINTER and (i.type.get_pointee().kind == TypeKind.FUNCTIONPROTO or i.type.get_pointee().kind == TypeKind.FUNCTIONNOPROTO or\
                             i.type.get_pointee().kind == TypeKind.UNEXPOSED)) or i.type.kind == TypeKind.UNEXPOSED:
                        for var in list(variables):
                            v, t = var[0], var[1]
                            if v == i.displayname:
                                variables.remove(var)
                                break
                        continue
                    res = CodeSnippetManager.find_type_and_add(variables, i)
                    if not res:
                        return -1, None
        return list(variables), list(labels)

    @staticmethod
    def find_type_and_add(variables, i):
        """
        Finds the type of a variable
        """
        temp = i.type.spelling
        if '[' in temp:
            temp = i.type.element_type.spelling + ' *'
        logger.debug('Type: %s' % str(i.type.spelling))
        temp = temp.replace('const', '')
        temp = temp.replace('unsigned', '')
        if str(temp).replace('*', '').strip() in ['double', 'long', 'size_t', 'short', 'float']:
            temp = str(temp).replace(re.sub('[\s+]', '', str(temp).replace('*', '').strip()), 'int')
        if temp == 'char' or temp.find('int') != -1:
            variables.add((i.displayname, 'int'))
        elif str(temp).replace('*', '').strip() in VALID_TYPES:
            variables.add((i.displayname, re.sub('[\s+]', '', temp.strip())))
        elif str(temp).replace('*', '').strip() == 'void':
            if i.displayname in [t[0] for t in variables]:
                return True  # continue
            return False  # -1, None
        else:
            final_type = i.type
            while True:
                if final_type.kind == TypeKind.INCOMPLETEARRAY or final_type.kind == TypeKind.CONSTANTARRAY:
                    final_type = final_type.element_type
                    continue
                if final_type.kind == TypeKind.POINTER:
                    final_type = final_type.get_pointee()
                    continue
                break
            print str(i.type.get_declaration().extent) + " " + str(final_type.spelling)
            print final_type.get_declaration().extent
            variables.add((i.displayname, re.sub('[\s+]', '', temp.strip()), final_type.get_declaration().extent.start.file.name))
        return True

    def write_file(self, blocks, variables, outputs, function_calls, labels=None):
        """
        Prepares a file to be used with KLEE
        """
        s = '''#include <klee/klee.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define break
'''
        s += self.includes
        if isinstance(outputs, str):
            s += outputs + ' foo('
        elif len(outputs) == 1:
            s += outputs[outputs.keys()[0]]['type'] + ' foo('
        elif len(outputs) == 0:
            s += 'void foo('
        else:
            s += '''
struct s{
'''
            for name in outputs.keys():
                if '*' not in outputs[name]['type']:
                    s += outputs[name]['type'] + " " + name + ";\n"
                else:
                    s += outputs[name]['type'].replace('*', '') + " " + name + "[10];\n"
            s += '''
            };

struct s foo('''

        i = 0
        for var in variables:
            name, typ = var[0], var[1]
            s += typ + " " + name
            if i < len(variables) - 1:
                s += ', '
            i += 1
        s += '){\n'
        code_snippet = ''
        with open(self.filename, 'r') as f:
            i = 1
            function_lines = [func[2]['line'][0] for func in function_calls]
            func_end = 0
            variable_dictionary = {}
            for var in variables:
                variable_dictionary[var[0]] = var[1]
            for line in f:
                if func_end < i:
                    func_end = 0
                elif func_end:  # for now we assumed no function call appears in the same line as other statements
                    if func_end == i:
                        func_end = 0
                    code_snippet += line
                    i += 1
                    continue
                if i in function_lines:
                    remove = True
                    for t1, t2, info in function_calls:
                        if info['line'][0] == i:
                            logger.debug("Args: %s" % str(info['args']))
                            if line[:info['column'][0]-1].strip():  # means the function call is sharing the line with others
                                remove = False
                                break
                            for name in info['args']:
                                typ = variable_dictionary[name]
                                if '*' not in typ:
                                    s += 'klee_make_symbolic(&' + name + ', sizeof(' + name + '), "' + name + '");\n'
                                elif typ.replace('*', '').strip() in VALID_TYPES:
                                    s += 'klee_make_symbolic(' + name + ', 20 * sizeof(' + typ.replace('*', '', 1) + '), "' + name + '");\n'
                                else:
                                    s += 'klee_make_symbolic(' + name + ', sizeof(' + typ.replace('*', '', 1) + '), "' + name + '");\n'
                            func_end = info['line'][1]
                            break
                    if remove:
                        code_snippet += line
                        i += 1
                        continue
                if i == blocks[0].extent.start.line:
                    if line[blocks[0].extent.start.column-1:].strip().startswith('else'):  # Solo else
                        s += 'if(0);\n'
                        continue
                    temp = ''
                    if i == blocks[-1].extent.end.line:
                        temp += line[blocks[0].extent.start.column-1:blocks[-1].extent.end.column]
                    else:
                        temp += line[blocks[0].extent.start.column-1:]
                    for letter in line[blocks[0].extent.start.column-2::-1]:
                        logger.debug('Letter: %s' % letter)
                        if letter == ' ':
                            continue
                        elif letter == '(':
                            temp = '(' + temp
                        else:
                            break
                    s += temp
                    code_snippet += temp
                elif blocks[0].extent.start.line < i < blocks[-1].extent.end.line:
                    s += line
                    code_snippet += line
                elif i == blocks[-1].extent.end.line:
                    s += line[:blocks[-1].extent.end.column]
                    code_snippet += line[:blocks[-1].extent.end.column]
                elif i > blocks[-1].extent.end.line:
                    break
                i += 1
        if not (code_snippet.strip().endswith(";") or code_snippet.strip().endswith("}")):
            code_snippet += ";"
            s += ";\n"
        logger.debug("Snippet: %s" % code_snippet)
        # s += code_snippet

        if labels:
            for l, t in labels:
                s += str(l) + ':;\n'

        if isinstance(outputs, str):
            s += '''
            }
            int main(){
            '''
            if '*' not in outputs:
                s += outputs + ' ret;\n'
            else:
                s += outputs.replace('*', '', 1) + ' ret[10];\n'
            s += 'klee_make_symbolic(&ret, sizeof(ret), "return_value");\n'
        elif len(outputs) == 1:
            s += 'return ' + outputs.keys()[0] + ';\n'
            s += '''
            }

            int main(){
            '''
            if '*' not in outputs[outputs.keys()[0]]['type']:
                s += outputs[outputs.keys()[0]]['type'] + ' ret;\n'
            else:
                s += outputs[outputs.keys()[0]]['type'].replace('*', '', 1) + ' ret[10];\n'
            s += 'klee_make_symbolic(&ret, sizeof(ret), "' + outputs.keys()[0] + '_ret");\n'
        elif len(outputs) == 0:
            s += '''
            }

            int main(){
            '''
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
                s += outputs[name]['type'] + " " + name + "_ret;\n"
                s += 'klee_make_symbolic(&' + name + '_ret, sizeof(' + name + '_ret), "' + name + '_ret");\n'

        for var in variables:
            name, typ = var[0], var[1]
            if '*' not in typ:
                s += typ + " " + name + ";\n"
                s += 'klee_make_symbolic(&' + name + ', sizeof(' + name + '), "' + name + '");\n'
            elif typ.replace('*', '').strip() in VALID_TYPES:
                s += typ + " " + name + " = malloc( 20 * sizeof(" + typ.replace('*', '', 1) + " ));\n"
                s += 'klee_make_symbolic(' + name + ', 20 * sizeof(' + typ.replace('*', '', 1) + '), "' + name + '");\n'
            else:
                s += typ + " " + name + " = malloc( sizeof(" + typ.replace('*', '', 1) + " ));\n"
                s += 'klee_make_symbolic(' + name + ', sizeof(' + typ.replace('*', '', 1) + '), "' + name + '");\n'

        foo = 'foo('
        i = 0
        for var in variables:
            name, typ = var[0], var[1]
            foo += name
            if i < len(variables) - 1:
                foo += ', '
            i += 1
        foo += ')'
        if isinstance(outputs, str) or len(outputs) == 1:
            s += 'klee_assume(ret == ' + foo + ');\n'
        elif len(outputs) == 0:
            s += foo + ';\n'
        else:
            s += 'ret = ' + foo + ';\n'
            for name in outputs.keys():
                s += 'klee_assume(' + name + '_ret == ret.' + name + ');\n'

        s += '''
        return 0;
        }
        '''
        with open('snippet.c', 'w') as f:
            f.write(s)
        logger.debug("Snippet on file:\n %s" % s)
        return code_snippet

    def symbolic_execution(self, code_snippet, filename='snippet.c'):
        """
        Runs KLEE on the generated file and adds constraints to the CodeSnippet
        """
        if not path.exists(filename):
            raise IOError
        if not compile_clang(filename, self.extra_args):
            return False
        number_of_paths = run_klee(filename)
        logger.debug("Number of paths generated by KLEE: " + str(number_of_paths))
        if not number_of_paths:
            return False
        for i in range(1, number_of_paths+1):
            smt = read_smt_files(i)
            code_snippet.add_constraint(smt)
        return True


class CodeSnippet():
    """
    Holds information related to a code snippet that should later be added to the DB
    """

    def __init__(self, source, variables, outputs, filepath, function_calls=[]):
        self.source = source
        self.variables = variables
        self.outputs = outputs
        self.path = filepath
        self.function_calls = function_calls
        self.constraints = []

    def add_constraint(self, constraint):
        logger.debug("Constraint %s" % str(constraint))
        self.constraints.append(constraint)

    def separate_declarations(self, constraint):
        """
        Separates declarations from the rest of the constraints
        """
        declarations = ''
        SMT = ''
        for l in constraint.splitlines():
            if l.startswith('(declare'):
                if declarations:
                    declarations += '\n' + l
                else:
                    declarations += l
            elif l.startswith('(assert'):
                SMT += l[8:-1] #removing (assert ) from the SMT
        return declarations, SMT

