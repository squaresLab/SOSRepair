__author__ = 'Afsoon Afzal'

import logging
from clang.cindex import *
import os

logger = logging.getLogger(__name__)


class PatchGeneration():
    """
    Generates patched file from the original buggy file, the candidate snippet and the mappings.
    """
    def __init__(self, source, variables, mapping, temporary_file='temp_snippet.c'):
        self.source = source
        self.variables = variables
        self.mapping = mapping
        self.temporary_file = temporary_file
        self.extra_lines = 1+len(variables )
        assert isinstance(self.mapping, dict)

    def prepare_snippet_to_parse(self):
        """
        Writes the snippet as a C file so that clang be able to parse it.
        :return: Name of the generated file
        """
        with open(self.temporary_file, 'w') as f:
            #f.write("#include <stddef.h>\n")
            #f.write("#define break  \n")
            for var in self.variables:
                if len(var) == 3:
                    f.write('#include "' + var[2] + '"\n')
                    self.extra_lines += 1
            f.write("void foo(){\n")
            for var in self.variables:
                v, t = var[0], var[1]
                f.write(t + " " + v + ";\n")
            if self.source.strip().startswith('else'):
                f.write('if(0);\n')
                self.extra_lines += 1
            f.write(self.source)
            f.write("\n}\n")
        return self.temporary_file

    def parse_snippet(self):
        index = Index.create()
        root = index.parse(self.temporary_file, ["-I/home/afsoon/llvm/build/lib/clang/3.9.0/include"])
        return root.cursor

    def replace_vars(self, ast):
        """
        Finds all variables in the snippet and replaces them with their mapped variable
        :param ast: clang ast of the snippet
        :return: snippet with replaced variables
        """
        lines = self.source.splitlines()
        if len(lines) == 0:
            logger.warning("Source doesn't have any split lines: %s" % self.source)
            return self.source
        s = ''
        line, column = 0, 0
        var_list = [i[0] for i in self.variables]
        for i in ast.walk_preorder():
            logger.debug("AST walk: " + str(i.location.line) + ":" + str(i.location.column) + " " + str(i.kind) + " " + i.displayname + " " + str(i.type.kind))
            if str(i.location.file) != self.temporary_file or i.location.line <= self.extra_lines or\
                    (i.location.line - (1+self.extra_lines) == line and column + 1 > i.location.column):
                continue
            if str(i.displayname) in var_list:
                l, c = i.location.line - (1+self.extra_lines), i.location.column
                if line < l:
                    s += lines[line][column:] + '\n'
                    for j in range(line+1, l):
                        s += lines[j] + '\n'
                    s += lines[l][0:c-1]
                else:
                    s += lines[l][column:c-1]
                s += self.mapping[i.displayname]
                line = l
                column = c + len(i.displayname) - 1
        s += lines[line][column:] + '\n'
        for j in range(line+1, len(lines)):
            s += lines[j] + '\n'
        logger.debug("SNIPPET: " + s)
        return s

    @staticmethod
    def create_patch(suspicious_block, snippet, patch_file='patch1.c'):
        """
        Generates a file with suspicious block replaced by the snippet.
        """
        with open(patch_file, 'w') as patch:
            with open(suspicious_block.filename, 'r') as f:
                i = 0
                snippet_written = False
                for l in f:
                    i += 1
                    if i < suspicious_block.line_range[0] or i >= suspicious_block.line_range[1]:
                        patch.write(l)
                    elif i == suspicious_block.line_range[0]:
                        patch.write(l[:suspicious_block.column_range[0]])
                        snippet_written = True
                        patch.write(snippet)
                        if i == suspicious_block.line_range[1]-1:
                            patch.write(l[suspicious_block.column_range[1]-1:])
                    elif i == suspicious_block.line_range[1]-1:
                        patch.write(l[suspicious_block.column_range[1]-1:])
                    elif snippet_written:
                        continue
        return patch_file

    def remove_temp_file(self):
        os.system('rm ' + self.temporary_file)

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.remove_temp_file()
