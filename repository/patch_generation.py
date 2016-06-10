__author__ = 'Afsoon Afzal'

import logging
from clang.cindex import *
import os

logger = logging.getLogger(__name__)


class PatchGeneration():

    def __init__(self, source, variables, mapping, temporary_file='temp_snippet.c'):
        self.source = source
        self.variables = variables
        self.mapping = mapping
        self.temporary_file = temporary_file
        assert isinstance(self.mapping, dict)

    def prepare_snippet_to_parse(self):
        with open(self.temporary_file, 'w') as f:
            f.write("void foo(){\n")
            for v, t in self.variables:
                f.write(t + " " + v + ";\n")
            f.write(self.source)
            f.write("\n}\n")
        return self.temporary_file

    def parse_snippet(self):
        index = Index.create()
        root = index.parse(self.temporary_file)
        return root.cursor

    def replace_vars(self, ast):
        lines = self.source.splitlines()
        s = ''
        line, column = 0, 0
        var_dict = dict(self.variables)
        for i in ast.walk_preorder():
            # print str(i.location.line) + ":" + str(i.location.column) + " " + str(i.kind) + " " + i.displayname + " " + str(i.type.kind)
            if str(i.location.file) != self.temporary_file or i.location.line <= 1+len(self.variables) or\
                    (i.location.line - (2+len(self.variables)) == line and column + 1 > i.location.column):
                continue
            if str(i.displayname) in var_dict.keys():
                l, c = i.location.line - (2+len(self.variables)), i.location.column
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
        with open(patch_file, 'w') as patch:
            with open(suspicious_block.filename, 'r') as f:
                i = 0
                snippet_written = False
                for l in f:
                    i += 1
                    if i < suspicious_block.line_range[0] or i >= suspicious_block.line_range[1]:
                        patch.write(l)
                    elif snippet_written:
                        continue
                    else:
                        snippet_written = True
                        patch.write(snippet)
        return patch_file

    def remove_temp_file(self):
        os.system('rm ' + self.temporary_file)

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.remove_temp_file()