__author__ = 'Afsoon Afzal'

from clang.cindex import *
import os

from settings import TESTS_DIRECTORY
from fault_localization.suspicious_block import FaultLocalization
from utils.c_run import compile_c, run_c_with_input


class Profile():

    def __init__(self, filename, suspicious_block):
        self.filename = filename
        self.suspicious_block = suspicious_block
        self.variables = []
        self.input_list = []
        self.marked_file = self.filename + "_marked.c"

    def find_variables(self):
        self.variables = []
        for i in self.suspicious_block.function.walk_preorder():
            if i.kind == CursorKind.PARM_DECL or i.kind == CursorKind.VAR_DECL:
                self.variables.append(i)
                print str(i.displayname) + " " + str(i.location.line) + " " + str(i.kind) + " " + str(i.type.kind) + " " + str(i.location.file)
        return self.variables


    def generate_file(self):
        state = 'printf("input start:'
        state_vars = ''
        for v in self.variables:
            name = v.displayname
            if v.type.kind == TypeKind.INT:
                state += name + ':%d:int_'
            elif v.type.kind == TypeKind.FLOAT or v.type.kind == TypeKind.DOUBLE:
                state += name + ':%f:float_'
            elif v.type.kind == TypeKind.CHAR_S:
                state += name + ':%d:char_'
            elif v.type.kind == TypeKind.POINTER:
                if v.type.get_pointee().kind == TypeKind.CHAR_S:
                    state += name + ':%s:char*_'
                else:
                    #TODO Pointers
                    continue
            state_vars += ', ' + name
        state += '\\n"' + state_vars + ");\n"
        i = 0
        with open(self.filename) as f:
            out = open(self.marked_file , "w")
            for line in f:
                i += 1
                if i == self.suspicious_block.block[0] or i == self.suspicious_block.block[1]:
                    out.write(state)
                out.write(line)
            out.flush()
            out.close()

    def generate_profile(self, positive_tests):
        res = compile_c(self.marked_file, self.filename + '.o')
        if not res:
            raise Exception
        for pt in positive_tests:
            test = os.path.join(TESTS_DIRECTORY, pt)
            res = run_c_with_input(self.filename + '.o', test, self.filename+ '_temp.out')
            if not res:
                raise Exception
            lines = []
            with open(self.filename + '_temp.out') as file:
                for l in file:
                    index = l.find('input start:')
                    if index != -1:
                        lines.append(l[index+12:].split('_'))
            if len(lines) != 2 or len(lines[0]) != len(lines[1]):
                print "Error in generating profile " + str(len(lines))
                raise Exception
            profile_list = []
            for i in range(len(lines[0])):
                if lines[0][i] == '\n':
                    continue
                profile_list.append((lines[0][i], lines[1][i]))
            self.input_list.append(profile_list)
        os.system('rm ' + self.filename + '.o ' + self.filename + '_temp.out')
        print self.input_list
        return True

if __name__ == "__main__":
    fl = FaultLocalization('median.c')
    sb = fl.line_to_block(20)
    profile = Profile('median.c', sb)
    profile.find_variables()
    profile.generate_file()



