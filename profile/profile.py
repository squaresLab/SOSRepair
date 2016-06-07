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

    # def find_variables(self):
    #     self.variables = []
    #     for i in self.suspicious_block.function.walk_preorder():
    #         if i.kind == CursorKind.PARM_DECL or i.kind == CursorKind.VAR_DECL:
    #             self.variables.append(i)
    #             print str(i.displayname) + " " + str(i.location.line) + " " + str(i.kind) + " " + str(i.type.kind) + " " + str(i.location.file)
    #     return self.variables

    def generate_file(self):
        state = 'printf("input start:'
        state_vars = ''
        for v, t in self.suspicious_block.vars:
            state += v
            if t == 'int' or t == 'char':
                state += ':%d'
            elif t == 'float' or t == 'double':
                state += ':%f'
            elif t == 'char*' or t == '*char' or t == 'char *' or t == '* char':
                state += ':%s'
            #TODO Pointers
            state += ':' + t + '_'
            state_vars += ', ' + v
            self.variables.append(v)
        state += '\\n"' + state_vars + ");\n"
        i = 0
        with open(self.filename) as f:
            out = open(self.marked_file , "w")
            for line in f:
                i += 1
                if i == self.suspicious_block.line_range[0] or i == self.suspicious_block.line_range[1]:
                    out.write(state)
                out.write(line)
            out.flush()
            out.close()

    def generate_profile(self, positive_tests):
        res = compile_c(self.marked_file, self.filename + '.o')
        if not res:
            # raise Exception
            print "ERROR: the profile is not compilable"
            return False
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
                # This happens when the block contains return
                # raise Exception
                return False
            profile_dict = {}
            for i in range(len(lines[0])):
                if lines[0][i] == '\n':
                    continue
                parts1 = lines[0][i].split(':')
                parts2 = lines[1][i].split(':')
                if len(parts1) < 3 or len(parts2) < 3 or parts1[0] != parts2[0]:
                    print "ERROR: something is wrong in profile generation"
                    return
                profile_dict[parts1[0]] = (''.join(parts1[1:-1]), ''.join(parts2[1:-1]))
            self.input_list.append(profile_dict)
        os.system('rm ' + self.filename + '.o ' + self.filename + '_temp.out')
        print self.input_list
        return True

    def generate_gdb_script(self, positive_tests):
        res = compile_c(self.filename, self.filename + '.o', '-g')
        if not res:
            # raise Exception
            print "ERROR: the profile is not compilable"
            return False
        file_and_breaks = 'file ' + self.filename + '.o\n'
        file_and_breaks += 'break ' + self.filename + ':' + str(self.suspicious_block.line_range[0]) + '\n'
        file_and_breaks += 'break ' + self.filename + ':' + str(self.suspicious_block.line_range[1]) + '\n'

        vars = ''
        for v, t in self.suspicious_block.vars:
            vars += 'print ' + str(v) + '\n'
        vars += 'continue\n'
        vars += vars

        for pt in positive_tests:
            test = os.path.join(TESTS_DIRECTORY, pt)
            states = []
            with open('gdb_script.txt', 'w') as f:
                f.write(file_and_breaks)
                f.write('run < ' + test + '\n')
                f.write(vars)

            res = os.system('gdb < gdb_script.txt > gdb_out')
            if res != 0:
                print "WARNING: cannot run gdb"
                continue
            with open('gdb_out', 'r') as f:
                for l in f:
                    if l.startswith('(gdb) $'):
                        parts = l[7:].split('=')
                        if len(parts) != 2:
                            print "WARNING: something is wrong"
                            continue
                        try:
                            i = int(parts[0])
                        except:
                            print "WARNING: something is wrong"
                            continue
                        states.append(parts[1].strip())  # TODO strip for Strings?
            if len(states) != len(self.suspicious_block.vars)*2:
                print "WARNING: not enough output"
                continue
            profile_dict = {}
            for i in range(len(states)/2):
                profile_dict[self.suspicious_block.vars[i][0]] = (states[i], states[i+len(self.suspicious_block.vars)])
            self.input_list.append(profile_dict)
        return True

if __name__ == "__main__":
    fl = FaultLocalization('median.c')
    sb = fl.line_to_block(20)
    profile = Profile('median.c', sb)
    # profile.find_variables()
    profile.generate_file()



