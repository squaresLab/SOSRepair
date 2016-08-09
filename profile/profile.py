__author__ = 'Afsoon Afzal'

from clang.cindex import *
import os
import logging

from settings import *
from fault_localization.suspicious_block import FaultLocalization
from utils.c_run import *

logger = logging.getLogger(__name__)


class Profile():

    def __init__(self, suspicious_block):
        self.filename = FAULTY_CODE
        self.suspicious_block = suspicious_block
        self.variables = []
        self.input_list = []
        self.marked_file = self.filename + "_marked.c"
        self.output_file = self.filename + "_output.txt"

    # def find_variables(self):
    #     self.variables = []
    #     for i in self.suspicious_block.function.walk_preorder():
    #         if i.kind == CursorKind.PARM_DECL or i.kind == CursorKind.VAR_DECL:
    #             self.variables.append(i)
    #             print str(i.displayname) + " " + str(i.location.line) + " " + str(i.kind) + " " + str(i.type.kind) + " " + str(i.location.file)
    #     return self.variables

    def generate_printing_profile(self, positive_tests, original=FAULTY_CODE+'_orig.c'):
        # copy original file to somewhere safe
        self.generate_file()
        run_command('cp ' + self.marked_file + ' ' + self.filename)
        res = self.generate_profile(positive_tests)
        print self.input_list
        run_command('cp ' + original + ' ' + self.filename)
        run_command('rm ' + self.marked_file)
        return res

    def generate_file(self):
        state = 'fprintf(fp, "input start:'
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
            state += ':' + t + '_afs_'
            state_vars += ', ' + v
            self.variables.append(v)
        state += '\\n"' + state_vars + ");\n"
        i = 0
        with open(self.filename) as f:
            out = open(self.marked_file, "w")
            for line in f:
                i += 1
                if i == self.suspicious_block.line_range[0]:
                    out.write('FILE *fp = fopen("' + self.output_file + '", "w");\n')
                    out.write('fprintf(fp, "input\\n");\n')
                    out.write(state)
                    out.write("fflush(fp);\n")
                elif i == self.suspicious_block.line_range[1]:
                    out.write('fprintf(fp, "output\\n");\n')
                    out.write(state)
                    out.write("fclose(fp);\n")
                out.write(line)
            out.flush()
            out.close()

    def generate_profile(self, positive_tests):
        res = run_command_with_timeout(COMPILE_SCRIPT, timeout=10)
        if not res:
            logger.error("the profile is not compilable")
            return False
        for pt in positive_tests:
            run_command('rm ' + self.output_file)
            res = run_command_with_timeout(TEST_SCRIPT + ' ' + pt)
            if not res:
                raise Exception
            lines = []
            try:
                with open(self.output_file, 'r') as f:
                    for l in f:
                        index = l.find('input start:')
                        if index != -1:
                            lines.append(l[index+12:].split('_afs_'))
            except IOError:
                logger.warning("This test probabely does not pass the faulty code %s" % pt)
                continue
            if len(lines) != 2 or len(lines[0]) != len(lines[1]):
                logger.error("Error in generating profile " + str(len(lines)))
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
                    logger.error("something is wrong in profile generation")
                    return
                profile_dict[parts1[0]] = (''.join(parts1[1:-1]), ''.join(parts2[1:-1]))
            self.input_list.append(profile_dict)
        logger.debug(self.input_list)
        return True

    def generate_gdb_script(self, positive_tests):
        file_and_breaks = 'file ' + TEST_SCRIPT_TYPE + '\n'
        file_and_breaks += 'set breakpoint pending on\n'
        file_and_breaks += 'break ' + self.filename + ':' + str(self.suspicious_block.line_range[0]) + '\n'
        file_and_breaks += 'break ' + self.filename + ':' + str(self.suspicious_block.line_range[1])
        file_and_breaks += '''
set detach-on-fork off
set non-stop on
set pagination on
set target-async on
set confirm off
'''

        vars = ''
        for v, t in self.suspicious_block.vars:
            vars += 'print ' + str(v) + '\n'
        vars += 'continue\n'

        for pt in positive_tests:
            states = []
            with open('gdb_script.txt', 'w') as f:
                f.write(file_and_breaks)
                f.write('set args ' + TEST_SCRIPT + ' ' + pt + '\n')
                f.write('command 1\n' + vars + 'end\n')
                f.write('command 2\n' + vars + 'end\n')
                f.write('run\n')
            res = run_command('gdb --command=gdb_script.txt > gdb_out')
            if not res:
                logger.warning("cannot run gdb")
                continue
            with open('gdb_out', 'r') as f:
                for l in f:
                    if l.startswith('(gdb) $'):
                        parts = l[7:].split('=')
                        if len(parts) != 2:
                            logger.warning("something is wrong")
                            continue
                        try:
                            i = int(parts[0])
                        except:
                            logger.warning("something is wrong")
                            continue
                        if parts[1].strip().startswith('"'): # it's a string
                            states.append(parts[1].strip()[1:parts[1].strip().find('\\000')])
                        else:
                            states.append(parts[1].strip())  # TODO strip for Strings?
            if len(states) != len(self.suspicious_block.vars)*2:
                logger.warning("not enough output")
                continue
            profile_dict = {}
            for i in range(len(states)/2):
                profile_dict[self.suspicious_block.vars[i][0]] = (states[i], states[i+len(self.suspicious_block.vars)])
            self.input_list.append(profile_dict)
        os.system('rm gdb_script.txt gdb_out')
        return True

if __name__ == "__main__":
    fl = FaultLocalization('median.c')
    sb = fl.line_to_block(20)
    profile = Profile('median.c', sb)
    # profile.find_variables()
    profile.generate_file()



