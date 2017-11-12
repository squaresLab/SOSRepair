__author__ = 'Afsoon Afzal'

from clang.cindex import *
import os
import logging

from settings import *
from fault_localization.suspicious_block import FaultLocalization
from utils.c_run import *

logger = logging.getLogger(__name__)


class Profile:
    """
    A Profile shows values of variables in the SuspiciousBlock exactly before and after that block for all the test
    cases that pass the region.
    """
    def __init__(self, suspicious_block):
        self.filename = FAULTY_CODE
        self.suspicious_block = suspicious_block
        self.variables = []
        self.input_list = []
        self.negative_input_list = []
        self.marked_file = self.filename + "_marked.c"
        self.output_file = self.filename + "_output.txt"

    def generate_printing_profile(self, tests,  original=FAULTY_CODE+'_orig.c'):
        # copy original file to somewhere safe
        self.generate_file()
        run_command('cp ' + self.marked_file + ' ' + self.filename)
        res = self.generate_profile(tests.positives, self.input_list)
        if (not res or len(self.input_list) == 0) and SOSREPAIR:
            logger.debug("no positive profile")
            res = self.generate_profile(tests.negatives, self.negative_input_list)
            logger.debug("Negative profile: %s" % str(self.negative_input_list))
        run_command('cp ' + original + ' ' + self.filename)
        run_command('rm ' + self.marked_file)
        return res

    def update_profile(self, tests,  original=FAULTY_CODE+'_orig.c'):
        """
        Update negative profile with new information as incremental profile
        """
        # copy original file to somewhere safe
        if not os.path.isfile(self.marked_file):
            self.generate_file()
        run_command('cp ' + self.marked_file + ' ' + self.filename)
        original_len = len(self.negative_input_list)
        res = self.generate_profile(tests.negatives, self.negative_input_list)
        if not res or len(self.negative_input_list) == original_len:
            # res = self.generate_gdb_script(tests.negatives, self.negative_input_list)
            logger.debug("Update negative profile: %s" % str(self.negative_input_list))
        run_command('cp ' + original + ' ' + self.filename)
        return res

    def generate_file(self):
        """
        This function generates a file that has printf statements before and after the snippet to record their values
        """
        state = 'fprintf(fp, "input start:'
        state_vars = ''
        invalid_vars = []
        for var in self.suspicious_block.vars:
            v, t = var[0], var[1]
            if t not in VALID_TYPES and t not in ['char *', '* char', 'char*', '*char']:
                invalid_vars.append((v, t))
                continue
            state += v
            if t.find('int') != -1 or t == 'char' or t == 'long' or t == 'size_t':
                state += ':%d'
            elif t == 'float' or t == 'double':
                state += ':%f'
            elif t == 'char*' or t == '*char' or t == 'char *' or t == '* char':
                state += ':%s'
            #TODO Pointers
            state += ':' + t + '_afs_'
            state_vars += ', ' + v
            self.variables.append(v)
        if not invalid_vars:
            state += '\\n"' + state_vars + ");\n"
        else:
            state += '"' + state_vars + ");\n"
            for v, t in invalid_vars:
                if '*' in t:
                    state += 'buffer_afs = (unsigned char *)' + v + ';'
                else:
                    state += 'buffer_afs = (unsigned char *) &' + v + ';'
                state += '''
                fprintf(fp, "%s:");
                for (i_afs = 0; i_afs < sizeof(%s); i_afs++)
                    fprintf(fp, "%%d,", (unsigned) buffer_afs[i_afs]);
                fprintf(fp, ":%s_afs_");
                ''' % (v, t.replace('*', '', 1), t)
            state += 'fprintf(fp, "\\n");'
        i = 0
        with open(self.filename) as f:
            out = open(self.marked_file, "w")
            for line in f:
                i += 1
                if i == self.suspicious_block.line_range[0]:
                    out.write('FILE *fp = fopen("' + self.output_file + '", "w");\n')
                    #out.write('fprintf(fp, "input\\n");\n')
                    out.write('unsigned char *buffer_afs;\nint i_afs;\n')
                    out.write(state)
                    out.write('fprintf(fp, "--------------------------------\\n");\n')
                    out.write("fflush(fp);\n")
                if i == self.suspicious_block.line_range[1]:
                    #out.write('fprintf(fp, "output\\n");\n')
                    out.write(state)
                    out.write("fclose(fp);\n")
                out.write(line)
            out.flush()
            out.close()

    def generate_profile(self, tests, input_list):
        """
        Run the tests on the marked file and reads the output to store as profile
        :param tests: List of tests to be executed
        :param input_list: The list to be used as profile
        :return: True if success, False if failed
        """
        res = run_command_with_timeout(COMPILE_SCRIPT, timeout=70)
        if not res:
            logger.error("the profile is not compilable")
            return False
        for pt in tests:
            run_command('rm ' + self.output_file)
            logger.debug('Test running: %s' % pt)
            res = run_command_with_timeout(TEST_SCRIPT + ' ' + pt, timeout=100)
            if not res:
                print "Run failed: %s" % pt
                print "Res: %s" % str(res)
                raise Exception
            lines = []
            console_output = ''
            try:
                with open(self.output_file, 'r') as f:
                    console = False
                    ll = ''
                    for l in f:
                        index = l.find('input start:')
                        if index != -1:
                            if not console and ll:
                                lines.append(ll.split('_afs_'))
                            elif console:
                                console_output = ll
                                console = False
                            ll = l[index+12:]
                        elif l.startswith('------------'):
                            if ll:
                                lines.append(ll.split('_afs_'))
                            ll = ''
                            console = True
                        else:
                            ll += l
                    if ll:
                        lines.append(ll.split('_afs_'))
            except IOError:
                logger.warning("This test probabely does not pass the faulty code %s" % pt)
                continue
            if len(lines) != 2 or len(lines[0]) != len(lines[1]):
                logger.error("Error in generating profile " + str(len(lines)))
                # This happens when the block contains return
                # raise Exception
                continue
            profile_dict = {}
            for i in range(len(lines[0])):
                if lines[0][i] == '\n':
                    continue
                parts1 = lines[0][i].split(':')
                parts2 = lines[1][i].split(':')
                if len(parts1) < 3 or len(parts2) < 3 or parts1[0] != parts2[0]:
                    logger.error("something is wrong in profile generation")
                    raise Exception
                    return False
                profile_dict[parts1[0]] = (''.join(parts1[1:-1]), ''.join(parts2[1:-1]))
                logger.debug("Profile generated from this test: %s" % pt)
            profile_dict['console'] = ('""', '"' + console_output[:20] + '"')
            input_list.append(profile_dict)
        logger.debug(self.input_list)
        return True

    def generate_gdb_script(self, positive_tests, input_list):
        """
        An effort to create profile with the help of gdb (does not work on large programs)
        :param positive_tests:
        :param input_list:
        :return:
        """
        res = run_command_with_timeout(COMPILE_SCRIPT, timeout=70)
        if not res:
            logger.error("the gdb profile is not compilable")
            return False
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

        for pt in positive_tests:
            states = []
            with open('gdb_script.txt', 'w') as f:
                f.write(file_and_breaks)
                f.write('set args ' + TEST_SCRIPT + ' ' + pt + '\n')
                f.write('command 1\n' + vars + 'continue\nend\n')
                f.write('command 2\n' + vars + 'quit\nend\n')
                f.write('run\n')
            res = run_command('gdb --command=gdb_script.txt > gdb_out')
            if not res:
                logger.warning("cannot run gdb")
                continue
            with open('gdb_out', 'r') as f:
                for l in f:
                    if l.startswith('$'):
                        parts = l[1:].split('=')
                        if len(parts) != 2:
                            logger.warning("something is wrong")
                            continue
                        try:
                            i = int(parts[0])
                        except:
                            logger.warning("something is wrong")
                            continue
                        string_index = parts[1].strip().find('"')
                        if string_index != -1: # it's a string
                            states.append(parts[1].strip()[string_index+1:parts[1].strip().rfind('"')])
                        else:
                            states.append(parts[1].strip())  # TODO strip for Strings?
            if len(states) != len(self.suspicious_block.vars)*2:
                logger.warning("not enough output")
                continue
            profile_dict = {}
            for i in range(len(states)/2):
                profile_dict[self.suspicious_block.vars[i][0]] = (states[i], states[i+len(self.suspicious_block.vars)])
            input_list.append(profile_dict)
        print input_list
        os.system('rm gdb_script.txt gdb_out')
        return True




