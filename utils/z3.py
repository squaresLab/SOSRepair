__author__ = 'Afsoon Afzal'

import subprocess
import os
from settings import Z3_COMMAND


def run_z3(query):
    ret = False
    with open('z3_query.smt2', 'w') as f:
        f.write(query)
        f.flush()
        proc = subprocess.Popen(Z3_COMMAND + ' -smt2 z3_query.smt2', stdout=subprocess.PIPE, shell=True)
        (out, err) = proc.communicate()
        print "**** " + out
        if err:
            print "ERROR: z3"
        for l in out.splitlines():
            if l == 'sat':
                ret = True
            elif l == 'unsat':
                ret = False
    os.system('rm z3_query.smt2')
    return ret
