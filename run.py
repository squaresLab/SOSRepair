__author__ = 'afsoona'

import os
import fnmatch
from settings import INTROCLASS_PATH
from profile.profile import *
from profile.tests import *
from fault_localization.suspicious_lines import *
from repository.snippet_preparation import *
from repository.db_manager import DatabaseManager
from repository.smt_solver import Z3
from repository.patch_generation import PatchGeneration

# if __name__ == "__main__":
#     fl = FaultLocalization('src/fdevent_freebsd_kqueue.c')
#     sb = fl.line_to_block(57)
#     print str(sb.block) + " " + str(sb.node.kind) + " " + str(sb.node.type.kind) + " " + str(sb.function.spelling)


if __name__ == "__main2__":
    fl = FaultLocalization('median.c')
    sb = fl.line_to_block(19)
    print sb.line_range
    print sb.vars
    print sb.outputs
    profile = Profile('median.c', sb)
    # profile.find_variables()
    profile.generate_file()

    tests = Tests('', 'median.c')
    tests.initialize_testing()

    profile.generate_profile(tests.positives)

    sl = SuspiciousLines('median.c', '', tests)
    sl.compute_suspiciousness()

    profile.generate_profile(tests.positives)
    print tests

if __name__ == "__main1__":
    fl = CodeSnippetManager('median.c')
    fl.detach_snippets()
    # db_manager = DatabaseManager()
    # db_manager.initialize_tables()
    # snippet = CodeSnippet('asf', [('a', 'int')], {'a': {'line': 1, 'type': 'int'}}, [('printf', 'stdio')])
    # snippet.add_constraint("ALAKI")
    # snippet.add_constraint("PALAKI")
    # snippet.add_constraint("DUMMY")
    # db_manager.insert_snippet(snippet)
    # db_manager.close()


def re_build_database(db_manager):
    db_manager.drop_tables()
    db_manager.initialize_tables()
    for root, dirs, files in os.walk(INTROCLASS_PATH):
        for items in fnmatch.filter(files, "*.c"):
            fl = CodeSnippetManager(os.path.join(root, items))
            fl.detach_snippets()

if __name__ == "__main__":
    faulty_code = 'median.c'
    tests = Tests('', faulty_code)
    tests.initialize_testing()

    suspicious_lines = SuspiciousLines(faulty_code, '', tests)
    suspicious_lines.compute_suspiciousness()

    db_manager = DatabaseManager()
    # re_build_database(db_manager)

    fl = FaultLocalization(faulty_code)

    patch_found = False
    for line, score in suspicious_lines.suspiciousness:
        sb = fl.line_to_block(line)
        profile = Profile(faulty_code, sb)
        profile.generate_file()
        success = profile.generate_profile(tests.positives)
        if not success:
            continue

        z3 = Z3(sb, profile, db_manager)
        i = z3.fetch_valid_snippets()
        while i:
            res = z3.prepare_smt_query(i)
            for source, variables, mapping in res:
                patch_generation = PatchGeneration(source, variables, mapping)
                patch_generation.prepare_snippet_to_parse()
                ast = patch_generation.parse_snippet()
                patch_snippet = patch_generation.replace_vars(ast)
                patch_file = patch_generation.create_patch(sb, patch_snippet)
                patch_test = Tests('', patch_file)
                success = patch_test.initialize_testing()
                if success and len(patch_test.negatives) == 0:
                    print "Found a patch!!! YAY"
                    patch_found = True
                    break
            i = z3.fetch_valid_snippets()
        if patch_found:
            break

