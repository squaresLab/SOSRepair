__author__ = 'afsoona'

import os
import fnmatch
import logging
from settings import *
from profile.profile import *
from profile.tests import *
from fault_localization.suspicious_lines import *
from repository.snippet_preparation import *
from repository.db_manager import DatabaseManager
from repository.smt_solver import Z3
from repository.patch_generation import PatchGeneration
from utils.file_process import transform_file

logger = logging.getLogger(__name__)


def re_build_database(db_manager):
    db_manager.drop_tables()
    db_manager.initialize_tables()
    deletion_snippet = CodeSnippet('', [], {}, '', [])
    deletion_snippet.add_constraint('(assert true)')
    db_manager.insert_snippet(deletion_snippet)
    del deletion_snippet
    for root, dirs, files in os.walk(INTROCLASS_PATH):
        for items in fnmatch.filter(files, "*.c"):
            ff = os.path.join(root, items)
            ff = transform_file(ff)
            fl = CodeSnippetManager(ff)
            fl.detach_snippets()
            os.system('rm ' + ff)


def main(build_db=False):
    logger.info('***************************** %s' % FAULTY_CODE)
    # faulty_code = transform_file(FAULTY_CODE)
    original_copy = FAULTY_CODE + '_orig.c'
    run_command('cp ' + FAULTY_CODE + ' ' + original_copy)

    tests = Tests()
    tests.initialize_script_testing()
    logger.debug('Tests %s' % str(tests))
    if len(tests.positives) == 0:
        print "No positive test!"
        return 1
    if len(tests.negatives) == 0:
        print "Passes all tests"
        return 2

    suspicious_lines = SuspiciousLines(tests)
    suspicious_lines.compute_suspiciousness()

    db_manager = DatabaseManager()
    if build_db:
        re_build_database(db_manager)

    fl = FaultLocalization()

    passing_patches = []
    os.system('rm -r patches')
    os.system('mkdir patches')
    investigated_blocks = set([])
    suspicious_lines_investigated = 0
    for line, score in suspicious_lines.suspiciousness:
        if suspicious_lines_investigated >= MAX_SUSPICIOUS_LINES:
            return 4
        logger.info("Suspicious line: %d ,score: %f" % (line, score))
        sb = fl.line_to_block(line)
        if not sb or sb.line_range[0] > line or sb.line_range[1] < line:
            logger.warning("No block found for line: %d" %line)
            continue
        if sb.line_range in investigated_blocks:
            continue
        investigated_blocks.add(sb.line_range)
        logger.info("Suspicious block range %s" % str(sb.line_range))
        profile = Profile(sb)
        # profile.generate_file()
        # success = profile.generate_profile(tests.positives)
        # success = profile.generate_gdb_script(tests.positives)
        success = profile.generate_printing_profile(tests, original_copy)
        logger.debug('Profile: ' + str(profile.input_list))
        if not success:
            success = profile.generate_gdb_script(tests.negatives, profile.negative_input_list)
            logger.debug('Profile with gdb: ' + str(profile.input_list))
        if not success or (not profile.input_list and not profile.negative_input_list):
            continue

        z3 = Z3(sb, profile, db_manager)
        i = z3.fetch_valid_snippets()
        suspicious_lines_investigated += 1
        while i:
            res = z3.prepare_smt_query_new_version(i)
            if not res:
                i = z3.fetch_valid_snippets()
                continue
            for source, variables, mapping in res:
                patch_generation = PatchGeneration(source, variables, mapping)
                patch_generation.prepare_snippet_to_parse()
                ast = patch_generation.parse_snippet()
                patch_snippet = patch_generation.replace_vars(ast)
                patch_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'patches/patch'+str(len(passing_patches))+'.c')
                patch_file = patch_generation.create_patch(sb, patch_snippet, patch_file=patch_file)
                run_command('cp ' + patch_file + ' ' + FAULTY_CODE)
                patch_test = Tests()
                success = patch_test.initialize_script_testing()
                if success and len(patch_test.negatives) == 0:
                    print "Found a patch!!! YAY"
                    run_command('cp ' + original_copy + ' ' + FAULTY_CODE)
                    passing_patches.append(patch_file)
                    if not ALL_PATCHES:
                        return 0
                    break
                elif len(profile.input_list) == 0:
                    profile.update_profile(patch_test, original_copy)
                    logger.debug('Updated profile: ' + str(profile.negative_input_list))
                    run_command('cp ' + original_copy + ' ' + FAULTY_CODE)
            i = z3.fetch_valid_snippets()
    return 3


def main2():
    success_file = open('success.txt', 'w')
    failed_file = open('failed.txt', 'w')
    exception = open('exception.txt', 'w')
    first_time = False
    #s = []
    #with open('success1.txt', 'r') as f:
    #    for l in f:
    #        s.append(l)
    for root, dirs, files in os.walk(INTROCLASS_PATH):
        for items in fnmatch.filter(files, "*.c"):
            ff = os.path.join(root, items)
            logger.info("File: " + ff)
            #if ff in s:
            #    success_file.write(ff + '\n')
            #    success_file.flush()
            #    continue
            try:
                os.system('cp ' + ff + ' .')
                res = main(items, first_time)
                if res == 0:
                    success_file.write(ff + '\n')
                    success_file.flush()
                elif res == 1:
                    exception.write(ff + ':No positive tests\n')
                    exception.flush()
                elif res == 2:
                    exception.write(ff + ':Already correct\n')
                    exception.flush()
                elif res == 3:
                    failed_file.write(ff + '\n')
                    failed_file.flush()
                elif res == 4:
                    failed_file.write(ff + ':Reached max of blocks\n')
                    failed_file.flush()
                first_time = False
            except Exception as e:
                exception.write(ff + ':Exception ' + str(e) + '\n')
                exception.flush()
    success_file.close()
    failed_file.close()
    exception.close()

if __name__ == "__main__":
    main()
