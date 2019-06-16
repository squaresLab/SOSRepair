__author__ = 'afsoona'

import argparse
import os
import re
import time
import fnmatch
import random
import hashlib
import logging
from settings import *
from profile.profile import *
from profile.tests import *
from fault_localization.suspicious_lines import *
from repository.snippet_preparation import *
from repository.db_manager import DatabaseManager
from repository.smt_solver import Z3
from repository.patch_generation import PatchGeneration
from utils.file_process import transform_file, get_file_name_and_module_re

logger = logging.getLogger(__name__)


class MainReturn(object):
    Patch_found = 0
    No_positive_tests = 1
    No_negative_tests = 2
    Patch_not_found = 3


def re_build_database(db_manager):
    start_time = time.time()
    db_manager.drop_tables()
    db_manager.initialize_tables()
    if SOSREPAIR:
        deletion_snippet = CodeSnippet('', [], {}, '', [])
        deletion_snippet.add_constraint('(assert true)')
        db_manager.insert_snippet(deletion_snippet)
        del deletion_snippet
    with open("processed.txt", "w") as f:
        for root, dirs, files in os.walk(GENERATE_DB_PATH):
            for items in sorted(fnmatch.filter(files, "*.c")):
                ff = os.path.join(root, items)
                f.write("Start: %s\n" % str(ff))
                ff = transform_file(ff)
                fl = CodeSnippetManager(ff, db_manager)
                fl.detach_snippets()
                os.system('rm ' + ff)
                f.write("Finished\n")
                f.write("Total time: %f\n" % (time.time() - start_time))
    logger.info('Total time: %f' % (time.time() - start_time))


def main(build_db=False, all_patches=False):
    logger.info('***************************** %s' % FAULTY_CODE)
    original_copy = FAULTY_CODE + '_orig.c'
    run_command('cp ' + FAULTY_CODE + ' ' + original_copy)

    tests = Tests()
    tests.initialize_script_testing()
    logger.debug('Tests %s' % str(tests))
    if len(tests.positives) == 0:
        print "No positive test!"
        return MainReturn.No_positive_tests
    if len(tests.negatives) == 0:
        print "Passes all tests"
        return MainReturn.No_negative_tests

    suspicious_lines = SuspiciousLines(tests)
    suspicious_lines.compute_suspiciousness()

    logger.debug("Suspicious lines : %s" % str(suspicious_lines.suspiciousness))
    db_manager = DatabaseManager()
    if build_db:
        re_build_database(db_manager)

    fl = FaultLocalization()

    passing_patches = []
    os.system('rm -r patches')
    os.system('mkdir patches')

    filename, module_name = get_file_name_and_module_re(FAULTY_CODE)
    stored_data = {}
    unsuccessful_lines = []
    phases = ['in_file', 'in_module', 'all']
    if not SOSREPAIR:
        phases = ['any']
    for phase in phases:
        logger.debug("Beginning of phase %s" % phase)
        investigated_blocks = set([])
        suspicious_lines_investigated = 0
        for line, score in suspicious_lines.suspiciousness:
            if not (METHOD_RANGE[0] <= line <= METHOD_RANGE[1]) or line in unsuccessful_lines:
                continue
            if suspicious_lines_investigated >= MAX_SUSPICIOUS_LINES:
                break
            logger.info("Suspicious line: %d ,score: %f" % (line, score))
            if line in stored_data:
                sb = stored_data[line]['sb']
                profile = stored_data[line]['profile']
            else:
                sb = fl.line_to_block(line)
                if not sb or sb.line_range[0] > line or sb.line_range[1] < line:
                    logger.warning("No block found for line: %d" % line)
                    unsuccessful_lines.append(line)
                    continue
                if sb.line_range in investigated_blocks:
                    unsuccessful_lines.append(line)
                    continue
                investigated_blocks.add(sb.line_range)
                logger.info("Suspicious block range %s" % str(sb.line_range))
                profile = Profile(sb)
                success = profile.generate_printing_profile(tests, original_copy)
                logger.debug('Profile: ' + str(profile.input_list))
                if not success or (not profile.input_list and not profile.negative_input_list):
                    unsuccessful_lines.append(line)
                    continue
                stored_data[line] = {'sb': sb, 'profile': profile}
            suspicious_lines_investigated += 1
            candidate_snippets_ids = db_manager.fetch_all_valid_snippets(phase, filename, module_name, sb.vars,
                                                                         sb.outputs)
            logger.debug("Candidate snippets len %d" % len(candidate_snippets_ids))
            random.shuffle(candidate_snippets_ids)
            tried_snippets = []
            z3 = Z3(sb, profile, db_manager)
            unsat = 0
            for snippet_id in candidate_snippets_ids:
                res = z3.prepare_smt_query_new_version(snippet_id)
                if not res:
                    unsat += 1
                    continue
                for source, variables, mapping in res:
                    hash_object = hashlib.sha1(re.sub('[\s+]', '', source))
                    hex_dig = hash_object.hexdigest()
                    if hex_dig in tried_snippets:
                        continue
                    tried_snippets.append(hex_dig)
                    patch_generation = PatchGeneration(source, variables, mapping)
                    patch_generation.prepare_snippet_to_parse()
                    ast = patch_generation.parse_snippet()
                    patch_snippet = patch_generation.replace_vars(ast)
                    patch_file = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                              'patches/patch' + str(len(passing_patches)) + '.c')
                    patch_file = patch_generation.create_patch(sb, patch_snippet, patch_file=patch_file)
                    run_command('cp ' + patch_file + ' ' + FAULTY_CODE)
                    for i in range(NUMBER_OF_TIMES_RERUNNING_TESTS):
                        success = tests.rerun_tests()
                        if not success:
                            break
                        logger.debug("Passed all tests %d times" % (i+1))
                    if success:
                        print "Found a patch!!! YAY"
                        logger.info("Found a patch!!! YAY")
                        run_command('cp ' + original_copy + ' ' + FAULTY_CODE)
                        passing_patches.append(patch_file)
                        if not all_patches:
                            return MainReturn.Patch_found
                        break
                    elif len(profile.input_list) == 0 and SOSREPAIR:
                        profile.update_profile(tests, original_copy)
                        logger.debug('Updated profile: ' + str(profile.negative_input_list))
                    run_command('cp ' + original_copy + ' ' + FAULTY_CODE)
            logger.debug("total %d were unsatisfiable from %d" % (unsat, len(candidate_snippets_ids)))
    if not SOSREPAIR:
        return MainReturn.Patch_not_found if len(passing_patches) == 0 else MainReturn.Patch_found
    logger.info("Entering insertion")
    stored_data = {}
    unsuccessful_lines = []
    run_command('cp ' + original_copy + ' ' + original_copy + '_copy')
    for phase in phases:
        investigated_blocks = set([])
        suspicious_lines_investigated = 0
        for line, score in suspicious_lines.suspiciousness:  # Try insertion
            if not (METHOD_RANGE[0] <= line <= METHOD_RANGE[1]) or line in unsuccessful_lines:
                continue
            if suspicious_lines_investigated >= MAX_SUSPICIOUS_LINES:
                break
            with open(original_copy + '_copy', 'r') as AA:
                i = 1
                with open(original_copy, 'w') as BB:
                    for LL in AA:
                        if i == line:
                            BB.write('\n')
                        BB.write(LL)
                        i += 1
            run_command('cp ' + original_copy + ' ' + FAULTY_CODE)
            logger.info("Suspicious line: %d ,score: %f" % (line, score))
            if line in stored_data:
                sb = stored_data[line]['sb']
                profile = stored_data[line]['profile']
            else:
                sb = fl.line_to_insert(line)
                if not sb or sb.line_range[0] > line or sb.line_range[1] < line:
                    logger.warning("No block found for line: %d" % line)
                    unsuccessful_lines.append(line)
                    continue
                if sb.line_range in investigated_blocks:
                    unsuccessful_lines.append(line)
                    continue
                investigated_blocks.add(sb.line_range)
                logger.info("Suspicious block range %s" % str(sb.line_range))
                profile = Profile(sb)
                success = profile.generate_printing_profile(tests, original_copy)
                logger.debug('Profile: ' + str(profile.input_list))
                if not success or (not profile.input_list and not profile.negative_input_list):
                    unsuccessful_lines.append(line)
                    continue
                stored_data[line] = {'sb': sb, 'profile': profile}
            suspicious_lines_investigated += 1
            candidate_snippets_ids = db_manager.fetch_all_valid_snippets(phase, filename, module_name, sb.vars,
                                                                         sb.outputs)
            random.shuffle(candidate_snippets_ids)
            tried_snippets = []
            z3 = Z3(sb, profile, db_manager)
            for snippet_id in candidate_snippets_ids:
                res = z3.prepare_smt_query_new_version(snippet_id)
                if not res:
                    continue
                for source, variables, mapping in res:
                    hash_object = hashlib.sha1(re.sub('[\s+]', '', source))
                    hex_dig = hash_object.hexdigest()
                    if hex_dig in tried_snippets:
                        continue
                    tried_snippets.append(hex_dig)
                    patch_generation = PatchGeneration(source, variables, mapping)
                    patch_generation.prepare_snippet_to_parse()
                    ast = patch_generation.parse_snippet()
                    patch_snippet = patch_generation.replace_vars(ast)
                    patch_file = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                              'patches/patch' + str(len(passing_patches)) + '.c')
                    patch_file = patch_generation.create_patch(sb, patch_snippet, patch_file=patch_file)
                    run_command('cp ' + patch_file + ' ' + FAULTY_CODE)
                    for i in range(NUMBER_OF_TIMES_RERUNNING_TESTS):
                        success = tests.rerun_tests()
                        if not success:
                            break
                        logger.debug("Passed all tests %d times" % (i+1))
                    if success:
                        print "Found a patch!!! YAY"
                        logger.info("Found a patch!!! YAY")
                        run_command('cp ' + original_copy + ' ' + FAULTY_CODE)
                        passing_patches.append(patch_file)
                        if not all_patches:
                            return MainReturn.Patch_found
                        break
                    elif len(profile.input_list) == 0:
                        profile.update_profile(tests, original_copy)
                        logger.debug('Updated profile: ' + str(profile.negative_input_list))
                    run_command('cp ' + original_copy + ' ' + FAULTY_CODE)
    return MainReturn.Patch_not_found if len(passing_patches) == 0 else MainReturn.Patch_found


def bulk_running_main(all_patches=False):
    """
    This function could be used as a script to run SearchRepair on many programs
    in sequence
    """

    success_file = open('success.txt', 'w')
    failed_file = open('failed.txt', 'w')
    exception = open('exception.txt', 'w')
    os.system('rm -r ' + BULK_RUN_PATH + '/patches')
    os.system('mkdir ' + BULK_RUN_PATH + '/patches')
    index = 0

    for root, dirs, files in os.walk(GENERATE_DB_PATH):
        for items in fnmatch.filter(files, "*.c"):
            ff = os.path.join(root, items)
            logger.info("File: " + ff)
            try:
                os.system('cp ' + ff + ' ' + BULK_RUN_PATH)
                res = main(build_db=False, all_patches=all_patches)
                if res == MainReturn.Patch_found:
                    success_file.write(ff + '\n')
                    success_file.flush()
                    os.system('cp patches/patch0.c ' + BULK_RUN_PATH + '/patches/patch.c' + str(index))
                    index += 1
                elif res == MainReturn.No_positive_tests:
                    exception.write(ff + ':No positive tests\n')
                    exception.flush()
                elif res == MainReturn.No_negative_tests:
                    exception.write(ff + ':Already correct\n')
                    exception.flush()
                elif res == MainReturn.Patch_not_found:
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
    parser = argparse.ArgumentParser(description="SOSRepair automatic program repair tool")
    parser.add_argument("--db", choices=["none", "build_and_run", "build"],
                        default="none", help="Specify whether the DB should be built")
    parser.add_argument("--run_mode", choices=["normal", "bulk_run"],
                        default="normal", help="The running mode")
    parser.add_argument("--all_patches", action="store_true",
                        help="Find all patches")
    parser.add_argument("--seed", type=int,
                        default=1000, help="Random seed")
    args = parser.parse_args()
    random.seed(args.seed)
    start_time = time.time()
    logger.info("Start time %s" % str(start_time))

    if args.db == "build":
        db_manager = DatabaseManager()
        re_build_database(db_manager)
    elif args.run_mode == "normal":
        if args.db == "none":
            main(build_db=False, all_patches=args.all_patches)
        elif args.db == "build_and_run":
            main(build_db=True, all_patches=args.all_patches)
    elif args.run_mode == "bulk_run":
        if args.db == "none":
            bulk_running_main(all_patches=args.all_patches)
        elif args.db == "build_and_run":
            db_manager = DatabaseManager()
            re_build_database(db_manager)
            bulk_running_main(all_patches=args.all_patches)
    #main()
    logger.info("Total time %s" % str((time.time() - start_time)))
    # db_manager = DatabaseManager()
    # re_build_database(db_manager)
