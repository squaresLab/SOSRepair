__author__ = 'afsoona'

from profile.profile import *
from profile.tests import *
from fault_localization.suspicious_lines import *
from repository.snippet_preparation import *
from repository.db_manager import DatabaseManager

# if __name__ == "__main__":
#     fl = FaultLocalization('src/fdevent_freebsd_kqueue.c')
#     sb = fl.line_to_block(57)
#     print str(sb.block) + " " + str(sb.node.kind) + " " + str(sb.node.type.kind) + " " + str(sb.function.spelling)


if __name__ == "__main__":
    fl = FaultLocalization('median.c')
    sb = fl.line_to_block(18)
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