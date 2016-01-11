__author__ = 'afsoona'

from profile.profile import *
from profile.tests import *

# if __name__ == "__main__":
#     fl = FaultLocalization('src/fdevent_freebsd_kqueue.c')
#     sb = fl.line_to_block(57)
#     print str(sb.block) + " " + str(sb.node.kind) + " " + str(sb.node.type.kind) + " " + str(sb.function.spelling)


if __name__ == "__main__":
    fl = FaultLocalization('median.c')
    sb = fl.line_to_block(19)
    profile = Profile('median.c', sb)
    profile.find_variables()
    profile.generate_file()

    tests = Tests('', 'median.c')
    tests.initialize_testing()
    print tests