__author__ = 'afsoona'

import os
import signal
import threading
from collections import Counter

kill_check = threading.Event()


def timeout(p):
    if p.poll() is None:
        try:
            os.killpg(os.getpgid(p.pid), signal.SIGTERM)
            print 'Error: process taking too long to complete--terminating'
            kill_check.set()
        except OSError as e:
            return


def timeout_interrupt(p):
    if p.poll() is None:
        try:
            os.killpg(os.getpgid(p.pid), signal.SIGINT)
            print 'Error: process taking too long to complete--terminating'
        except OSError as e:
            return


def counter_subset(list1, list2):
    c1, c2 = Counter(list1), Counter(list2)
    for k, n in c1.items():
        if n < c2[k]:
            return False
    for k, n in c2.items():
        if n > c1[k]:
            return False
    return True
