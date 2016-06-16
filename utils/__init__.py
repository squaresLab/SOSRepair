__author__ = 'afsoona'

import os
import signal
import threading

kill_check = threading.Event()


def timeout(p):
        if p.poll() is None:
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGTERM)
                print 'Error: process taking too long to complete--terminating'
                kill_check.set()
            except OSError as e:
                return
