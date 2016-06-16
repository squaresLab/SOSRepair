__author__ = 'afsoona'

import threading

kill_check = threading.Event()


def timeout(p):
        if p.poll() is None:
            try:
                p.kill()
                print 'Error: process taking too long to complete--terminating'
                kill_check.set()
            except OSError as e:
                return
