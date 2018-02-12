#!/usr/bin/env python3
import os
from subprocess import check_output, check_call


def needed_interpreter(binary_path):
    cmd = "patchelf --print-interpreter '{}'".format(binary_path)
    interp = check_output(cmd, shell=True).decode('utf-8').strip()
    return interp


def needed_libraries(binary_path):
    """
    Returns the set of libraries required by a given binary.
    """
    cmd = "patchelf --print-needed '{}'".format(binary_path)
    out = check_output(cmd, shell=True).decode('utf-8')
    libs = set(l.strip() for l in out.split('\n') if l != '')
    return libs


def fix_binaries(install_path, binary_paths):
    install_lib_path = os.path.join(install_path, 'lib')
    install_bin_path = os.path.join(install_path, 'bin')

    # find dependencies and fix binaries
    dependencies = set()
    for p in binary_paths:
        dependencies.update(needed_libraries(p))
        dependencies.add(needed_interpreter(p))

    # split dependencies into sym. links and real files
    libraries = set()
    symlinks = set()
    for dep in dependencies:
        if os.path.islink(dep):
            symlinks.add(dep)
            libraries.add(os.path.realpath(dep))
        else:
            libraries.add(dep)

    print("found libraries: {}".format(libraries))
    print("found symbolic links: {}".format(symlinks))

    # copy libraries
    for cp_from in libraries:
        cp_to = os.path.join(install_lib_path,
                             os.path.basename(cp_from))

    # copy binaries
    for cp_from in binary_paths:
        cp_to = os.path.join(install_bin_path,
                             os.path.basename(cp_from))

    # reconstruct symbolic links
    for old_from in symlinks:
        old_to = os.path.realpath(dep)
        new_from = os.path.join(install_lib_path,
                                os.path.basename(old_from))
        new_to = os.path.join(install_lib_path,
                              os.path.basename(old_to))
        os.symlink(new_from, new_to)

    # fix binaries
    for old_binary_path in binary_paths:
        new_binary_path = os.path.join(install_bin_path,
                                       os.path.basename(old_binary_path))

        old_interp = needed_interpreter(old_binary_path)
        new_interp = os.path.join(install_lib_path,
                                  os.path.basename(old_interp))

        cmd = "patchelf --set-rpath '{}' --set-interpreter '{}' '{}'"
        cmd = cmd.format(install_lib_path, new_interp, p)
        check_call(cmd, shell=True)
        print("patched {}".format(p))


fix_binaries('/opt/sosrepair', ['/opt/sosrepair/bin/klee'])
