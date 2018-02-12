#!/usr/bin/env python3
import os
from subprocess import check_output, check_call
from shutil import copyfile


def find_library(name, resolve_links=True):
    """
    Finds the location of a given library.
    """
    cmd = "find . -name '{}'".format(name)
    out = check_output(cmd, shell=True).decode('utf-8').strip()
    try:
        location = out.split('\n')[0][1:]
        print("Found library '{}' at '{}'".format(name, location))
        if resolve_links:
            location = os.path.realpath(location)
        return location
    except IndexError:
        raise Exception("failed to find library: {}".format(name))


def needed_interpreter(binary_path):
    cmd = "patchelf --print-interpreter '{}'".format(binary_path)
    interp = check_output(cmd, shell=True).decode('utf-8').strip()
    interp = os.path.basename(interp)
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

    # copy binaries
    for cp_from in binary_paths:
        cp_to = os.path.join(install_bin_path, os.path.basename(cp_from))
        print("Copied binary: {}".format(cp_from))

    # find dependencies
    libraries = set()
    for p in binary_paths:
        libraries.update(needed_libraries(p))
        libraries.add(needed_interpreter(p))

    # copy libraries
    for lib in libraries:
        cp_from = find_library(lib)
        cp_to = os.path.join(install_lib_path, lib)
        if os.path.realpath(cp_from) != os.path.realpath(cp_to):
            copyfile(cp_from, cp_to)

    # resolve symbolic links
    for alias in libraries:
        actual = os.path.basename(find_library(alias))

        if alias != actual:
            link_from = os.path.join(install_lib_path, alias)
            link_to = os.path.join(install_lib_path, actual)
            if not os.path.exists(link_to):
                os.symlink(link_from, link_to)
                print("Built sym. link: '{}' -> '{}'".format(link_from, link_to))

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
