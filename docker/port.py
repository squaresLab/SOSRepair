#!/usr/bin/env python3
#
# TODO: handle recursive links!
#   - find all dependencies recursively
#
import os
import sys
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
            points_to = os.path.realpath(location)
            if points_to != location:
                print("- '{}' resolves to '{}'".format(location, points_to))
                location = points_to
        return location
    except IndexError:
        raise Exception("failed to find library: {}".format(name))


def needed_interpreter(binary_path):
    cmd = "patchelf --print-interpreter '{}'".format(binary_path)
    interp = check_output(cmd, shell=True).decode('utf-8').strip()
    interp = os.path.basename(interp)
    print("Binary '{}' uses interpreter: '{}'".format(binary_path, interp))
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
        cp_to = os.path.join(install_lib_path, os.path.basename(cp_from))
        if os.path.realpath(cp_from) != os.path.realpath(cp_to):
            copyfile(cp_from, cp_to)

    # rebuild symbolic links
    for alias in libraries:
        actual = os.path.basename(find_library(alias))

        if alias != actual:
            link_from = os.path.join(install_lib_path, alias)
            link_to = os.path.join(install_lib_path, actual)
            if not os.path.exists(link_from):
                os.symlink(link_to, link_from)
                print("Built sym. link: '{}' -> '{}'".format(link_from, link_to))

    # fix binaries
    for old_binary_path in binary_paths:
        new_binary_path = os.path.join(install_bin_path,
                                       os.path.basename(old_binary_path))

        interpreter_name = needed_interpreter(old_binary_path)
        new_interpreter = os.path.join(install_lib_path, interpreter_name)

        # fix RPATH
        cmd = "patchelf --set-rpath '{}' '{}'".format(install_lib_path, p)
        check_call(cmd, shell=True)

        # fix interpreter and ensure it's executable
        cmd = "patchelf --set-interpreter '{}' '{}'".format(new_interpreter, p)
        check_call(cmd, shell=True)
        check_call("chmod +x '{}'".format(new_interpreter), shell=True)
        print("patched {}".format(p))


if __name__ == '__main__':
    install_path = sys.argv[1]
    binary_path = sys.argv[2]
    fix_binaries(install_path, [binary_path])
