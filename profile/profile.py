__author__ = 'Afsoon Afzal'

from clang.cindex import *
from fault_localization.suspicious_block import FaultLocalization


class Profile():

    def __init__(self, filename, suspicious_block):
        self.filename = filename
        self.suspicious_block = suspicious_block
        self.variables = []
        self.input_list = []


    def find_variables(self):
        self.variables = []
        for i in self.suspicious_block.function.walk_preorder():
            if i.kind == CursorKind.PARM_DECL or i.kind == CursorKind.VAR_DECL:
                self.variables.append(i)
                print str(i.displayname) + " " + str(i.location.line) + " " + str(i.kind) + " " + str(i.type.kind) + " " + str(i.location.file)
        return self.variables


    def generate_file(self):
        state = 'printf("input start:'
        state_vars = ''
        for v in self.variables:
            name = v.displayname
            if v.type.kind == TypeKind.INT:
                state += name + ':%d:int_'
            elif v.type.kind == TypeKind.FLOAT or v.type.kind == TypeKind.DOUBLE:
                state += name + ':%f:float_'
            elif v.type.kind == TypeKind.CHAR_S:
                state += name + ':%d:char_'
            elif v.type.kind == TypeKind.POINTER:
                if v.type.get_pointee().kind == TypeKind.CHAR_S:
                    state += name + ':%s:char*_'
                else:
                    #TODO Pointers
                    continue
        state_vars += ', ' + name
        state += '\\n"' + state_vars + ");\n"
        i = 0
        with open(self.filename) as f:
            out = open(self.filename + "_marked.c", "w")
            for line in f:
                i += 1
                if i == self.suspicious_block.block[0] or i == self.suspicious_block.block[1]:
                    out.write(state)
                out.write(line)
            out.flush()
            out.close()


if __name__ == "__main__":
    fl = FaultLocalization('median.c')
    sb = fl.line_to_block(20)
    profile = Profile('median.c', sb)
    profile.find_variables()
    profile.generate_file()



