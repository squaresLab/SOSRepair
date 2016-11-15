__author__ = 'Afsoon Afzal'

import logging
from clang.cindex import *
from clang.cindex import BinaryOperator
from settings import *
from utils.file_process import number_of_lines
from repository.snippet_preparation import CodeSnippetManager

Config.set_library_file(LIBCLANG_PATH)
logger = logging.getLogger(__name__)


class SuspiciousBlock():
    def __init__(self, line_number, line_range, blocks, vars, outputs, functions, filename):
        self.line_number = line_number
        self.line_range = line_range
        self.column_range = (blocks[0].extent.start.column-1, blocks[-1].extent.end.column) if blocks else (0, 1)
        self.blocks = blocks
        self.vars = vars
        self.outputs = outputs
        self.functions = functions
        self.filename = filename

    def get_output_names(self):
        if isinstance(self.outputs, dict):
            return [i for i in self.outputs.keys()]
        else:
            return []

    def get_var_names(self):
        return [i[0] for i in self.vars]


class FaultLocalization():
    def __init__(self):
        self.filename = FAULTY_CODE
        self.number_of_lines = number_of_lines(FAULTY_CODE)
        self.root = None

    def line_to_block(self, line_number):
        index = Index.create()
        logger.info("parsing")
        self.root = index.parse(self.filename)
        logger.info("parsing root")
        return self.traverse_tree_suspicious_block(self.root.cursor, self.number_of_lines, line_number)

    def traverse_tree(self, line_number, ast):
        assert (isinstance(ast, Cursor))
        block = (1, 10000000)
        current = ast
        children = ast.get_children()
        function = None
        cond = True
        while cond:
            for child in children:
                cond = True
                if str(child.location.file) != self.filename:
                    continue
                # print block
                # print str(child.spelling) + " " + str(child.location.file)
                # print child.location.line
                if child.location.line > line_number:
                    temp_block = (current.location.line, child.location.line)
                    if current.kind == CursorKind.IF_STMT:
                        cond = False
                    elif temp_block[1] - temp_block[0] < 4:
                        cond = False
                        if block[1] - block[0] > 6:
                            block = (temp_block[1] - 6, temp_block[1])
                        break
                    block = temp_block
                    break
                current = child
                if child.kind == CursorKind.FUNCTION_DECL:
                    function = child
            children = current.get_children()

        return SuspiciousBlock(line_number, block, current, function)

    def traverse_tree_suspicious_block(self, ast, end_of_file, line_number):
        assert (isinstance(ast, Cursor))
        from_line = -1
        blocks = []
        children = list(ast.get_children())
        children.append(end_of_file)
        for child in children:
            cursor = False
            if isinstance(child, Cursor):
                cursor = True
            if cursor and (str(child.location.file) != self.filename or child.kind == CursorKind.DECL_STMT):
                continue
            line = child.location.line if cursor else child
            # print line
            if from_line < 0:
                from_line = line
                blocks.append(child)
                continue
            if line <= line_number:
                blocks.append(child)
                continue
            dist = line - from_line
            generate_block = False
            if dist > LARGEST_SNIPPET:
                while (line - from_line) > LARGEST_SNIPPET:
                    logger.debug("line: %d, from_line: %d" % (line, from_line))
                    logger.debug("block0: %s" % str(blocks[0].kind))
                    if len(blocks) == 1:  # means it's a large block
                        return self.traverse_tree_suspicious_block(blocks[0], line, line_number)
                    else:
                        if len(blocks) > 1 and blocks[1].location.line <= line_number:
                            blocks.pop(0)
                            from_line = blocks[0].location.line
                        else:
                            generate_block = True
                            break
            if generate_block or (LARGEST_SNIPPET >= (line - from_line) >= SMALLEST_SNIPPET and line >= line_number >= from_line):
                while len(blocks) > 1 and blocks[1].location.line < line_number and \
                                        LARGEST_SNIPPET >= (line - blocks[1].location.line) >= SMALLEST_SNIPPET:
                    blocks.pop(0)
                    from_line = blocks[0].location.line
                vars, labels = CodeSnippetManager.find_vars(blocks)
                outputs = CodeSnippetManager.find_outputs(blocks)
                if vars != -1 and outputs != -1:
                    func_calls = CodeSnippetManager.find_function_calls(blocks, vars)
                    sb = SuspiciousBlock(line_number, (from_line, line), blocks, vars, outputs, func_calls, self.filename)
                    return sb
                return None
            if cursor:
                blocks.append(child)
                from_line = blocks[0].location.line
        return None

    def line_to_insert(self, line_number):
        function = self.find_function_of_this_line(line_number)
        live_vars = self.find_live_variables(function, line_number)
        outputs = {}
        for v in live_vars:
            if len(v) == 2:
                outputs[v[0]] = {'type': v[1]}
            else:
                outputs[v[0]] = {'type': v[1], 'declaration': v[2]}
        return SuspiciousBlock(line_number, (line_number, line_number+1), [], list(live_vars), outputs, [], self.filename)

    def find_function_of_this_line(self, line_number):
        if not self.root:
            index = Index.create()
            self.root = index.parse(self.filename)
        ast = self.root.cursor
        current = ast
        children = ast.get_children()
        function = None
        cond = True
        while cond:
            cond = False
            for child in children:
                cond = True
                if str(child.location.file) != self.filename:
                    continue
                if child.location.line > line_number:
                    break
                current = child
                if child.kind == CursorKind.FUNCTION_DECL:
                    function = child
            children = current.get_children()
        return function

    @staticmethod
    def find_live_variables(function, line):
        final_list = set([])
        all_vars = set([])
        live_vars = set([])
        dead_vars = set([])
        for cursor in function.walk_preorder():
            if cursor.location.line < line and cursor.kind == CursorKind.PARM_DECL or cursor.kind == CursorKind.VAR_DECL:
                all_vars.add(str(cursor.displayname))
            if cursor.location.line >= line and (cursor.kind == CursorKind.DECL_REF_EXPR or cursor.kind == CursorKind.UNEXPOSED_EXPR) \
                    and str(cursor.displayname) not in dead_vars and str(cursor.displayname) in all_vars:
                live_vars.add(str(cursor.displayname))
                res = CodeSnippetManager.find_type_and_add(final_list, cursor)
                # if not res:
                #     return False
            if cursor.location.line >= line and (cursor.kind == CursorKind.BINARY_OPERATOR and
                                                 cursor.binary_operator == BinaryOperator.Assign):
                left_side = None
                visited = []
                for node in cursor.walk_preorder():
                    if node.hash in visited:
                        continue
                    if node.kind == CursorKind.DECL_REF_EXPR or node.kind == CursorKind.UNEXPOSED_EXPR:
                        if not left_side:
                            left_side = str(node.displayname)
                        elif str(node.displayname) not in dead_vars and str(node.displayname) in all_vars:
                            live_vars.add(str(node.displayname))
                            CodeSnippetManager.find_type_and_add(final_list, node)
                    elif not left_side and node.kind == CursorKind.MEMBER_REF_EXPR:
                        for inner in node.walk_preorder():
                            visited.append(inner.hash)
                            if inner.kind == CursorKind.DECL_REF_EXPR or inner.kind == CursorKind.UNEXPOSED_EXPR:
                                left_side = str(inner.displayname)
                if left_side not in live_vars and left_side in all_vars:
                    dead_vars.add(left_side)
        return final_list


if __name__ == "__main__":
    fl = FaultLocalization('src/fdevent_freebsd_kqueue.c')
    sb = fl.line_to_block(57)
    print str(sb.block) + " " + str(sb.node.kind) + " " + str(sb.node.type.kind) + " " + str(sb.function.spelling)
