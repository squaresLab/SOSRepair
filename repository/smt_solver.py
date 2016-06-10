__author__ = 'Afsoon Afzal'

import logging
from itertools import permutations, product
from utils.z3 import run_z3
from repository.patch_generation import PatchGeneration

logger = logging.getLogger(__name__)


class Z3:

    def __init__(self, suspicious_block, profile, db_manager):
        self.suspicious_block = suspicious_block
        self.profile = profile
        self.db_manager = db_manager
        self.last_checked = 0

    def fetch_valid_snippets(self):
        index = self.db_manager.fetch_next_valid_snippet(self.suspicious_block.vars, self.suspicious_block.outputs,
                                                         self.last_checked)
        if not index:
            return None
        self.last_checked = index
        return index

    def prepare_smt_query(self, index):
        result = []
        snippet = self.db_manager.fetch_snippet(index)
        constraints = self.db_manager.fetch_constraints(index)
        if len(constraints) < 1 or not snippet:
            logger.error("ERROR no constraints or snippet for this id %d" % index)
            return None
        decls = self.prepare_declarations(constraints)
        consts = self.prepare_constraints(constraints)
        snippet_variables = [i[0] for i in eval(snippet[2])]
        snippet_outputs = eval(snippet[3])
        if isinstance(snippet_outputs, dict):
            snippet_outputs = [i for i in snippet_outputs.keys()]
        else:
            snippet_outputs = []
        output_permutations = [list(zip(snippet_outputs, p)) for p in permutations(self.suspicious_block.get_output_names())]
        if len(output_permutations) == 0:
            output_permutations = [None]
        snippet_variables = list(set(snippet_variables) - set(snippet_outputs))
        code_variables = list(set(self.suspicious_block.get_var_names()) - set(self.suspicious_block.get_output_names()))
        variable_permutations = [list(zip(snippet_variables, p)) for p in permutations(code_variables)]
        if len(variable_permutations) == 0:
            variable_permutations = [None]
        for r in product(variable_permutations, output_permutations):
            all_satisfied = True
            query = decls + '\n'
            query += consts + '\n'
            if r[1]:
                for a, b in r[1]:
                    query += '(assert (let ' + self.get_let_statement(b+'_out', 'A1') + '(let ' +\
                        self.get_let_statement(a+'_ret', 'A2') + '(= ?A1 ?A2) ) ) ) \n'
                    if b in self.suspicious_block.get_var_names():
                        query += '(assert (let ' + self.get_let_statement(b+'_in', 'A1') + '(let ' +\
                            self.get_let_statement(a, 'A2') + '(= ?A1 ?A2) ) ) ) \n'
            if r[0]:
                for a, b in r[0]:
                    query += '(assert (let ' + self.get_let_statement(b+'_in', 'A1') + '(let ' +\
                        self.get_let_statement(a, 'A2') + '(= ?A1 ?A2) ) ) ) \n'
            logger.debug(query)
            for profile in self.profile.input_list:
                mappings = query
                # profile = self.profile.input_list[i]
                for v, t in self.suspicious_block.vars:
                    mappings += '(assert (let ' + self.get_let_statement(v + '_in') + '(= ?A1 (_ bv' + profile[v][0] + \
                                ' 32) ) ) ) \n'
                if isinstance(self.suspicious_block.outputs, dict):
                    for v in self.suspicious_block.outputs.keys():
                        mappings += '(assert (let ' + self.get_let_statement(v + '_out') + '(= ?A1 (_ bv' + profile[v][1] + \
                                    ' 32) ) ) ) \n'
                satisfied = run_z3(mappings + '(check-sat)\n')
                if not satisfied:
                    all_satisfied = False
            if all_satisfied:
                var_mappings = dict(r[0])
                var_mappings.update(dict(r[1]))
                logger.debug(var_mappings)
                result.append((snippet[1], eval(snippet[2]), var_mappings))
                # patch_generation = PatchGeneration(snippet[1], eval(snippet[2]), var_mappings)
                # patch_generation.prepare_snippet_to_parse()
                # ast = patch_generation.parse_snippet()
                # patch_snippet = patch_generation.replace_vars(ast)
                # patch_generation.create_patch(self.suspicious_block, patch_snippet)
                # break
        return result

    def prepare_declarations(self, constraints):
        code_declarations = set([])
        constraint_declarations = set([])
        for c in constraints:
            lines = c[1].splitlines()  # Declarations of constraint
            for l in lines:
                constraint_declarations.add(l)
        for v, t in self.suspicious_block.vars:
            code_declarations.add(
                '(declare-fun ' + v + '_in () (Array (_ BitVec 32) (_ BitVec 8) ) )')  # TODO check later
        if isinstance(self.suspicious_block.outputs, dict):
            for v in self.suspicious_block.outputs.keys():
                code_declarations.add(
                    '(declare-fun ' + v + '_out () (Array (_ BitVec 32) (_ BitVec 8) ) )')  # TODO check later
                # else:
                # code_declarations.add('(declare-fun single_value_out () (Array (_ BitVec 32) (_ BitVec 8) ) )')  # TODO check later

        decls = '\n'.join(list(constraint_declarations)) + '\n' + '\n'.join(list(code_declarations))
        return decls

    @staticmethod
    def prepare_constraints(constraints):
        s = '(assert '
        s += '(or ' * (len(constraints) - 1)
        first = True
        for c in constraints:
            s += c[2]
            if first:
                first = False
            else:
                s += ') '
        s += ')'
        return s

    @staticmethod
    def get_let_statement(var_name, abbreviation='A1'):
        s = '( (?' + abbreviation + ' (concat  (select  ' + var_name + ' (_ bv3 32) ) (concat  (select  ' + var_name + \
            ' (_ bv2 32) ) (concat  (select  ' + var_name + ' (_ bv1 32) ) (select  ' + var_name + ' (_ bv0 32) ) ) ) ) ) )'
        return s
