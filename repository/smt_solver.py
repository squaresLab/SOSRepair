__author__ = 'Afsoon Afzal'

import logging
from itertools import permutations, product
from utils.z3 import run_z3, twos_comp
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

    def prepare_smt_query_new_version(self, index):
        snippet = self.db_manager.fetch_snippet(index)
        constraints = self.db_manager.fetch_constraints(index)
        if len(constraints) < 1 or not snippet:
            logger.error("ERROR no constraints or snippet for this id %d" % index)
            return None
        snippet_variables = [i[0] for i in eval(snippet[2])]
        snippet_outputs = eval(snippet[3])
        consts = '(assert ' + self.prepare_constraints(constraints) + '\n'
        if isinstance(snippet_outputs, dict):
            snippet_outputs = [i for i in snippet_outputs.keys()]
        else:
            snippet_outputs = []
        query, get_value = self.prepare_declarations_new_version(snippet_variables, snippet_outputs)
        num = 0
        for profile in self.profile.input_list:
            query += self.replace_variable_names(num, consts, snippet_variables, snippet_outputs)
            for v, t in self.suspicious_block.vars:
                if t != 'char *':
                    query += '(assert (let ' + self.get_let_statement(v + '_in_' + str(num)) + '(= ?A1 (_ bv' + self.proper_value(profile[v][0], t) + \
                                ' 32) ) ) ) \n'
                else:
                    query += self.get_string_mapping(profile[v][0], v + '_in_' + str(num))
            if isinstance(self.suspicious_block.outputs, dict):
                for v in self.suspicious_block.outputs.keys():
                    t = self.suspicious_block.outputs[v]['type']
                    if t != 'char *':
                        query += '(assert (let ' + self.get_let_statement(v + '_out_' + str(num)) + '(= ?A1 (_ bv' + self.proper_value(profile[v][1], t) + \
                                    ' 32) ) ) ) \n'
                    else:
                        query += self.get_string_mapping(profile[v][1], v + '_out_' + str(num))
            num += 1
        query += '(check-sat)\n(get-value ('
        query += ' '.join(get_value) + ') )\n'
        print query
        satisfied = run_z3(query)
        print satisfied
        raise Exception

    def prepare_smt_query(self, index):
        result = []
        snippet = self.db_manager.fetch_snippet(index)
        constraints = self.db_manager.fetch_constraints(index)
        if len(constraints) < 1 or not snippet:
            logger.error("ERROR no constraints or snippet for this id %d" % index)
            return None
        decls = self.prepare_declarations(constraints)
        consts = '(assert ' + self.prepare_constraints(constraints)
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
            if not self.is_valid_mapping(r, eval(snippet[2]), self.suspicious_block.vars, eval(snippet[3]),\
                                         self.suspicious_block.outputs):
                logger.debug("Not a valid mapping %s" % str(r))
                continue
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
                    if t != 'char *':
                        mappings += '(assert (let ' + self.get_let_statement(v + '_in') + '(= ?A1 (_ bv' + self.proper_value(profile[v][0], t) + \
                                    ' 32) ) ) ) \n'
                    else:
                        mappings += self.get_string_mapping(profile[v][0], v + '_in')
                if isinstance(self.suspicious_block.outputs, dict):
                    for v in self.suspicious_block.outputs.keys():
                        t = self.suspicious_block.outputs[v]['type']
                        if t != 'char *':
                            mappings += '(assert (let ' + self.get_let_statement(v + '_out') + '(= ?A1 (_ bv' + self.proper_value(profile[v][1], t) + \
                                        ' 32) ) ) ) \n'
                        else:
                            mappings += self.get_string_mapping(profile[v][1], v + '_out')
                # TODO deal with single output
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

    def prepare_declarations_new_version(self, snippet_vars, snippet_outputs):
        declarations = ''
        constraints = ''
        for i in range(len(self.profile.input_list)):
            for v, t in self.suspicious_block.vars:
                declarations += '(declare-fun %s_in_%d () (Array (_ BitVec 32) (_ BitVec 8) ) )\n' % (v, i)
            for v in snippet_vars:
                declarations += '(declare-fun %s_%d () (Array (_ BitVec 32) (_ BitVec 8) ) )\n' % (v, i)
            if isinstance(self.suspicious_block.outputs, dict):
                for v in self.suspicious_block.outputs.keys():
                    declarations += '(declare-fun %s_out_%d () (Array (_ BitVec 32) (_ BitVec 8) ) )\n' % (v, i)
            for v in snippet_outputs:
                declarations += '(declare-fun %s_ret_%d () (Array (_ BitVec 32) (_ BitVec 8) ) )\n' % (v, i)

        get_value = []
        # well-formed
        snippet_variables = list(set(snippet_vars) - set(snippet_outputs))
        code_variables = list(set(self.suspicious_block.get_var_names()) - set(self.suspicious_block.get_output_names()))
        constraints += '(assert (and '
        i = 0
        for v in code_variables:
            declarations += '(declare-const l_%s_in Int)\n' % v
            constraints += '(= l_%s_in %d) ' % (v, i)
            i += 1
        for v in snippet_variables:
            declarations += '(declare-const l_%s Int)\n' % v
            constraints += '(<= 0 l_%s) (< l_%s %d) ' % (v, v, len(snippet_variables))
            get_value.append('l_%s' % v)
        for v in self.suspicious_block.get_output_names():
            declarations += '(declare-const l_%s_out Int)\n' % v
            constraints += '(= l_%s_out %d) ' % (v, i)
            i += 1
        for v in snippet_outputs:
            declarations += '(declare-const l_%s_ret Int)\n' % v
            constraints += '(<= %d l_%s_ret) (< l_%s_ret %d) ' % (len(snippet_variables), v, v, len(snippet_variables)+len(snippet_outputs))
            get_value.append('l_%s_ret' % v)
        constraints += '))\n(assert (and '
        for v in code_variables:
            for sv in snippet_variables:
                constraints += '(=> (= l_%s_in l_%s) (and ' % (v, sv)
                constraints += ''.join(['(= %s_in_%d %s_%d) ' % (v, i, sv, i) for i in range(len(self.profile.input_list))])
                constraints += ') ) '
        for v in snippet_outputs:
            for pv in self.suspicious_block.outputs.keys():
                constraints += '(=> (= l_%s_out l_%s_ret) (and ' % (pv, v)
                constraints += ''.join(['(= %(pv)s_out_%(i)d %(v)s_ret_%(i)d) (= %(pv)s_in_%(i)d %(v)s_%(i)d) '
                                        % {'pv': pv, 'v': v, 'i': i} for i in range(len(self.profile.input_list))])
                constraints += ') ) '
        constraints += ') )\n'

        constraints += '(assert (= %d (+ ' % sum(range(len(snippet_variables))) + \
                       ' '.join(['l_%s' % s for s in snippet_variables]) + ') ) )\n'
        constraints += '(assert (= %d (+ ' % sum(range(len(snippet_variables), len(snippet_variables)+len(snippet_outputs))) + \
                       ' '.join(['l_%s_ret' % s for s in snippet_outputs]) + ') ) )\n'

        return declarations + constraints, get_value

    @staticmethod
    def proper_value(value, typ):
        if typ not in ['int', 'long', 'short']:
            return value
        try:
            i = int(value)
            if i < 0:
                v = twos_comp(i, 32)
                return str(v + 1)
            return value
        except:
            logger.error("Something wrong in smt encoding %s" % value)
            return value

    @staticmethod
    def prepare_constraints(constraints):
        s = '(or ' * (len(constraints) - 1)
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

    @staticmethod
    def is_valid_mapping(mapping, snippet_vars, code_vars, snippet_outs, code_outs):
        s_dict = dict(snippet_vars)
        c_dict = dict(code_vars)
        for a, b in mapping[0]:
            if s_dict[a] != c_dict[b]:
                return False
        if not isinstance(snippet_outs, dict) or not isinstance(code_outs, dict):
            return True
        for a, b in mapping[1]:
            if snippet_outs[a]['type'] != code_outs[b]['type']:
                return False
        return True

    @staticmethod
    def get_string_mapping(string, variable):
        if len(string) == 0:
            return ''
        query = '(assert '
        for i in range(len(string)):
            query += '(and (= (select %s (_ bv%d 32) ) (_ bv%d 32) ) ' % (variable, i, ord(string[i]))
        query += ') '*(len(string)+1)
        query += '\n'
        return query

    @staticmethod
    def replace_variable_names(num, constraint, variables, outputs):
        replaced = constraint
        for v in variables:
            replaced = replaced.replace(' %s ' % v, ' %s_%d ' % (v, num))
            replaced = replaced.replace('(%s)' % v, '(%s_%d)' % (v, num))
        for o in outputs:
            replaced = replaced.replace(' %s_ret ' % o, ' %s_ret_%d ' % (v, num))
            replaced = replaced.replace('(%s_ret)' % o, '(%s_ret_%d)' % (v, num))
        return replaced
