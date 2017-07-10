__author__ = 'Afsoon Afzal'

import logging
import re
from itertools import permutations, product
from utils.z3 import run_z3, twos_comp
from settings import VALID_TYPES

logger = logging.getLogger(__name__)


class Z3:
    """
    This class prepares an SMT query and runs Z3 on it to check if the query is satisfiable or not and also gets
    proper mapping between context variables and snippet variables.
    """
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
        """
        This functions prepares the SMT query and runs Z3. It is using location variables to run only one query.
        :param index: snippet id in the DB
        :return: The snippet and mapping if satisfiable, None if not
        """
        snippet = self.db_manager.fetch_snippet(index)
        constraints = self.db_manager.fetch_constraints(index)
        if len(constraints) < 1 or not snippet:
            logger.error("ERROR no constraints or snippet for this id %d" % index)
            return None
        snippet_variables = eval(snippet[2])
        try:
            snippet_outputs = eval(snippet[3])
        except Exception:
            snippet_outputs = snippet[3]
        if isinstance(snippet_outputs, dict):
            snippet_outputs = [i for i in snippet_outputs.keys()]
        else:
            snippet_outputs = ['return_value']
        positive = True if len(self.profile.input_list) > 0 else False
        consts = '(assert ' + self.prepare_constraints(constraints) + ')\n'
        try:
            query, get_value, program_mapping = self.prepare_declarations_new_version(snippet_variables, snippet_outputs,
                                                                                  len(self.profile.input_list) if
                                                                                  positive else len(self.profile.negative_input_list))
        except:
            return None
        if not query:
            return None
        snippet_variables = [i[0] for i in snippet_variables]
        num = 0
        if positive:
            for profile in self.profile.input_list:
                query += self.replace_variable_names(num, consts, snippet_variables, snippet_outputs)
                for var in self.suspicious_block.vars:
                    v, t = var[0], var[1]
                    if t != 'char*' and t in VALID_TYPES:
                        query += '(assert (let ' + self.get_let_statement(v + '_in_' + str(num)) + '(= ?A1 (_ bv' + \
                                 self.proper_value(profile[v][0], t) + ' 32) ) ) ) \n'
                    elif t == 'char*':
                        query += '(assert ' + self.get_string_mapping(profile[v][0], v + '_in_' + str(num)) + ')\n'
                    else:
                        query += '(assert ' + self.get_struct_mapping(profile[v][0], v + '_in_' + str(num)) + ')\n'
                if isinstance(self.suspicious_block.outputs, dict):
                    for v in self.suspicious_block.outputs.keys():
                        t = self.suspicious_block.outputs[v]['type']
                        if t != 'char*' and t in VALID_TYPES:
                            query += '(assert (let ' + self.get_let_statement(v + '_out_' + str(num)) + '(= ?A1 (_ bv' \
                                     + self.proper_value(profile[v][1], t) + ' 32) ) ) ) \n'
                        elif t == 'char*':
                            query += '(assert ' + self.get_string_mapping(profile[v][1], v + '_out_' + str(num)) + ')\n'
                        else:
                            query += '(assert ' + self.get_struct_mapping(profile[v][0], v + '_out_' + str(num)) + ')\n'
                query += '(assert ' + self.get_string_mapping(profile['console'][1], 'console_' + str(num)) + ')\n'
                num += 1
        else:
            logger.debug("We only have negative tests!")
            for profile in self.profile.negative_input_list:
                query += self.replace_variable_names(num, consts, snippet_variables, snippet_outputs)
                query += '(assert (and '
                for var in self.suspicious_block.vars:
                    v, t = var[0], var[1]
                    if t != 'char*' and t in VALID_TYPES:
                        query += '(let ' + self.get_let_statement(v + '_in_' + str(num)) + '(= ?A1 (_ bv' \
                                 + self.proper_value(profile[v][0], t) + ' 32) ) ) '
                    elif t == 'char*':
                        query += self.get_string_mapping(profile[v][0], v + '_in_' + str(num)) + ' '
                    else:
                        query += self.get_struct_mapping(profile[v][0], v + '_in_' + str(num)) + ' '
                if isinstance(self.suspicious_block.outputs, dict):
                    for v in self.suspicious_block.outputs.keys():
                        t = self.suspicious_block.outputs[v]['type']
                        if t != 'char*' and t in VALID_TYPES:
                            query += '(not (let ' + self.get_let_statement(v + '_out_' + str(num)) + '(= ?A1 (_ bv' \
                                     + self.proper_value(profile[v][1], t) + ' 32) ) ) ) '
                        elif t == 'char*':
                            query += '(not ' + self.get_string_mapping(profile[v][1], v + '_out_' + str(num)) + ' ) '
                        else:
                            query += '(not ' + self.get_struct_mapping(profile[v][1], v + '_out_' + str(num)) + ' ) '
                query += ') )\n'
                num += 1
        query += '(check-sat)\n'
        for s in get_value:
            query += '(get-value (%s))\n' % s
        print query
        logger.debug('Query: %s' % query)
        satisfied, mappings = run_z3(query)  # run Z3
        print satisfied
        print mappings
        if not satisfied:
            return None
        final_map = {}
        for v, m in mappings:
            if v == "return_value":  # For a bug, should fix it later
                continue
            final_map[v] = program_mapping[m]
        print final_map
        return [(snippet[1], eval(snippet[2]), final_map)]

    def prepare_smt_query(self, index):
        """
        This functions prepares the SMT query and runs Z3. It tries all the permutation of tests and mappings and runs
        Z3 several times.
        :param index: snippet id in the DB
        :return: The snippet and mapping if satisfiable, None if not
        """
        result = []
        snippet = self.db_manager.fetch_snippet(index)
        constraints = self.db_manager.fetch_constraints(index)
        if len(constraints) < 1 or not snippet:
            logger.error("ERROR no constraints or snippet for this id %d" % index)
            return None
        decls = self.prepare_declarations(constraints)
        consts = '(assert ' + self.prepare_constraints(constraints) + ')'
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
                        mappings += '(assert ' + self.get_string_mapping(profile[v][0], v + '_in') + ')\n'
                if isinstance(self.suspicious_block.outputs, dict):
                    for v in self.suspicious_block.outputs.keys():
                        t = self.suspicious_block.outputs[v]['type']
                        if t != 'char *':
                            mappings += '(assert (let ' + self.get_let_statement(v + '_out') + '(= ?A1 (_ bv' + self.proper_value(profile[v][1], t) + \
                                        ' 32) ) ) ) \n'
                        else:
                            mappings += 'assert ' + self.get_string_mapping(profile[v][1], v + '_out') + ')\n'
                # TODO deal with single output
                satisfied = run_z3(mappings + '(check-sat)\n')
                if not satisfied:
                    all_satisfied = False
            if all_satisfied:
                var_mappings = dict(r[0])
                var_mappings.update(dict(r[1]))
                logger.debug(var_mappings)
                result.append((snippet[1], eval(snippet[2]), var_mappings))
        return result

    def prepare_declarations(self, constraints):
        """
        Prepares declarations at the beginning of the query for the old version
        """
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

    def prepare_declarations_new_version(self, snippet_vars_input, snippet_outputs, number_of_profiles):
        """
        Prepares declarations at the beginning of the query for the new version. Defines location variables and
        expressions and declares variables once for each test (or profile element).
        """
        snippet_vars = [i[0] for i in snippet_vars_input]
        declarations = ''
        constraints = ''
        for i in range(number_of_profiles):
            for var in self.suspicious_block.vars:
                v, t = var[0], var[1]
                declarations += '(declare-fun %s_in_%d () (Array (_ BitVec 32) (_ BitVec 8) ) )\n' % (v, i)
            for v in snippet_vars:
                declarations += '(declare-fun %s_%d () (Array (_ BitVec 32) (_ BitVec 8) ) )\n' % (v, i)
            if isinstance(self.suspicious_block.outputs, dict):
                for v in self.suspicious_block.outputs.keys():
                    declarations += '(declare-fun %s_out_%d () (Array (_ BitVec 32) (_ BitVec 8) ) )\n' % (v, i)
            for v in snippet_outputs:
                declarations += '(declare-fun %s_ret_%d () (Array (_ BitVec 32) (_ BitVec 8) ) )\n' % (v, i)

        get_value = []
        mapping = {}
        # well-formed
        snippet_variables = list(set(snippet_vars) - set(snippet_outputs))
        code_variables = list(set(self.suspicious_block.get_var_names()) - set(self.suspicious_block.get_output_names()))
        types = {}
        types_out = {}
        code_vars_dict = {}
        for v in self.suspicious_block.vars:
            code_vars_dict[v[0]] = re.sub('[\s+]', '', v[1])
        # print "Vars: %s" % str(snippet_vars)
        snippet_vars_dict = {}
        for v in snippet_vars_input:
            snippet_vars_dict[v[0]] = re.sub('[\s+]', '', v[1])
        constraints += '(assert (and '
        i = 0
        logger.debug("code_vars %s, snippet vars: %s" % (str(code_vars_dict), str(snippet_vars_dict)))
        for v in code_variables:
            declarations += '(declare-const l_%s_in Int)\n' % v
            constraints += '(= l_%s_in %d) ' % (v, i)
            mapping[i] = v
            if not re.sub('[\s+]', '', code_vars_dict[v]) in types:
                types[re.sub('[\s+]', '', code_vars_dict[v])] = [i, ]
            else:
                types[re.sub('[\s+]', '', code_vars_dict[v])].append(i)
            i += 1
        for v in self.suspicious_block.get_output_names():
            declarations += '(declare-const l_%s_out Int)\n' % v
            constraints += '(= l_%s_out %d) ' % (v, i)
            mapping[i] = v
            if not v in code_vars_dict:
                logger.error("FIXME!!! %s %s" %(str(self.suspicious_block.vars),str(self.suspicious_block.get_output_names())))
                return None, None, None
            if not re.sub('[\s+]', '', code_vars_dict[v]) in types_out:
                types_out[re.sub('[\s+]', '', code_vars_dict[v])] = [i, ]
            else:
                types_out[re.sub('[\s+]', '', code_vars_dict[v])].append(i)
            i += 1
        logger.debug('Types %s' % str(types))
        for v in snippet_variables:
            declarations += '(declare-const l_%s Int)\n' % v
            if len(types[re.sub('[\s+]', '', snippet_vars_dict[v])]) == 1:
                constraints += '(= %d l_%s)' % (types[re.sub('[\s+]', '', snippet_vars_dict[v])][0], v)
            else:
                constraints += '(or ' + ' '.join(['(= %d l_%s)' % (i, v) for i in types[re.sub('[\s+]', '', snippet_vars_dict[v])]]) + ')'
            #constraints += '(<= 0 l_%s) (< l_%s %d) ' % (v, v, len(snippet_variables))
            get_value.append('l_%s' % v)
        for v in snippet_outputs:
            declarations += '(declare-const l_%s Int)\n' % v
            if not v in snippet_vars_dict:
                constraints += '(<= %d l_%s) (< l_%s %d) ' % (len(snippet_variables), v, v, len(snippet_variables)+len(snippet_outputs))
            elif len(types_out[re.sub('[\s+]', '',snippet_vars_dict[v])]) == 1:
                constraints += '(= %d l_%s)' % (types_out[re.sub('[\s+]', '', snippet_vars_dict[v])][0], v)
            else:
                constraints += '(or ' + ' '.join(['(= %d l_%s)' % (i, v) for i in types_out[re.sub('[\s+]', '', snippet_vars_dict[v])]]) + ')'
            #constraints += '(<= %d l_%s) (< l_%s %d) ' % (len(snippet_variables), v, v, len(snippet_variables)+len(snippet_outputs))
            get_value.append('l_%s' % v)
        constraints += '))\n(assert (and '
        for v in code_variables:
            for sv in snippet_variables:
                constraints += '(=> (= l_%s_in l_%s) (and ' % (v, sv)
                constraints += ''.join(['(= %s_in_%d %s_%d) ' % (v, i, sv, i) for i in range(number_of_profiles)])
                constraints += ') ) '
        for v in snippet_outputs:
            if not isinstance(self.suspicious_block.outputs, dict):
                break
            for pv in self.suspicious_block.outputs.keys():
                constraints += '(=> (= l_%s_out l_%s) (and ' % (pv, v)
                constraints += ''.join(['(= %(pv)s_out_%(i)d %(v)s_ret_%(i)d) (= %(pv)s_in_%(i)d %(v)s_%(i)d) '
                                        % {'pv': pv, 'v': v, 'i': i} for i in range(number_of_profiles)])
                constraints += ') ) '
        constraints += ') )\n'

        if len(snippet_variables) > 1:
            constraints += '(assert (distinct ' + \
                           ' '.join(['l_%s' % s for s in snippet_variables]) + ') )\n'
        if len(snippet_outputs) > 1:
            constraints += '(assert (distinct ' + \
                           ' '.join(['l_%s' % s for s in snippet_outputs]) + ') )\n'

        return declarations + constraints, get_value, mapping

    @staticmethod
    def proper_value(value, typ):
        """
        Returns two's complement for negative numbers
        """
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
        """
        Disjuncts all constraints together
        :param constraints:
        :return:
        """
        s = '(or ' * (len(constraints) - 1)
        first = True
        for c in constraints:
            s += c[2]
            if first:
                first = False
            else:
                s += ') '
        return s

    @staticmethod
    def get_let_statement(var_name, abbreviation='A1'):
        """
        Let statement for a variable
        """
        s = '( (?' + abbreviation + ' (concat  (select  ' + var_name + ' (_ bv3 32) ) (concat  (select  ' + var_name + \
            ' (_ bv2 32) ) (concat  (select  ' + var_name + ' (_ bv1 32) ) (select  ' + var_name + ' (_ bv0 32) ) ) ) ) ) )'
        return s

    @staticmethod
    def is_valid_mapping(mapping, snippet_vars, code_vars, snippet_outs, code_outs):
        """
        Is a mapping valid? (Old version)
        """
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
        """
        Translate a string into smt language
        """
        if len(string) == 0:
            return ''
        query = ''
        for i in range(len(string)):
            query += '(and (= (select %s (_ bv%d 32) ) (_ bv%d 8) ) ' % (variable, i, ord(string[i]))
        query += ') '*(len(string))
        return query

    @staticmethod
    def get_struct_mapping(mem_array, variable):
        """
        Translate a struct into smt language
        """
        parts = mem_array.split(',')
        if len(parts) <= 1:
            return ''
        query = '(and '
        i = 0
        for i in range(len(parts)):
            if parts[i]:
                try:
                    query += '(= (select %s (_ bv%d 32) ) (_ bv%d 8) ) ' % (variable, i, int(parts[i]))
                except Exception as e:
                    logger.error("The output of struct profile doesn't seem right: %s" % str(e))
                    raise e
        return query + ')'

    @staticmethod
    def replace_variable_names(num, constraint, variables, outputs):
        """
        Add test number to the end of variable name
        """
        replaced = constraint
        for v in variables:
            replaced = replaced.replace(' %s ' % v, ' %s_%d ' % (v, num))
            replaced = replaced.replace('(%s)' % v, '(%s_%d)' % (v, num))
        for o in outputs:
            if o == 'return_value':
                replaced = replaced.replace(' %s ' % o, ' %s_ret_%d ' % (o, num))
                replaced = replaced.replace('(%s)' % o, '(%s_ret_%d)' % (o, num))
                continue
            replaced = replaced.replace(' %s_ret ' % o, ' %s_ret_%d ' % (o, num))
            replaced = replaced.replace('(%s_ret)' % o, '(%s_ret_%d)' % (o, num))
        replaced = replaced.replace(' console ', ' console_%d ' % num)
        replaced = replaced.replace('(console)', '(console_%d)' % num)
        return replaced
