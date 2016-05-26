__author__ = 'Afsoon Afzal'


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

        return index

    def prepare_smt_query(self, index):
        snippet = self.db_manager.fetch_snippet(index)
        constraints = self.db_manager.fetch_constraints(index)
        if len(constraints) < 1 or not snippet:
            print "ERROR no constraints or snippet for this id %d" % index
        decls = self.prepare_declarations(constraints)
        for profile in self.profile.input_list:
            query = decls + '\n'
            for v, t in self.suspicious_block.vars:
                query += '(assert (let ' + self.get_let_statement(v + '_in') + '(= ?A1 (_ bv' + profile[v][0] + \
                         ' 32) ) ) ) \n'
            if isinstance(self.suspicious_block.outputs, dict):
                for v in self.suspicious_block.outputs.keys():
                    query += '(assert (let ' + self.get_let_statement(v + '_out') + '(= ?A1 (_ bv' + profile[v][1] + \
                             ' 32) ) ) ) \n'
            print query

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
        print decls
        return decls

    @staticmethod
    def get_let_statement(var_name, abbreviation='A1'):
        s = '( (?' + abbreviation + ' (concat  (select  ' + var_name + ' (_ bv3 32) ) (concat  (select  ' + var_name + \
            ' (_ bv2 32) ) (concat  (select  ' + var_name + ' (_ bv1 32) ) (select  ' + var_name + ' (_ bv0 32) ) ) ) )) )'
        return s
