__author__ = 'Afsoon Afzal'


import logging
import psycopg2
import re
from settings import DATABASE
from utils import counter_subset

logger = logging.getLogger(__name__)

class DatabaseManager():
    """
    Manages interactions with database
    """
    def __init__(self):
        self.connection = None
        self.last_id = None
        self.connect()
        self.initialize_tables()

    def connect(self):
        if self.connection:
            return self.connection
        try:
            self.connection = psycopg2.connect(database=DATABASE['db_name'], user=DATABASE['user'], password=DATABASE['password'])
        except psycopg2.DatabaseError, e:
            if self.connection:
                self.connection.rollback()
            logger.error('%s' % str(e))
            self.close()
        return self.connection

    def close(self):
        if self.connection:
            self.connection.close()
        self.connection = None

    def drop_tables(self):
        try:
            cursor = self.connect().cursor()
            sql = """
    DROP TABLE constraints;
    DROP TABLE snippets;
    """
            cursor.execute(sql)
            self.connect().commit()
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            self.close()

    def initialize_tables(self):
        try:
            cursor = self.connect().cursor()
            sql = """
    CREATE TABLE IF NOT EXISTS snippets (
       ID SERIAL PRIMARY KEY     NOT NULL,
       SOURCE           TEXT,
       VARIABLES         TEXT,
       OUTPUTS        TEXT,
       FUNCTIONS         TEXT,
       PATH             TEXT    NOT NULL
    );
    CREATE TABLE IF NOT EXISTS constraints (
      ID SERIAL PRIMARY KEY   NOT NULL ,
      DECL            TEXT    NOT NULL ,
      SMT             TEXT    NOT NULL ,
      SNIPPET_ID      INT     REFERENCES snippets(ID)
    );
    """
            cursor.execute(sql)
            self.connect().commit()
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            self.close()

    def insert_snippet(self, snippet):
        try:
            cursor = self.connect().cursor()
            sql = """
    INSERT INTO snippets (SOURCE, VARIABLES, OUTPUTS, FUNCTIONS, PATH)
    VALUES (%s, %s, %s, %s, %s)
    RETURNING ID
            """
            cursor.execute(sql, (str(snippet.source), str(snippet.variables),
                                 str(snippet.outputs), str(snippet.function_calls), snippet.path))
            self.connect().commit()
            id = cursor.fetchone()[0]
            print "ID %d" % id
            logger.debug("ID: %d" % id)
            self.insert_constraint(snippet, id)
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            self.close()

    def insert_constraint(self, snippet, snippet_id):
        try:
            cursor = self.connect().cursor()
            for constraint in snippet.constraints:
                decl, smt = snippet.separate_declarations(constraint)
                sql = """
        INSERT INTO constraints (DECL, SMT, SNIPPET_ID)
        VALUES (%s, %s, %s)
                """
                cursor.execute(sql, (decl, smt, snippet_id))
                self.connect().commit()
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            if self.connect():
                self.connect().rollback()
            self.close()

    def insert_constraints(self, values):
        try:
            cursor = self.connect().cursor()
            sql = """
    INSERT INTO constraints (DECL, SMT, SNIPPET_ID)
    VALUES (%s, %s, %s)
            """
            cursor.executemany(sql, values)
            self.connect().commit()
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            if self.connect():
                self.connect().rollback()
            self.close()

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()

    def fetch_next_valid_snippet(self, vars, outputs, index=0):
        """
        Checks signature of suspicious block and the snippets in the DB to find the next valid snippet
        """
        try:
            cursor = self.connect().cursor()
            sql = """
            SELECT ID,VARIABLES,OUTPUTS FROM snippets WHERE ID>%d
            ORDER BY ID
            """ % index
            cursor.execute(sql)
            rows = cursor.fetchall()  # TODO are you sure?
            if len(rows) == 0:
                return 0
            var_types = [i[1] for i in vars]
            if isinstance(outputs, dict):
                output_types = [outputs[i]['type'] for i in outputs.keys()]
            else:
                output_types = [outputs]
            for id, v, o in rows:
                logger.debug("id: %d, o: %s, v: %s" %(id, str(o), str(v)))
                v_types = [i[1] for i in eval(v)]
                try:
                    out = eval(o)
                    if not isinstance(out, dict):
                        out = [out]
                except:
                    out = [o]
                #if (isinstance(out, dict) and not isinstance(outputs, dict)) or \
                #        (not isinstance(out, dict) and isinstance(outputs, dict)):
                #    continue
                logger.debug("id: %d, o: %s, out: %s, is: %s" %(id, str(o), str(out), str(isinstance(out, dict))))
                if isinstance(out, dict):
                    o_types = [out[i]['type'] for i in out.keys()]
                else:
                    o_types = [str(o)]
                logger.debug("var: %s, v: %s, subset: %s, out: %s, o: %s, subset: %s" % (str(var_types), str(v_types), str(counter_subset(var_types, v_types)), str(output_types), str(o_types), str(counter_subset(output_types, o_types))))
                if counter_subset(var_types, v_types) and counter_subset(output_types, o_types):
                    return id
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            if self.connect():
                self.connect().rollback()
            self.close()

    def fetch_snippet(self, index):
        try:
            cursor = self.connect().cursor()
            sql = """
            SELECT * FROM snippets WHERE ID=%d
            """ % index
            cursor.execute(sql)
            row = cursor.fetchone()
            return row
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            if self.connect():
                self.connect().rollback()
            self.close()

    def fetch_constraints(self, index):
        try:
            cursor = self.connect().cursor()
            sql = """
            SELECT * FROM constraints WHERE SNIPPET_ID=%d
            """ % index
            cursor.execute(sql)
            rows = cursor.fetchall()
            return rows
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            if self.connect():
                self.connect().rollback()
            self.close()

    def is_syntactically_redundant(self, snippet):
        sql = "SELECT ID,SOURCE FROM snippets ORDER BY ID"
        try:
            cursor = self.connect().cursor()
            cursor.execute(sql)
            rows = cursor.fetchall()
            m_s = re.sub('[\s+]', '', snippet)
            for id, source in rows:
                s = re.sub('[\s+]', '', source)
                if m_s == s:
                    return True
            return False
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            if self.connect():
                self.connect().rollback()
            self.close()

    def fetch_all_valid_snippets(self, phase, filename, module_name, vars, outputs):
        if phase == 'deletion':
            rows = self.get_snippets_deletion()
        elif phase == 'in_file':
            rows = self.get_snippets_in_file(filename)
        elif phase == 'in_module':
            rows = self.get_snippets_in_module(filename, module_name)
        else:
            rows = self.get_snippets_all(filename, module_name)
        candidate_rows = []
        if len(rows) == 0:
            return []
        var_types = [re.sub('[\s+]', '', i[1]) for i in vars]
        if isinstance(outputs, dict):
            output_types = [re.sub('[\s+]', '',outputs[i]['type']) for i in outputs.keys()]
        else:
            output_types = [re.sub('[\s+]', '',outputs)]
        for id, v, o in rows:
            logger.debug("id: %d, o: %s, v: %s" %(id, str(o), str(v)))
            v_types = [re.sub('[\s+]', '',i[1]) for i in eval(v)]
            try:
                out = eval(o)
                if not isinstance(out, dict):
                    out = [out]
            except:
                out = [o]
            #if (isinstance(out, dict) and not isinstance(outputs, dict)) or \
            #        (not isinstance(out, dict) and isinstance(outputs, dict)):
            #    continue
            logger.debug("id: %d, o: %s, out: %s, is: %s" %(id, str(o), str(out), str(isinstance(out, dict))))
            if isinstance(out, dict):
                o_types = [re.sub('[\s+]', '',out[i]['type']) for i in out.keys()]
            else:
                o_types = [re.sub('[\s+]', '',str(o))]
            logger.debug("var: %s, v: %s, subset: %s, out: %s, o: %s, subset: %s" % (str(var_types), str(v_types), str(counter_subset(var_types, v_types)), str(output_types), str(o_types), str(counter_subset(output_types, o_types))))
            if counter_subset(var_types, v_types) and counter_subset(output_types, o_types):
                candidate_rows.append(id)
        return candidate_rows

    def get_snippets_deletion(self):
        sql = "SELECT ID,VARIABLES,OUTPUTS FROM snippets WHERE PATH = ''"
        logger.debug("Run this 0: %s" %sql)
        try:
            cursor = self.connect().cursor()
            cursor.execute(sql)
            rows = cursor.fetchall()
            logger.debug("Length 0: %d" %len(rows))
            return rows
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            if self.connect():
                self.connect().rollback()
            self.close()

    def get_snippets_in_file(self, filename):
        sql = "SELECT ID,VARIABLES,OUTPUTS FROM snippets WHERE PATH = '%s'" % filename
        logger.debug("Run this 1: %s" %sql)
        try:
            cursor = self.connect().cursor()
            cursor.execute(sql)
            rows = cursor.fetchall()
            logger.debug("Length 1: %d" %len(rows))
            return rows
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            if self.connect():
                self.connect().rollback()
            self.close()

    def get_snippets_in_module(self, filename, module):
        sql = "SELECT ID,VARIABLES,OUTPUTS FROM snippets WHERE PATH != '%s' AND PATH ~ '%s'" % (filename, module)
        logger.debug("Run this 2: %s" %sql)
        try:
            cursor = self.connect().cursor()
            cursor.execute(sql)
            rows = cursor.fetchall()
            logger.debug("Length 2: %d" %len(rows))
            return rows
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            if self.connect():
                self.connect().rollback()
            self.close()

    def get_snippets_all(self, filename, module):
        sql = "SELECT ID,VARIABLES,OUTPUTS FROM snippets WHERE PATH != '%s' AND NOT PATH ~ '%s' AND PATH != ''" % (filename, module)
        logger.debug("Run this 3: %s" %sql)
        try:
            cursor = self.connect().cursor()
            cursor.execute(sql)
            rows = cursor.fetchall()
            logger.debug("Length 3: %d" %len(rows))
            return rows
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            if self.connect():
                self.connect().rollback()
            self.close()
