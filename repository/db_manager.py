__author__ = 'afsoona'


import logging
import psycopg2
from settings import DATABASE
from utils import counter_subset

logger = logging.getLogger(__name__)

class DatabaseManager():
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
            self.insert_constraint(snippet, id)
        except psycopg2.DatabaseError, e:
            logger.error('%s' % str(e))
            self.close()

    def insert_constraint(self, snippet, snippet_id):
        try:
            cursor = self.connect().cursor()
            for constraint in snippet.constraints:
                decl, smt = snippet.seperate_declarations(constraint)
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
        try:
            cursor = self.connect().cursor()
            sql = """
            SELECT ID,VARIABLES,OUTPUTS FROM snippets WHERE ID>%d
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
                v_types = [i[1] for i in eval(v)]
                try:
                    out = eval(o)
                except:
                    continue
                if (isinstance(out, dict) and not isinstance(outputs, dict)) or \
                        (not isinstance(out, dict) and isinstance(outputs, dict)):
                    continue
                if isinstance(out, dict):
                    o_types = [out[i]['type'] for i in out.keys()]
                else:
                    o_types = [out]
                logger.debug("var: %s, v: %s, out: %s, o: %s" % (str(var_types), str(v_types), str(output_types), str(o_types)))
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
