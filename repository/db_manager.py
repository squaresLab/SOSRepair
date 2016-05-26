__author__ = 'afsoona'


import collections
import psycopg2
from settings import DATABASE


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
            print 'Error %s' % e
            self.close()
        return self.connection

    def close(self):
        if self.connection:
            self.connection.close()
        self.connection = None

    def initialize_tables(self):
        try:
            cursor = self.connect().cursor()
            sql = """
    CREATE TABLE IF NOT EXISTS snippets (
       ID SERIAL PRIMARY KEY     NOT NULL,
       SOURCE           TEXT,
       VARIABLES         TEXT,
       OUTPUTS        TEXT,
       FUNCTIONS         TEXT
    );
    CREATE TABLE IF NOT EXISTS constraints (
      ID SERIAL PRIMARY KEY   NOT NULL ,
      DECL            TEXT    NOT NULL ,
      SMT             TEXT    NOT NULL ,
      SNIPPET_ID      INT     REFERENCES snippets(ID)
    );
    """
            cursor.execute(sql)
            ver = self.connect().commit()
            print ver
        except psycopg2.DatabaseError, e:
            print 'Error %s' % e
            self.close()

    def insert_snippet(self, snippet):
        try:
            cursor = self.connect().cursor()
            sql = """
    INSERT INTO snippets (SOURCE, VARIABLES, OUTPUTS, FUNCTIONS)
    VALUES (%s, %s, %s, %s)
    RETURNING ID
            """
            cursor.execute(sql, (str(snippet.source), str(snippet.variables), \
                   str(snippet.outputs), str(snippet.function_calls)))
            self.connect().commit()
            id = cursor.fetchone()[0]
            print id
            self.insert_constraint(snippet, id)
        except psycopg2.DatabaseError, e:
            print 'Error %s' % e
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
            print 'Error %s' % e
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
            print 'Error %s' % e
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
            compare = lambda x, y: collections.Counter(x) == collections.Counter(y)
            for id, v, o in rows:
                v_types = [i[1] for i in eval(v)]
                out = eval(o)
                if isinstance(out, dict):
                    o_types = [out[i]['type'] for i in out.keys()]
                else:
                    o_types = [out]
                if compare(var_types, v_types) and compare(output_types, o_types):
                    return id
        except psycopg2.DatabaseError, e:
            print 'Error %s' % e
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
            print 'Error %s' % e
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
            print 'Error %s' % e
            if self.connect():
                self.connect().rollback()
            self.close()
