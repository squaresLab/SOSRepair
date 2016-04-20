__author__ = 'afsoona'


import psycopg2
from settings import DATABASE
from repository.snippet_preparation import CodeSnippet


class DatabaseManager():
    def __init__(self):
        self.connection = None
        self.last_id = None

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
        assert isinstance(snippet, CodeSnippet)
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
                sql = """
        INSERT INTO constraints (SMT, SNIPPET_ID)
        VALUES (%s, %s)
                """
                cursor.execute(sql, (constraint, snippet_id))
                self.connect().commit()
        except psycopg2.DatabaseError, e:
            print 'Error %s' % e
            self.close()