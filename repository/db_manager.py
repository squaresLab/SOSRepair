__author__ = 'afsoona'


import psycopg2
from settings import DATABASE


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

        finally:
            self.close()


