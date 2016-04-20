__author__ = 'afsoona'


import psycopg2
from settings import DATABASE


class DatabaseManager():
    def __init__(self):
        self.connection = None

    def connect(self):
        if self.connection:
            return self.connection
        try:
            self.connection = psycopg2.connect(database=DATABASE['db_name'], user=DATABASE['user'], password=DATABASE['password'])
        except psycopg2.DatabaseError, e:
            if self.connection:
                self.connection.rollback()
            print 'Error %s' % e
        finally:
            if self.connection:
                self.connection.close()
        return self.connection

    def close(self):
        if self.connection:
            self.connection.close()
        self.connection = None
