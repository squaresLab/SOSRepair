__author__ = 'afsoona'

import re



def comment_remover(text):
    def replacer(match):
        s = match.group(0)
        if s.startswith('/'):
            multiline = len(s.split('\n'))
            str = ""
            for i in range(multiline-1):
                str += "\n"
            return str.strip()
        else:
            try:
                rest = match.group(1)
                multiline = len(rest.split('\n'))
                for i in range(multiline-1):
                    s += "\n"
            except:
                return s.strip()
            return s.strip()
    pattern = re.compile(
        r'//.*?$|/\*.*?\*/|\'(?:\\.|[^\\\'])*\'|"(?:\\.|[^\\"])*"',
        re.DOTALL | re.MULTILINE
    )
    return re.sub(pattern, replacer, text)

class ProcessProgram():

    def __init__(self, filename):
        self.filename = filename
        self.original_text = ''
        self.processed_text = ''
        self.total_lines = 0
        self.read_file()


    def read_file(self):
        #TODO check the file
        with open(self.filename) as f:
            for line in f:
                self.total_lines += 1
                self.original_text += line
                if '#include' in line:
                    self.processed_text += '\n'
                elif '#define' in line or '#if' in line or '#else' in line or '#end' in line:
                    self.processed_text += '\n'
                else:
                    self.processed_text += line.strip() + '\n'
        self.processed_text = comment_remover(self.processed_text)


if __name__ == "__main__":
    pp = ProcessProgram('median.c')
    pp.read_file()
    print pp.processed_text