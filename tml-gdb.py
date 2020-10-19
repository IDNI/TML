import gdb.printing;

class LexemePrinter(object):
    """Print a lexeme"""
    def __init__(self, val):
        self.val = val["_M_elems"]

    def to_string(self):
        if self.val[0] == 0 or self.val[0] == self.val[1]:
            return "``"
        return "`%s`" % self.val[0].string("utf-8", 'strict', self.val[1] - self.val[0])

def build_pretty_printer():
    pp = gdb.printing.RegexpCollectionPrettyPrinter("prettytml")
    pp.add_printer('lexeme', '^std::array<unsigned char const\*, 2>', LexemePrinter)
    return pp

gdb.printing.register_pretty_printer(
    gdb.current_objfile(),
    build_pretty_printer())
