"""An effective exhaustive encoding of finite piecewise chart certificates.

The natural numbers enumerate ALL finite bit strings in shortlex order. The
decoder is a finite data grammar, not a programming language. Every finite
certificate accepted by PiecewiseVerifier has an equivalent encoding here:
Q(sqrt(462)) coefficients, arbitrary legal words, rational interpolation,
arbitrary finite domains, nodes, destinations and inline parameter pieces.

This fallback establishes relative semidecision completeness, not a useful
runtime bound. The separate finite-library solver supplies practical search.
"""
from fractions import Fraction

from chart_geometry import Domain
from type_graph_geometry import full_labels, root_cells
from verify_piecewise_charts import FORMAT


class DecodeError(ValueError):
    pass


def code_bits(index):
    if type(index) is not int or index < 0:
        raise ValueError('nonnegative integer index required')
    return bin(index+1)[3:]


def bits_code(bits):
    if any(c not in '01' for c in bits):
        raise ValueError('not a binary string')
    return int('1'+bits, 2)-1


def word_code(word):
    value = 0
    for c in word:
        if c not in '123':
            raise ValueError('only digits 1, 2, 3 are encodable')
        value = 3*value+int(c)
    return value


def code_word(value):
    digits = []
    while value:
        value, c = divmod(value-1, 3)
        digits.append(str(c+1))
    return ''.join(reversed(digits))


class Reader:
    def __init__(self, bits):
        self.bits, self.position = bits, 0

    def bit(self):
        if self.position == len(self.bits):
            raise DecodeError('incomplete code')
        value = self.bits[self.position] == '1'
        self.position += 1
        return value

    def uint(self):
        # Elias gamma of n+1. All loops consume input bits.
        zeros = 0
        while not self.bit():
            zeros += 1
        value = 1
        for _ in range(zeros):
            value = 2*value+int(self.bit())
        return value-1

    def size(self, offset=0):
        n = self.uint()+offset
        # Every list element in this grammar consumes at least one bit.
        # This is a grammar impossibility test, not a size cutoff.
        if n > len(self.bits)-self.position:
            raise DecodeError('list cannot fit in remaining code')
        return n

    def rational(self):
        z = self.uint()
        numerator = z//2 if z % 2 == 0 else -(z//2)-1
        return str(Fraction(numerator, self.uint()+1))

    def field(self):
        return [self.rational(), self.rational()]

    def word(self):
        return code_word(self.uint())

    def tail(self):
        word = self.word()
        return word+'@'+self.rational() if self.bit() else word

    def label(self):
        return [self.tail(), self.bit(), self.tail(), self.bit()]

    def interval(self):
        tag = 2*int(self.bit())+int(self.bit())
        if tag < 2:
            return [list(v) for v in full_labels(-1 if tag == 0 else 1)]
        if tag == 2:
            return [self.label(), self.label()]
        raise DecodeError('reserved interval tag')

    def domain(self):
        tag = 2*int(self.bit())+int(self.bit())
        if tag < 2:
            root = root_cells()[tag]
            return Domain(root, ('', ''), root.high).record()
        if tag != 2:
            raise DecodeError('reserved domain tag')
        base = dict(states=[self.word(), self.word()],
                    parity=1 if self.bit() else -1, high=self.bit())
        for key in ('r', 's', 'ratio'):
            base[key] = [self.field(), self.field()]
        return dict(base=base, words=[self.word(), self.word()], high=self.bit())

    def edges(self):
        result = []
        for _ in range(self.size(1)):
            words, high = [self.word(), self.word()], self.bit()
            lower, upper = self.interval()
            ds = [dict(node=self.uint(), swap=self.bit()) for _ in range(self.size(1))]
            result.append(dict(suffixes=words, high=high, lower=lower, upper=upper, destinations=ds))
        return result

    def node(self):
        cid = self.uint()
        lower, upper = self.interval()
        node = dict(cell=cid, lower=lower, upper=upper, children=[])
        tag = 2*int(self.bit())+int(self.bit())
        if tag == 1:
            node['children'] = self.edges()
        elif tag == 2:
            node['pieces'] = [dict(cell=self.uint(), children=self.edges()) for _ in range(self.size(1))]
        elif tag != 0:
            raise DecodeError('reserved rule tag')
        return node


class Writer:
    def __init__(self):
        self.parts = []

    def bit(self, value):
        if type(value) is not bool:
            raise ValueError('boolean required')
        self.parts.append('1' if value else '0')

    def tag(self, n):
        self.bit(bool(n & 2))
        self.bit(bool(n & 1))

    def uint(self, n):
        if type(n) is not int or n < 0:
            raise ValueError('nonnegative integer required')
        digits = bin(n+1)[2:]
        self.parts.append('0'*(len(digits)-1)+digits)

    def rational(self, value):
        value = Fraction(value)
        n = value.numerator
        self.uint(2*n if n >= 0 else -2*n-1)
        self.uint(value.denominator-1)

    def field(self, value):
        for x in value:
            self.rational(x)

    def word(self, word):
        self.uint(word_code(word))

    def tail(self, text):
        fields = text.split('@')
        self.word(fields[0])
        self.bit(len(fields) == 2)
        if len(fields) == 2:
            self.rational(fields[1])
        elif len(fields) != 1:
            raise ValueError('invalid endpoint word')

    def label(self, row):
        self.tail(row[0])
        self.bit(row[1])
        self.tail(row[2])
        self.bit(row[3])

    def interval(self, lower, upper):
        pair = tuple(map(tuple, (lower, upper)))
        for tag, parity in enumerate((-1, 1)):
            if pair == full_labels(parity):
                self.tag(tag)
                return
        self.tag(2)
        self.label(lower)
        self.label(upper)

    def domain(self, record):
        domain = Domain.read(record)
        for tag, root in enumerate(root_cells()):
            if domain == Domain(root, ('', ''), root.high):
                self.tag(tag)
                return
        self.tag(2)
        base = domain.base.record()
        for state in base['states']:
            self.word(state)
        self.bit(base['parity'] == 1)
        self.bit(base['high'])
        for key in ('r', 's', 'ratio'):
            for bound in base[key]:
                self.field(bound)
        for word in domain.words:
            self.word(word)
        self.bit(domain.high)

    def edges(self, edges):
        self.uint(len(edges)-1)
        for edge in edges:
            for word in edge['suffixes']:
                self.word(word)
            self.bit(edge['high'])
            self.interval(edge['lower'], edge['upper'])
            self.uint(len(edge['destinations'])-1)
            for dest in edge['destinations']:
                self.uint(dest['node'])
                self.bit(dest['swap'])

    def node(self, node):
        self.uint(node['cell'])
        self.interval(node['lower'], node['upper'])
        if node.get('pieces'):
            if node.get('children'):
                raise ValueError('ambiguous rule')
            self.tag(2)
            self.uint(len(node['pieces'])-1)
            for piece in node['pieces']:
                self.uint(piece['cell'])
                self.edges(piece['children'])
        elif node.get('children'):
            self.tag(1)
            self.edges(node['children'])
        else:
            self.tag(0)


def encode_certificate(data):
    if data['format'] != FORMAT:
        raise ValueError('wrong certificate format')
    writer = Writer()
    writer.uint(len(data['cells'])-1)
    for domain in data['cells']:
        writer.domain(domain)
    writer.uint(len(data['nodes'])-1)
    for node in data['nodes']:
        writer.node(node)
    for name in ('zero', 'positive'):
        writer.uint(data['roots'][name])
    return ''.join(writer.parts)


def decode_certificate(bits):
    if any(c not in '01' for c in bits):
        raise DecodeError('not a bit string')
    reader = Reader(bits)
    data = dict(format=FORMAT, cells=[reader.domain() for _ in range(reader.size(1))],
                nodes=[reader.node() for _ in range(reader.size(1))])
    data['roots'] = {name: reader.uint() for name in ('zero', 'positive')}
    if reader.position != len(bits):
        raise DecodeError('trailing data')
    return data
