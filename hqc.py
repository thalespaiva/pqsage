from sage.all import *
from itertools import chain
from dataclasses import dataclass

def binary_vector_from_int(a, length):
    bits = bin(a)[2:]
    v = zero_vector(GF(2), length)
    for i, b in enumerate(reversed(bits)):
        v[i] = b

    return v

class RepeatedReedMullerForHQC():

    RMCodeLength = 128

    GeneratorMatrix = matrix([
        binary_vector_from_int(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, RMCodeLength),
        binary_vector_from_int(0xcccccccccccccccccccccccccccccccc, RMCodeLength),
        binary_vector_from_int(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, RMCodeLength),
        binary_vector_from_int(0xff00ff00ff00ff00ff00ff00ff00ff00, RMCodeLength),
        binary_vector_from_int(0xffff0000ffff0000ffff0000ffff0000, RMCodeLength),
        binary_vector_from_int(0x00000000ffffffff00000000ffffffff, RMCodeLength),
        binary_vector_from_int(0x0000000000000000ffffffffffffffff, RMCodeLength),
        binary_vector_from_int(0xffffffffffffffffffffffffffffffff, RMCodeLength),
    ])

    def __init__(self, multiplicity):
        assert multiplicity % 2 == 1

        self.q = 2
        self.k = 8
        self.n = 128 * multiplicity
        self.multiplicity = multiplicity

        self.encoded_table = [self.encode(binary_vector_from_int(m, self.k)) for m in range(256)]

    def generate_random_message(self):
        return random_vector(GF(2), self.k)

    def generate_random_error(self, weight):
        error_positions = sample(range(self.n), weight)
        error_vector = zero_vector(GF(2), self.n)
        for i in error_positions:
            error_vector[i] = 1
        return vector(error_vector)

    def encode(self, message):
        repeated_encoded = [vector(GF(2), message) * self.GeneratorMatrix] * self.multiplicity
        return vector(chain(*repeated_encoded))

    def decode(self, noisy_codeword):

        min_distance = self.n
        decoded_m = None
        for m in range(2**8):
            encoded_m = self.encoded_table[m]
            distance = (encoded_m - noisy_codeword).hamming_weight()

            if distance < min_distance:
                min_distance = distance
                decoded_m = m

        return binary_vector_from_int(decoded_m, self.k)


class ReedSolomonForHQC():

    def __init__(self, n, k):
        self.n = n  # Block length
        self.k = k  # Dimension
        self.q = 256
        self.delta = (n - k) // 2

        self.base_field = GF(self.q)
        self.polynomial_ring = PolynomialRing(self.base_field, 'x')
        self.x = self.polynomial_ring.gen()

        self.generator_polynomial = self._compute_generator_polynomial()

    def _compute_generator_polynomial(self):
        alpha = self.base_field.primitive_element()
        return prod(self.x - alpha**i for i in range(1, 2*self.delta + 1))

    def generate_random_message(self):
        return [self.base_field.random_element() for i in range(self.k)]

    def generate_random_error(self, weight):
        error_positions = sample(range(self.n), weight)
        error_vector = [0] * self.n
        for i in error_positions:
            v = self.base_field.random_element()
            while v == 0:
                v = self.base_field.random_element()
            error_vector[i] = v
        return self.polynomial_ring(error_vector)

    def encode(self, message):
        '''
        message should be list of coefficients
        '''
        message_polynomial = self.polynomial_ring(message)
        # assert len(message) == ...
        a = self.x**(self.n - self.k) * message_polynomial
        b = a % self.generator_polynomial
        c = b + a

        return c

    def berlekamp_massey(self, s):

        connection = self.polynomial_ring(1)
        b = self.base_field(1)
        last_connection = 1
        k = 1

        for s_n, n in enumerate(s):
            d = s_n + sum(connection[i]*s[n - i] for i in range(1, connection.degree() + 1))
            if d == 0:
                k += 1
                continue

            tmp_connection = copy(connection)
            connection = connection - d * b.inverse() * self.x**k * last_connection

            if 2 * tmp_connection.degree() <= n:
                last_connection, b, k = tmp_connection, d, 1
            else:
                k += 1

        return connection


    def decode(self, noisy_codeword):
        alpha = self.base_field.primitive_element()

        syndromes = [noisy_codeword(alpha**i) for i in range(1, 2*self.delta + 1)]

        # return syndromes
        error_location_polynomial = self.berlekamp_massey(syndromes)

        alpha_log_table = {alpha**i: i for i in range(1, self.n + 1)}

        error_positions = []
        for element in self.base_field:
            if error_location_polynomial(element) == 0:
                # element is a root
                error_pos = alpha_log_table[element.inverse()]
                error_positions.append(error_pos)

        return error_positions

class RMRSCodeForHQC():

    def __init__(self, rs_n, rs_k, rm_multiplicity):
        self.rs_code = ReedSolomonForHQC(rs_n, rs_k)
        self.rm_code = ReedSolomonForHQC(rm_multiplicity)

    def encode(self, message):
        assert len(message) == self.rs_code.k

        rs_codeword = self.rs_code.encode(message)

        return rs_codeword

@dataclass
class HQCParameters:
    security_level: int
    n1: int
    n2: int
    multiplicity: int
    n: int
    k: int
    w: int
    w_r: int
    w_e: int

class HQC():
    SecurityParameters = {
        # Security Level : parameters
        128: HQCParameters(
            security_level=128, n1=46, n2=384, multiplicity=3, n=17669, k=128, w=66, w_r=77, w_e=77,
        ),
        192: HQCParameters(
            security_level=192, n1=56, n2=640, multiplicity=5, n=35851, k=192, w=100, w_r=114, w_e=114,
        ),
        256: HQCParameters(
            security_level=256, n1=90, n2=640, multiplicity=5, n=57637, k=256, w=133, w_r=149, w_e=149,
        ),
    }

    def __init__(self, security_level):
        assert(security_level in self.SecurityParameters)

        self.params = self.SecurityParameters[security_level]

    def generate_binary_vector_of_fixed_weight(self, weight):
        support = sample(range(self.params.n), weight)
        v = zero_vector(GF(2), self.params.n)
        for s in support:
            v[s] = 1
        return v

    def vector_product(self, a, b):
        R = PolynomialRing(GF(2), 'x')
        x = R.gen()
        Q = R.quotient(x**self.params.n - 1)

        return vector(GF(2), Q(list(a)) * Q(list(b)))

    def keygen(self):
        h = random_vector(GF(2), self.params.n)
        x = self.generate_binary_vector_of_fixed_weight(self.params.w)
        y = self.generate_binary_vector_of_fixed_weight(self.params.w)
        s = x + self.vector_product(h, y)

        return (h, s), (x, y)

    def encrypt(self, pk, message):
        h, s = pk
        e = self.generate_binary_vector_of_fixed_weight(self.params.w_e)
        r_1 = self.generate_binary_vector_of_fixed_weight(self.params.w_r)
        r_2 = self.generate_binary_vector_of_fixed_weight(self.params.w_r)
        u = r_1 + self.vector_product(h, r_2)
        v = self.vector_product(s, r_2) + e

        return (u, v)



    def decrypt():
        pass

    # 128 [9, 69, 153, 116, 176, 117, 111, 75, 73, 233, 242, 233, 65, 210, 21, 139, 103, 173, 67, 118, 105, 210, 174, 110, 74, 69, 228, 82, 255, 181, 1]
    # 192 [45, 216, 239, 24, 253, 104, 27, 40, 107, 50, 163, 210, 227, 134, 224, 158, 119, 13, 158, 1, 238, 164, 82, 43, 15, 232, 246, 142, 50, 189, 29, 232, 1]
    # 256 [49, 167, 49, 39, 200, 121, 124, 91, 240, 63, 148, 71, 150, 123, 87, 101, 32, 215, 159, 71, 201, 115, 97, 210, 186, 183, 141, 217, 123, 12, 31, 243, 180, 219, 152, 239, 99, 141, 4, 246, 191, 144, 8, 232, 47, 27, 141, 178, 130, 64, 124, 47, 39, 188, 216, 48, 199, 187, 1]



