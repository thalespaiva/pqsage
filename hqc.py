from sage.all import *
from itertools import chain
from dataclasses import dataclass

from Crypto.Random import get_random_bytes
from Crypto.Hash import SHAKE256

from pseudorandom import xof_sample_k_indexes

def binary_vector_from_int(a, length):
    bits = bin(a)[2:]
    v = zero_vector(GF(2), length)
    for i, b in enumerate(reversed(bits)):
        v[i] = int(b)

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

    def encode_binary(self, binary_message):
        assert len(binary_message) == self.k * 8

        message = [self.base_field(binary_message[i * 8 : (i + 1) * 8]) for i in range(self.k)]
        encoded = self.encode(message)

        encoded_binary = chain(*[list(v) for v in encoded])
        return vector(GF(2), encoded_binary)


    def encode(self, message):
        '''
        message should be list of coefficients
        '''
        message_polynomial = self.polynomial_ring(message)
        a = self.x**(self.n - self.k) * message_polynomial
        b = a % self.generator_polynomial
        c = b + a

        return c

    def berlekamp_massey(self, s):
        connection = self.polynomial_ring(1)
        b = self.base_field(1)
        last_connection = 1
        k = 1

        for n, s_n in enumerate(s):
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

    def decode_binary(self, noisy_binary_codeword):
        assert len(noisy_binary_codeword) == self.n * 8

        noisy_codeword = [self.base_field(noisy_binary_codeword[i * 8 : (i + 1) * 8])
                            for i in range(self.n)]

        decoded = self.decode(self.polynomial_ring(noisy_codeword))
        if decoded is None:
            return None
        decoded_binary = chain(*[list(v) for v in decoded])
        return vector(GF(2), decoded_binary)

    def solve_error_linear_system(self, syndromes, error_location_poly):
        alpha = self.base_field.primitive_element()
        alpha_log_table = {alpha**i: i for i in range(1, self.n + 1)}
        roots = [a for a in self.base_field if error_location_poly(a) == 0]
        error_betas = [e.inverse() for e in roots]
        error_positions = [alpha_log_table[b] for b in error_betas]

        beta_matrix = matrix(GF(self.q), [
            [beta**i for beta in error_betas] for i in range(1, 2*self.delta + 1)
        ])
        error_values = beta_matrix.solve_right(vector(syndromes))

        error = self.polynomial_ring(sum(e * self.x**i
                                         for i, e in zip(error_positions, error_values)))

        return error

    def decode(self, noisy_codeword):
        alpha = self.base_field.primitive_element()
        syndromes = [noisy_codeword(alpha**i) for i in range(1, 2*self.delta + 1)]
        error_location_poly = self.berlekamp_massey(syndromes)

        try:
            error = self.solve_error_linear_system(syndromes, error_location_poly)
            codeword_polynomial = noisy_codeword - error
            return self.polynomial_ring(list(codeword_polynomial)[-self.k:])

        except (KeyError, ValueError):
            # Decoding failure
            return None




class RMRSCodeForHQC():

    def __init__(self, rs_n, rs_k, rm_multiplicity, n=None):
        self.rs_code = ReedSolomonForHQC(rs_n, rs_k)
        self.rm_code = RepeatedReedMullerForHQC(rm_multiplicity)

        if n == None:
            self.padding_length = 0
        else:
            self.padding_length = n - self.rm_code.n * self.rs_code.n

    def encode(self, binary_message):
        rs_codeword = self.rs_code.encode_binary(binary_message)

        rm_messages = [rs_codeword[i * 8 : (i + 1) * 8] for i in range(self.rs_code.n)]
        rm_codewords = [self.rm_code.encode(m) for m in rm_messages]

        # return vector(GF(2), chain(*rm_codewords)), rm_messages, rm_codewords

        return vector(GF(2), chain(*rm_codewords, [0] * self.padding_length))

    def decode(self, noisy_codeword):
        # By the way rm_noisy_codewords is defined, the padding is naturally removed
        rm_noisy_codewords = [noisy_codeword[i * self.rm_code.n : (i + 1) * self.rm_code.n]
                                for i in range(self.rs_code.n)]
        rm_codewords = [self.rm_code.decode(c) for c in rm_noisy_codewords]

        rs_noisy_codeword = vector(chain(*rm_codewords))

        return self.rs_code.decode_binary(rs_noisy_codeword)

@dataclass
class HQCParameters:
    n1: int
    n2: int
    multiplicity: int
    n: int
    k: int
    w: int
    w_r: int
    w_e: int

class HQC_PKE_CPA():
    SecurityParameters = {
        1: HQCParameters(n1=46, n2=384, multiplicity=3, n=17669,
                         k=128, w=66, w_r=77, w_e=77),
        3: HQCParameters(n1=56, n2=640, multiplicity=5, n=35851,
                         k=192, w=100, w_r=114, w_e=114),
        5: HQCParameters(n1=90, n2=640, multiplicity=5, n=57637,
                         k=256, w=133, w_r=149, w_e=149),
    }

    def __init__(self, security_level):
        self.params = self.SecurityParameters[security_level]

        self.rmrs = RMRSCodeForHQC(rs_n=self.params.n1, rs_k=self.params.k // 8,
                                   rm_multiplicity=self.params.multiplicity, n=self.params.n)

    def generate_binary_vector_of_fixed_weight(self, xof, weight):
        support = xof_sample_k_indexes(xof, self.params.n, weight)
        v = zero_vector(GF(2), self.params.n)
        for s in support:
            v[s] = 1
        return v

    def vector_product(self, a, b):
        R = PolynomialRing(GF(2), 'x')
        x = R.gen()
        Q = R.quotient(x**self.params.n - 1)

        return vector(GF(2), Q(list(a)) * Q(list(b)))

    def keygen(self, randomness):
        xof = SHAKE256.new(randomness)
        h = random_vector(GF(2), self.params.n)
        x = self.generate_binary_vector_of_fixed_weight(xof, self.params.w)
        y = self.generate_binary_vector_of_fixed_weight(xof, self.params.w)
        s = x + self.vector_product(h, y)

        return (h, s), (x, y)

    def encrypt(self, pk, message, randomness):
        h, s = pk
        xof = SHAKE256.new(randomness)
        e = self.generate_binary_vector_of_fixed_weight(xof, self.params.w_e)
        r_1 = self.generate_binary_vector_of_fixed_weight(xof, self.params.w_r)
        r_2 = self.generate_binary_vector_of_fixed_weight(xof, self.params.w_r)
        u = r_1 + self.vector_product(h, r_2)
        v = self.rmrs.encode(message) + self.vector_product(s, r_2) + e

        return (u, v)

    def decrypt(self, sk, ciphertext):
        u, v = ciphertext
        x, y = sk
        c_prime = v - self.vector_product(u, y)

        return self.rmrs.decode(c_prime)


def test_hqc():

    for security_level in [1, 3, 5]:
        hqc = HQC_PKE_CPA(security_level)
        message = random_vector(GF(2), hqc.params.k)
        key_randomness = get_random_bytes(32)
        pk, sk = hqc.keygen(key_randomness)
        pk2, sk2 = hqc.keygen(key_randomness + b'2')
        encryption_randomness = get_random_bytes(32)
        ciphertext1 = hqc.encrypt(pk, message, encryption_randomness)
        # ciphertext1 = hqc.encrypt(pk2, message, encryption_randomness)
        decrypted = hqc.decrypt(sk, ciphertext1)
        assert decrypted == message

        # ciphertext2 = hqc.encrypt(pk, message, randomness)
        # assert ciphertext1 == ciphertext2
        # randomness2 = get_random_bytes(32)
        # ciphertext3 = hqc.encrypt(pk, message, randomness2)

        # assert ciphertext1 != ciphertext3
        print(f'HQC {security_level}: PASSED')
        # print(f'message = {"".join(map(str, message))}')