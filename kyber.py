from sage.all import *
from itertools import chain
from dataclasses import dataclass

from Crypto.Hash import SHAKE128
from Crypto.Hash import SHA3_512 as HASH_G
from Crypto.Hash import SHAKE256 as PRF
from Crypto.Random import get_random_bytes


def int_to_bits(a, length):
    str_bits = bin(a)[2:]
    padding_length = length - len(str_bits)
    return [int(b) for b in reversed(str_bits)] + [0] * padding_length

@dataclass
class KyberParameters:
    security_level: int
    q: int
    n: int
    k: int
    eta1: int
    eta2: int
    du: int
    dv: int


class Kyber():
    SecurityParameters = {
        # Security Level : parameters
        128: KyberParameters(
            security_level=128, q=3329, n=256, k=2, eta1=3, eta2=2, du=10, dv=4,
        ),
        192: KyberParameters(
            security_level=192, q=3329, n=256, k=3, eta1=2, eta2=2, du=10, dv=4,
        ),
        256: KyberParameters(
            security_level=256, q=3329, n=256, k=4, eta1=2, eta2=2, du=11, dv=5,
        ),
    }

    def __init__(self, security_level):
        assert(security_level in self.SecurityParameters)

        self.params = self.SecurityParameters[security_level]

        self.F = GF(self.params.q)
        self.polynomial_ring = PolynomialRing(self.F, 'x')
        self.nth_root_unity = self.F(17)

    def ntt(self, a):
        a_hat = zero_vector(self.F, self.params.n)

        a_poly = self.polynomial_ring(list(a))
        for i in range(self.params.n):
            a_hat[i] = a_poly(self.nth_root_unity**i)

        return a_hat


    def inv_ntt(self, a_hat):
        a = zero_vector(self.F, self.params.n)

        inv_n = self.F(self.params.n)**(-1)

        a_hat_poly = self.polynomial_ring(list(a_hat))
        for i in range(self.params.n):
            a[i] = inv_n * a_hat_poly(self.nth_root_unity**(-i))

        return a

    def gen_uniformly_random_polynomial_with_xof(self, rho, j, i):
        seed_bytes = rho + int(j).to_bytes(1) + int(i).to_bytes(1)
        xof = SHAKE128.new(seed_bytes)
        hat_a = [None] * self.params.n

        k = 0
        while k < self.params.n:
            b0, b1, b2 = [int.from_bytes(xof.read(1)) for _ in range(3)]

            d1 = b0 + 256 * (b1 % 16)
            d2 = (b1 // 16) + 16 * b2

            if d1 < self.params.q:
                hat_a[k] = d1
                k += 1
            if d2 < self.params.q and k < self.params.n:
                hat_a[k] = d2
                k += 1

        return vector(self.F, hat_a)

    def get_ntt_A_from_seed(self, rho):
        ntt_A = [[None] * self.params.k for _ in range(self.params.k)]
        for i in range(self.params.k):
            for j in range(self.params.k):
                ntt_A[i][j] = self.gen_uniformly_random_polynomial_with_xof(rho, j, i)

        return ntt_A

    def get_ntt_A_transpose_from_seed(self, rho):
        ntt_A = [[None] * self.params.k for _ in range(self.params.k)]
        for i in range(self.params.k):
            for j in range(self.params.k):
                ntt_A[i][j] = self.gen_uniformly_random_polynomial_with_xof(rho, i, j)

        return ntt_A

    def bytes_to_bits(self, byte_array):
        bits = []
        for b in byte_array:
            bits += int_to_bits(b, 8)
        return bits


    def centered_binomial_distribution(self, eta, seed):
        bytes_array = PRF.new(seed).read(64 * eta)
        bits = self.bytes_to_bits(bytes_array)

        f = []
        for i in range(self.params.n):
            index = 2 * i * eta
            a = sum(bits[index:index + eta])
            b = sum(bits[index + eta:index + 2*eta])

            f.append(a - b)
        return f

    def sample_polynomial_with_centered_binomial(self, eta, seed, base_counter):
        seed_counter_bytes = seed + int(base_counter).to_bytes(1)
        poly_coeffs = self.centered_binomial_distribution(eta, seed_counter_bytes)
        return vector(self.F, poly_coeffs), 1

    def sample_vector_with_centered_binomial(self, eta, seed, base_counter):
        v = []
        for i in range(self.params.k):
            seed_counter_bytes = seed + int(base_counter + i).to_bytes(1)
            poly_coeffs = self.centered_binomial_distribution(eta, seed_counter_bytes)
            v.append(vector(self.F, poly_coeffs))
        return v, self.params.k


    def sample_s_and_e(self, sigma):
        s = []
        counter = 0
        for i in range(self.params.k):
            poly_coeffs = self.centered_binomial_distribution(self.params.eta1, sigma + int(counter).to_bytes(1))
            s.append(vector(self.F, poly_coeffs))
            counter += 1

        e = []
        for i in range(self.params.k):
            poly_coeffs = self.centered_binomial_distribution(self.params.eta1, sigma + int(counter).to_bytes(1))
            e.append(vector(self.F, poly_coeffs))
            counter += 1

        return s, e

    def ntt_polynomial_product(self, ntt_poly1, ntt_poly2):
        return vector(self.F, [c1 * c2 for c1, c2 in zip(ntt_poly1, ntt_poly2)])

    def ntt_vectors_product(self, ntt_vector1, ntt_vector2):
        ntt_product = zero_vector(self.F, self.params.n)

        for i in range(self.params.k):
            ntt_product += self.ntt_polynomial_product(ntt_vector1[i], ntt_vector2[i])

        return ntt_product

    def ntt_matrix_ntt_vector_product(self, ntt_matrix, ntt_vector):
        ntt_result = [[None] * self.params.k for _ in range(self.params.k)]

        for i in range(self.params.k):
            # print(self.ntt_vectors_product(ntt_matrix[i], ntt_vector))
            ntt_result[i] = self.ntt_vectors_product(ntt_matrix[i], ntt_vector)


        return ntt_result

    def vector_sum(self, vector1, vector2):
        vector_sum = [None] * self.params.k

        for i in range(self.params.k):
            vector_sum[i] = vector1[i] + vector2[i]

        return vector_sum

    def keygen(self):
        d = get_random_bytes(32)
        hash_g_of_d = HASH_G.new(d).digest()
        rho, sigma = hash_g_of_d[:16], hash_g_of_d[16:]
        ntt_A = self.get_ntt_A_from_seed(rho)

        counter = 0
        s, counter = self.sample_vector_with_centered_binomial(self.params.eta1, sigma, counter)
        e, counter = self.sample_vector_with_centered_binomial(self.params.eta1, sigma, counter)

        ntt_s = [self.ntt(s_i) for s_i in s]
        ntt_e = [self.ntt(e_i) for e_i in e]

        ntt_t = self.vector_sum(self.ntt_matrix_ntt_vector_product(ntt_A, ntt_s), ntt_e)

        return (ntt_t, rho), (ntt_s)

    def ntt_vector(self, vector):
        return [self.ntt(v) for v in vector]

    def inv_ntt_vector(self, vector):
        return [self.inv_ntt(v) for v in vector]

    def compress(self, coefficients, d):
        return [self.compress_coefficient(c, d) for c in coefficients]

    def decompress(self, coefficients, d):
        return vector(self.F, [self.decompress_coefficient(c, d) for c in coefficients])

    def compress_coefficient(self, x, d):
        return mod(round(2**d / self.params.q * int(x)), 2**d)

    def decompress_coefficient(self, x, d):
        return round(self.params.q / 2**d * int(x))

    def encrypt(self, pk, message, randomness):
        (ntt_t, rho) = pk

        ntt_A_transpose = self.get_ntt_A_transpose_from_seed(rho)

        counter = 0
        r, counter = self.sample_vector_with_centered_binomial(self.params.eta1, randomness,
                                                               counter)
        e1, counter = self.sample_vector_with_centered_binomial(self.params.eta1, randomness,
                                                                counter)
        e2, counter  = self.sample_polynomial_with_centered_binomial(self.params.eta1, randomness,
                                                                     counter)

        ntt_r = self.ntt_vector(r)
        u = self.inv_ntt_vector(self.ntt_matrix_ntt_vector_product(ntt_A_transpose, ntt_r) + e1)

        encoded_message = self.decompress(message, 1)
        v = encoded_message + self.inv_ntt(self.ntt_vectors_product(ntt_t, ntt_r)) + e2

        u_compressed = [self.compress(u_i, self.params.du) for u_i in u]
        v_compressed = self.compress(v, self.params.dv)
        return (u_compressed, v_compressed)

    def decrypt(self, sk, ciphertext):
        ntt_s = sk

        u_compressed, v_compressed = ciphertext
        u = [self.decompress(u_i, self.params.du) for u_i in u_compressed]
        v = self.decompress(v_compressed, self.params.dv)

        ntt_u = kyber.ntt_vector(u)
        noisy_message = v - self.inv_ntt(self.ntt_vectors_product(ntt_s, ntt_u))

        return self.compress(noisy_message, 1)

