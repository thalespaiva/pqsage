from sage.all import *
from itertools import chain
from dataclasses import dataclass

from Crypto.Hash import SHAKE128
from Crypto.Hash import SHA3_512 as HASH_G
from Crypto.Hash import SHAKE256 as PRF
from Crypto.Random import get_random_bytes

from crystals_common import PolynomialVector
from crystals_common import ntt_leveled_negacyclic_256
from crystals_common import inv_ntt_leveled_negacyclic_256
from crystals_common import bit_rev


def int_to_bits(a, length):
    str_bits = bin(a)[2:]
    padding_length = length - len(str_bits)
    return [int(b) for b in reversed(str_bits)] + [0] * padding_length


class KyberNTTRing():

    def __init__(self):
        self.field = GF(3329)
        self.n = 256
        self.omega_n = self.field(17)
        self.polynomial_ring = PolynomialRing(self.field, 'x')
        self.x = self.polynomial_ring.gen()

    def ntt(self, a):
        return ntt_leveled_negacyclic_256(a, self.field, self.omega_n, 7)

    def inv_ntt(self, a_hat):
        return inv_ntt_leveled_negacyclic_256(a_hat, self.field, self.omega_n, 7)

    def poly_product_ntt_domain(self, a_hat, b_hat):

        prod = [None] * 256
        for i in range(0, 256, 2):
            pa = a_hat[i + 1]*self.x + a_hat[i]
            pb = b_hat[i + 1]*self.x + b_hat[i]

            pol_prod = (pa * pb).mod(self.x**2 - self.omega_n**(2*bit_rev(i//2, 7) + 1))
            prod[i + 1] = pol_prod[1]
            prod[i] = pol_prod[0]

        return vector(self.field, prod)

    def dot_product_ntt_domain(self, poly_vec_a_hat, poly_vec_b_hat):
        return sum(self.poly_product_ntt_domain(poly_a, poly_b)
                   for poly_a, poly_b in zip(poly_vec_a_hat, poly_vec_b_hat))

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
        self.ntt_ring = KyberNTTRing()

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

        return vector(self.ntt_ring.field, hat_a)

    def get_ntt_A_from_seed(self, rho):
        ntt_A = [[None] * self.params.k for _ in range(self.params.k)]
        for i in range(self.params.k):
            for j in range(self.params.k):
                ntt_A[i][j] = self.gen_uniformly_random_polynomial_with_xof(rho, j, i)

        return [PolynomialVector(self.ntt_ring, vec_A, in_ntt_domain=True) for vec_A in ntt_A]

    def get_ntt_A_transpose_from_seed(self, rho):
        ntt_A = [[None] * self.params.k for _ in range(self.params.k)]
        for i in range(self.params.k):
            for j in range(self.params.k):
                ntt_A[i][j] = self.gen_uniformly_random_polynomial_with_xof(rho, i, j)

        return [PolynomialVector(self.ntt_ring, vec_A, in_ntt_domain=True) for vec_A in ntt_A]

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

    def to_poly_vec(self, poly_vec):
        return PolynomialVector(self.ntt_ring, poly_vec)

    def sample_polynomial_with_centered_binomial(self, eta, seed, base_counter):
        seed_counter_bytes = seed + int(base_counter).to_bytes(1)
        poly_coeffs = self.centered_binomial_distribution(eta, seed_counter_bytes)
        return vector(self.ntt_ring.field, poly_coeffs), 1

    def sample_vector_with_centered_binomial(self, eta, seed, base_counter):
        v = []
        for i in range(self.params.k):
            seed_counter_bytes = seed + int(base_counter + i).to_bytes(1)
            poly_coeffs = self.centered_binomial_distribution(eta, seed_counter_bytes)
            v.append(vector(self.ntt_ring.field, poly_coeffs))
        return self.to_poly_vec(v), base_counter + self.params.k


    def matrix_poly_vec_product(self, ntt_matrix, poly_vec):
        return PolynomialVector(self.ntt_ring, [ntt_vec * poly_vec for ntt_vec in ntt_matrix],
                                in_ntt_domain=True)

    def keygen(self):
        d = get_random_bytes(32)
        hash_g_of_d = HASH_G.new(d).digest()
        rho, sigma = hash_g_of_d[:16], hash_g_of_d[16:]
        ntt_A = self.get_ntt_A_from_seed(rho)

        counter = 0
        s, counter = self.sample_vector_with_centered_binomial(self.params.eta1, sigma, counter)
        e, counter = self.sample_vector_with_centered_binomial(self.params.eta1, sigma, counter)
        ntt_s = s.ntt()
        ntt_e = e.ntt()

        ntt_t = self.matrix_poly_vec_product(ntt_A, ntt_s) + ntt_e
        return (ntt_t, rho), (ntt_s)

    def compress(self, coefficients, d):
        return [self.compress_coefficient(c, d) for c in coefficients]

    def decompress(self, coefficients, d):
        return vector(self.ntt_ring.field, [self.decompress_coefficient(c, d) for c in coefficients])

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
        ntt_r = r.ntt()
        u = self.matrix_poly_vec_product(ntt_A_transpose, ntt_r).inv_ntt() + e1

        encoded_message = self.decompress(message, 1)
        v = encoded_message + self.ntt_ring.inv_ntt(ntt_t * ntt_r) + e2

        u_compressed = [self.compress(u_i, self.params.du) for u_i in u]
        v_compressed = self.compress(v, self.params.dv)
        return (u_compressed, v_compressed)

    def decrypt(self, sk, ciphertext):
        ntt_s = sk

        u_compressed, v_compressed = ciphertext
        u = self.to_poly_vec([self.decompress(u_i, self.params.du) for u_i in u_compressed])
        v = self.decompress(v_compressed, self.params.dv)

        ntt_u = u.ntt()
        noisy_message = v - self.ntt_ring.inv_ntt(ntt_s * ntt_u)

        return vector(self.compress(noisy_message, 1))


def test_kyber():

    for security_level in [128, 192, 256]:
        kyber = Kyber(security_level)
        message = random_vector(GF(2), 256).lift()
        pk, sk = kyber.keygen()
        randomness = get_random_bytes(32)
        ciphertext1 = kyber.encrypt(pk, message, randomness)
        decrypted = kyber.decrypt(sk, ciphertext1)
        assert decrypted == message

        ciphertext2 = kyber.encrypt(pk, message, randomness)
        assert ciphertext1 == ciphertext2
        randomness2 = get_random_bytes(32)
        ciphertext3 = kyber.encrypt(pk, message, randomness2)

        assert ciphertext1 != ciphertext3
        print(f'Kyber {security_level}: PASSED')
        print(f'message = {"".join(map(str, message))}')
