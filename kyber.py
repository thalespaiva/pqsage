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
from crystals_common import mod_centered

from pseudorandom import xof_random_bit
from pseudorandom import xof_random_int_mod

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

@dataclass
class KyberParameters:
    q: int
    n: int
    k: int
    eta1: int
    eta2: int
    du: int
    dv: int

class Kyber():
    SecurityParameters = {
        1: KyberParameters(
            q=3329, n=256, k=2, eta1=3, eta2=2, du=10, dv=4,
        ),
        3: KyberParameters(
            q=3329, n=256, k=3, eta1=2, eta2=2, du=10, dv=4,
        ),
        5: KyberParameters(
            q=3329, n=256, k=4, eta1=2, eta2=2, du=11, dv=5,
        ),
    }

    def __init__(self, security_level):
        self.params = self.SecurityParameters[security_level]
        self.ntt_ring = KyberNTTRing()

    def get_ntt_A_from_seed(self, rho, transpose=False):
        ntt_A = [[None] * self.params.k for _ in range(self.params.k)]
        for i in range(self.params.k):
            for j in range(self.params.k):
                if not transpose:
                    seed_bytes = rho + int(j).to_bytes(1) + int(i).to_bytes(1)
                else:
                    seed_bytes = rho + int(i).to_bytes(1) + int(j).to_bytes(1)
                xof = SHAKE128.new(seed_bytes)
                coeffs = [xof_random_int_mod(xof, self.params.q) for i in range(self.params.n)]
                ntt_A[i][j] = coeffs

        return [PolynomialVector(self.ntt_ring, vec_A, in_ntt_domain=True) for vec_A in ntt_A]

    def get_n_samples_from_cbd(self, eta, seed):
        xof = PRF.new(seed)
        f = []
        for i in range(self.params.n):
            a = sum(xof_random_bit(xof) for _ in range(eta))
            b = sum(xof_random_bit(xof) for _ in range(eta))
            f.append(a - b)
        return f

    def to_poly_vec(self, poly_vec):
        return PolynomialVector(self.ntt_ring, poly_vec)

    def sample_polynomial_from_cbd(self, eta, seed, base_counter):
        seed_counter_bytes = seed + int(base_counter).to_bytes(1)
        poly_coeffs = self.get_n_samples_from_cbd(eta, seed_counter_bytes)
        return vector(self.ntt_ring.field, poly_coeffs), 1

    def sample_vector_from_cbd(self, eta, seed, base_counter):
        v = []
        for i in range(self.params.k):
            seed_counter_bytes = seed + int(base_counter + i).to_bytes(1)
            v.append(self.get_n_samples_from_cbd(eta, seed_counter_bytes))
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
        s, counter = self.sample_vector_from_cbd(self.params.eta1, sigma, counter)
        e, counter = self.sample_vector_from_cbd(self.params.eta1, sigma, counter)
        ntt_s = s.ntt()
        ntt_e = e.ntt()

        ntt_t = self.matrix_poly_vec_product(ntt_A, ntt_s) + ntt_e
        return (ntt_t, rho), (ntt_s)

    def compress(self, coefficients, d):
        def compress_coefficient(x, d):
            return mod(round(2**d / self.params.q * int(x)), 2**d)
        return [compress_coefficient(c, d) for c in coefficients]

    def decompress(self, coefficients, d):
        def decompress_coefficient(x, d):
            return round(self.params.q / 2**d * int(x))
        return vector(self.ntt_ring.field, [decompress_coefficient(c, d) for c in coefficients])

    def encode_message(self, message):
        return vector(self.ntt_ring.field, [bit * self.params.q//2 for bit in message])

    def decode_message(self, noisy_message):
        def decode_coeff(c):
            if abs(int(mod_centered(c, self.params.q))) <= self.params.q//4:
                return 0
            return 1
        return vector(self.ntt_ring.field, [decode_coeff(c) for c in noisy_message])


    def encrypt(self, pk, message, randomness):
        (ntt_t, rho) = pk

        ntt_A_transpose = self.get_ntt_A_from_seed(rho, transpose=True)

        counter = 0
        r, counter = self.sample_vector_from_cbd(self.params.eta1, randomness, counter)
        e1, counter = self.sample_vector_from_cbd(self.params.eta2, randomness, counter)
        e2, counter  = self.sample_polynomial_from_cbd(self.params.eta2, randomness, counter)
        ntt_r = r.ntt()
        u = self.matrix_poly_vec_product(ntt_A_transpose, ntt_r).inv_ntt() + e1

        encoded_message = self.encode_message(message)
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

        return self.decode_message(noisy_message)


def test_kyber():

    for security_level in [1, 3, 5]:
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
