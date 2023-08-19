from sage.all import *

from Crypto.Random import get_random_bytes
from Crypto.Hash import SHAKE256

from dataclasses import dataclass
from pseudorandom import xof_sample_k_indexes

@dataclass
class NTRUHPS_Parameters:
    n: int
    q: int
    d: int
    max_degree_t: int

class NTRU_DPKE_OWCPA:
    SecurityParameters = {
        1: NTRUHPS_Parameters(n=509, q=2048, d=254, max_degree_t=509 - 2),
        3: NTRUHPS_Parameters(n=677, q=2048, d=254, max_degree_t=677 - 2),
        5: NTRUHPS_Parameters(n=821, q=2048, d=254, max_degree_t=821 - 2),
    }

    def __init_rings(self):
        ring_mod_q = PolynomialRing(Integers(self.params.q), 'x')

        x = ring_mod_q.gen()
        phi = x**self.params.n - 1
        phi_1 = x - 1
        phi_n = sum(x**i for i in range(self.params.n))
        assert phi_n * phi_1 == phi

        self.Rq = ring_mod_q.quotient_ring(phi)
        self.Sq = ring_mod_q.quotient_ring(phi_n)
        self.S3 = ring_mod_q.change_ring(Integers(3)).quotient(phi_n)
        self.S2 = ring_mod_q.change_ring(Integers(2)).quotient(phi_n)
        self.phi_1 = phi_1

    def __init__(self, security_level):
        self.params = self.SecurityParameters[security_level]
        self.__init_rings()

    def centered(self, polynomial):
        modulo = polynomial.base_ring().order()

        def mod_centered(v):
            v = int(v) % modulo
            if v <= modulo // 2:
                return v
            return - (modulo - v)

        return [mod_centered(c) for c in polynomial]

    def to_Rq(self, polynomial):
        return self.Rq(self.centered(polynomial))

    def to_Sq(self, polynomial):
        return self.Sq(self.centered(polynomial))

    def to_S3(self, polynomial):
        return self.S3(self.centered(polynomial))

    def to_S2(self, polynomial):
        return self.S2(self.centered(polynomial))

    def Sq_inverse(self, a):
        assert is_power_of_two(self.params.q)

        a_in_Sq = self.to_Sq(a)
        v0 = self.to_Sq(self.to_S2(a).inverse())
        t = 1
        while t < log(self.params.q, 2):
            v0 = v0 * (2 - a_in_Sq * v0)
            t = 2*t
        assert (v0 * a_in_Sq) == 1

        return v0

    def gen_ternary_coeffs(self, xof):
        return [choice([-1, 0, 1]) for _ in range(self.params.max_degree_t + 1)]

    def gen_ternary_coeffs_for_d(self, xof, d):
        assert d % 2 == 0
        coeffs = [0] * (self.params.max_degree_t + 1)
        supp = xof_sample_k_indexes(xof, self.params.max_degree_t + 1, d)
        for i in range(d // 2):
            coeffs[supp[i]] = 1
            coeffs[supp[d//2 + i]] = -1

        return coeffs

    def keygen(self, randomness):
        xof = SHAKE256.new(randomness)
        f_in_s3 = self.S3(self.gen_ternary_coeffs(xof))
        g_in_s3 = self.S3(self.gen_ternary_coeffs_for_d(xof, self.params.d))
        f_inv_3 = f_in_s3.inverse()

        f = self.to_Rq(f_in_s3)
        g = self.to_Rq(g_in_s3)

        h = 3 * g * self.to_Rq(self.Sq_inverse(f))
        h_inv_q = self.to_Rq(self.Sq_inverse(h))

        return h, (f, f_inv_3, h_inv_q)

    def sample_plaintext(self, randomness):
        xof = SHAKE256.new(randomness)

        r = self.gen_ternary_coeffs(xof)
        m = self.gen_ternary_coeffs_for_d(xof, self.params.d)
        return r, m

    def encrypt(self, pk, plaintext):
        h = pk
        r_coeffs, m_coeffs = plaintext

        r = self.Rq(r_coeffs)
        m = self.Rq(m_coeffs)
        c = h * r + m

        return c

    def is_valid_plaintext(self, r, m):
        if (m.count(-1), m.count(1)) != (self.params.d//2, self.params.d//2):
            return False

        r_non_ternary_coefficients = len([c for c in r if c not in {-1, 0, 1}])
        if r_non_ternary_coefficients:
            return False

        return True

    def decrypt(self, sk, ciphertext):
        (f, f_inv_3, h_inv_q) = sk
        c = ciphertext

        if c.lift().mod(self.phi_1) != 0:
            return None

        a = (c * self.to_Rq(f))
        m = self.to_S3(a) * f_inv_3

        r = (c - self.to_Rq(m)) * h_inv_q

        m = self.centered(m)
        r = self.centered(self.to_Sq(r))

        if self.is_valid_plaintext(r, m):
            return r, m
        else:
            return None


def test_ntru():

    for security_level in [1, 3, 5]:
        ntru = NTRU_DPKE_OWCPA(security_level)
        keygen_randomness = get_random_bytes(32)
        plaintext_randomness = get_random_bytes(32)
        pk, sk = ntru.keygen(keygen_randomness)
        plaintext = ntru.sample_plaintext(plaintext_randomness)
        ciphertext = ntru.encrypt(pk, plaintext)
        decrypted = ntru.decrypt(sk, ciphertext)
        assert decrypted == plaintext

        print(f'NTRU {security_level}: PASSED')


if __name__ == '__main__':
    test_ntru()
