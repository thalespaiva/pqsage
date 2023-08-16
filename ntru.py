from sage.all import *

from Crypto.Random import get_random_bytes

from dataclasses import dataclass

@dataclass
class NTRUHPS_Parameters:
    n: int
    q: int
    d: int

class NTRUHPS_PKE_CPA:
    SecurityParameters = {
        1: NTRUHPS_Parameters(n=509, q=2048, d=254),
        3: NTRUHPS_Parameters(n=677, q=2048, d=254),
        5: NTRUHPS_Parameters(n=821, q=2048, d=254),
    }

    def __init__(self, security_level):
        self.params = self.SecurityParameters[security_level]

        self.ring_mod_q = PolynomialRing(Integers(self.params.q), 'x')
        self.ring_mod_3 = PolynomialRing(Integers(3), 'x')
        self.ring_mod_2 = PolynomialRing(Integers(2), 'x')

        self.x = self.ring_mod_q.gen()
        self.phi = self.x**self.params.n - 1
        self.phi_1 = self.x - 1
        self.phi_n = sum(self.x**i for i in range(self.params.n))

        assert self.phi_n * self.phi_1 == self.phi

        self.Rq = self.ring_mod_q.quotient_ring(self.phi)

        self.Sq = self.ring_mod_q.quotient_ring(self.phi_n)
        self.S3 = self.ring_mod_3.quotient_ring(self.phi_n)
        self.S2 = self.ring_mod_2.quotient_ring(self.phi_n)

    def mod_centered(self, v, modulo):
        v = int(v) % modulo
        if v <= modulo // 2:
            return v
        return - (modulo - v)

    def from_S3_to_Rq(self, poly):
        return self.Rq([self.mod_centered(c, 3) for c in poly])

    def generate_ternary_coefficients(self, max_degree):
        return [choice([-1, 0, 1]) for _ in range(max_degree)]

    def generate_ternary_coefficients_for_d(self, d, max_degree):
        assert d % 2 == 0
        coeffs = [0] * max_degree
        supp = sample(range(max_degree), d)
        for i in range(d // 2):
            coeffs[supp[i]] = 1
            coeffs[supp[d//2 + i]] = -1

        return coeffs

    def centered(self, polynomial):
        modulo = polynomial.base_ring().order()
        return [self.mod_centered(c, modulo) for c in polynomial]

    def Rq_inverse(self, a):
        assert is_power_of_two(self.params.q)

        v0 = self.centered(self.S2(list(a)).inverse())
        t = 1
        while t < log(self.params.q, 2):
            v0_in_Rq = self.Rq(v0)
            v0 = self.centered(v0_in_Rq * (2 - a * v0_in_Rq))
            t = 2*t

        return self.Rq(v0)

    def to_Rq(self, polynomial):
        return self.Rq(self.centered(polynomial))

    def from_Rq_to_Sq(self, poly):
        return self.Sq(self.centered(poly.mod(self.phi_1)))

    def from_Rq_to_S3(self, poly):
        return self.S3(self.centered(from_Rq_to_Sq(poly)))

    def keygen(self):
        f_in_s3 = self.S3(self.generate_ternary_coefficients(self.params.n - 2))
        g_in_s3 = self.S3(self.generate_ternary_coefficients_for_d(self.params.d,
                                                                   self.params.n - 2))
        f_inv_3 = f_in_s3.inverse()

        f = self.to_Rq(f_in_s3)
        g = self.to_Rq(g_in_s3)

        h = 3 * g * self.Rq_inverse(f)
        h_inv_q = self.Rq_inverse(h)

        return h, (f, None, f_inv_3, h_inv_q, g)

    def encrypt(self, pk, randomness):
        h = pk
        r = self.Rq(self.generate_ternary_coefficients(self.params.n - 2))
        m = self.Rq(self.generate_ternary_coefficients_for_d(self.params.d,
                                                             self.params.n - 2))

        c = h * r + m

        m = self.centered(self.from_Rq_to_Sq(m))
        r = self.centered(self.from_Rq_to_Sq(r))
        return (r, m), c

    def is_valid_plaintext(self, r, m):
        if (m.count(-1), m.count(1)) != (self.params.d//2, self.params.d//2):
            return False

        r_non_ternary_coefficients = len([c for c in r if c not in {-1, 0, 1}])
        if r_non_ternary_coefficients:
            return False

        return True

    def decrypt(self, sk, ciphertext):
        (f, f_inv_q, f_inv_3, h_inv_q, g) = sk
        c = ciphertext

        if c.lift().mod(self.phi_1) != 0:
            return None

        a = (c * self.to_Rq(f))
        m = self.S3(self.centered(a)) * f_inv_3

        r = (c - self.from_S3_to_Rq(m)) * h_inv_q

        m = self.centered(m)
        r = self.centered(self.from_Rq_to_Sq(r))

        if self.is_valid_plaintext(r, m):
            return r, m
        else:
            return None


def test_ntru():

    for security_level in [1, 3, 5]:
        ntru = NTRUHPS_PKE_CPA(security_level)
        pk, sk = ntru.keygen()
        # randomness = get_random_bytes(32)
        message, ciphertext = ntru.encrypt(pk, None)
        decrypted = ntru.decrypt(sk, ciphertext)
        assert decrypted == message

        print(f'NTRU {security_level}: PASSED')


if __name__ == '__main__':
    test_ntru()
