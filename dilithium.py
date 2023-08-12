from sage.all import *
from dataclasses import dataclass

from Crypto.Hash import SHAKE128
from Crypto.Hash import SHAKE256
from Crypto.Hash import SHA3_512 as HASH_G
from Crypto.Hash import SHAKE256 as XOF_H
from Crypto.Random import get_random_bytes

from crystals_common import PolynomialVector
from crystals_common import mod_centered
from crystals_common import ntt_leveled_negacyclic_256
from crystals_common import inv_ntt_leveled_negacyclic_256

from pseudorandom import xof_randrange
from pseudorandom import xof_random_int_mod
from pseudorandom import xof_random_bit

class DilithiumNTTRing():

    def __init__(self):
        self.field = GF(8380417)
        self.n = 256
        self.omega_2n = self.field(1753)

    def ntt(self, a):
        return ntt_leveled_negacyclic_256(a, self.field, self.omega_2n, 8)

    def inv_ntt(self, a_hat):
        return inv_ntt_leveled_negacyclic_256(a_hat, self.field, self.omega_2n, 8)

    def poly_product_ntt_domain(self, a_hat, b_hat):
        return vector(self.field, [c_a * c_b for c_a, c_b in zip(a_hat, b_hat)])


@dataclass
class DilithiumParameters:
    q: int
    d: int
    tau: int
    gamma1: int
    gamma2: int
    n: int
    k: int
    l: int
    eta: int
    beta: int
    omega: int

class Dilithium():
    SecurityParameters = {
        2: DilithiumParameters(
            q=8380417, d=13, tau=39, gamma1=2**17, gamma2=95232,
            n=256, k=4, l=4, eta=2, beta=78, omega=80),
        3: DilithiumParameters(
            q=8380417, d=13, tau=49, gamma1=2**19, gamma2=261888,
            n=256, k=6, l=5, eta=4, beta=196, omega=55),
        5: DilithiumParameters(
            q=8380417, d=13, tau=60, gamma1=2**19, gamma2=261888,
            n=256, k=8, l=7, eta=2, beta=120, omega=75),
    }

    def __init__(self, security_level):
        assert(security_level in self.SecurityParameters)

        self.params = self.SecurityParameters[security_level]
        self.ntt_ring = DilithiumNTTRing()

    def get_ntt_A_from_seed(self, rho, transpose=False):
        ntt_A = [[None] * self.params.l for _ in range(self.params.k)]
        for i in range(self.params.k):
            for j in range(self.params.l):
                seed_bytes = rho + int(j).to_bytes(1) + int(i).to_bytes(1)
                xof = SHAKE128.new(seed_bytes)
                coeffs = [xof_random_int_mod(xof, self.params.q) for i in range(self.params.n)]
                ntt_A[i][j] = coeffs

        return [PolynomialVector(self.ntt_ring, vec_A, in_ntt_domain=True) for vec_A in ntt_A]

    def power2round_poly_vector(self, poly_vector, d):

        def power2round(r, d):
            r = int(r) % self.params.q
            r0 = mod_centered(r, 2**d)
            return (r - r0)//2**d, r0

        poly_vector0 = [[] for _ in poly_vector]
        poly_vector1 = [[] for _ in poly_vector]
        for i, poly in enumerate(poly_vector):
            for r in poly:
                r1, r0 = power2round(r, d)
                poly_vector0[i].append(r0)
                poly_vector1[i].append(r1)
        return self.to_poly_vec(poly_vector1), self.to_poly_vec(poly_vector0)

    def expand_S(self, rho_prime):
        shake256 = SHAKE256.new(rho_prime)
        s_1 = [[xof_randrange(shake256, -self.params.eta, self.params.eta + 1)
                    for j in range(self.params.n)] for i in range(self.params.l)]
        s_2 = [[xof_randrange(shake256, -self.params.eta, self.params.eta + 1)
                    for j in range(self.params.n)] for i in range(self.params.k)]

        return self.to_poly_vec(s_1), self.to_poly_vec(s_2)

    def matrix_poly_vec_product(self, ntt_matrix, poly_vec):
        return PolynomialVector(self.ntt_ring, [ntt_vec * poly_vec for ntt_vec in ntt_matrix],
                                in_ntt_domain=True)

    def keygen(self):
        zeta = get_random_bytes(32)
        xof_h = XOF_H.new(zeta)
        rho = xof_h.read(32)
        rho_prime = xof_h.read(64)
        K = xof_h.read(32)

        ntt_A = self.get_ntt_A_from_seed(rho)
        s1, s2 = self.expand_S(rho_prime)
        ntt_s1 = s1.ntt()

        t = self.matrix_poly_vec_product(ntt_A, ntt_s1).inv_ntt() + s2
        t1, t0 = self.power2round_poly_vector(t, self.params.d)
        tr = self.hash_H(rho + t1.as_bytes(), 32)

        assert (t1 * 2**self.params.d == t - t0)
        return (rho, t1), (rho, K, tr, s1, s2, t0)

    def hash_H(self, seed_bytes, n_bytes):
        xof_h = XOF_H.new(seed_bytes)
        return xof_h.read(n_bytes)

    def sample_in_ball(self, c_tilde):
        xof = SHAKE256.new(c_tilde)
        c = [0] * 256
        for i in range(256 - self.params.tau, 256):
            j = xof_randrange(xof, 0, i + 1)
            c[i] = c[j]
            c[j] = (-1)**xof_random_bit(xof)

        assert(c.count(1) + c.count(-1) == self.params.tau)
        return c

    def decompose(self, r, alpha):
        r = int(r) % self.params.q
        r0 = mod_centered(r, alpha)
        if r - r0 == self.params.q - 1:
            return (0, r0 - 1)
        return (r - r0) // alpha, r0

    def make_hint_coefficient(self, z, r, alpha):
        r1 = self.high_bits_coefficient(r, alpha)
        v1 = self.high_bits_coefficient(r + z, alpha)
        return int(r1 != v1)

    def high_bits_coefficient(self, r, alpha):
        return self.decompose(r, alpha)[0]

    def low_bits_coefficient(self, r, alpha):
        return self.decompose(r, alpha)[1]

    def use_hint_coefficient(self, h, r, alpha):
        m = (self.params.q - 1) // alpha
        (r1, r0) = self.decompose(r, alpha)
        if h and r0 > 0:
            return (r1 + 1) % m
        if h and r0 <= 0:
            return (r1 - 1) % m
        return r1

    def to_poly_vec(self, poly_vec):
        return PolynomialVector(self.ntt_ring, poly_vec)

    def high_bits(self, r, alpha):
        v = [[self.high_bits_coefficient(c, alpha) for c in poly] for poly in r]
        return self.to_poly_vec(v)

    def low_bits(self, r, alpha):
        v = [[self.low_bits_coefficient(c, alpha) for c in poly] for poly in r]
        return self.to_poly_vec(v)

    def make_hint(self, z, r, alpha):
        v = [[self.make_hint_coefficient(c_z, c_r, alpha) for c_z, c_r in zip(poly_z, poly_r)]
                for poly_z, poly_r in zip(z, r)]
        return self.to_poly_vec(v)

    def use_hint(self, h, r, alpha):
        v = [[self.use_hint_coefficient(c_h, c_r, alpha) for c_h, c_r in zip(poly_h, poly_r)]
              for poly_h, poly_r in zip(h, r)]
        return self.to_poly_vec(v)

    def expand_mask(self, rhoprime, kappa):
        xof = SHAKE256.new(rhoprime + kappa)
        n_bytes = ceil(log(2 * self.params.gamma1, 2**8))
        assert is_power_of_two(self.params.gamma1)

        y = [[] for _ in range(self.params.l)]
        for i in range(self.params.l):
            for j in range(self.params.n):
                value = int.from_bytes(xof.read(n_bytes)) % (2 * self.params.gamma1)
                y[i].append(value - self.params.gamma1)

        return PolynomialVector(self.ntt_ring, y)

    def sign(self, sk, message_bytes):
        (rho, K, tr, s1, s2, t0) = sk

        ntt_A = self.get_ntt_A_from_seed(rho)
        mu = self.hash_H(tr + message_bytes, 64)

        kappa = 0
        rho_prime = get_random_bytes(64)

        s1_ntt = s1.ntt()
        s2_ntt = s2.ntt()
        t0_ntt = t0.ntt()

        (z, h) = (None, None)
        while (z, h) == (None, None):
            y = self.expand_mask(rho_prime, kappa.to_bytes(32))
            y_ntt = y.ntt()
            w = self.matrix_poly_vec_product(ntt_A, y_ntt).inv_ntt()
            w1 = self.high_bits(w, 2 * self.params.gamma2)

            c_tilde = self.hash_H(mu + w1.as_bytes(), 32)
            c = self.sample_in_ball(c_tilde)
            c_ntt = self.ntt_ring.ntt(c)
            z = y + (s1_ntt * c_ntt).inv_ntt()
            r0 = self.low_bits(w - (s2_ntt * c_ntt).inv_ntt(), 2 * self.params.gamma2)
            z_norm_condition = (z.norm_infinity() >= self.params.gamma1 - self.params.beta)
            r0_norm_condition = (r0.norm_infinity() >= self.params.gamma2 - self.params.beta)

            if z_norm_condition or r0_norm_condition:
                (z, h) = (None, None)

            else:
                ct0 = (t0_ntt * c_ntt).inv_ntt()
                cs2 = (s2_ntt * c_ntt).inv_ntt()
                h = self.make_hint(-ct0, w - cs2 + ct0, 2 * self.params.gamma2)

                n_ones_in_h = sum(p.hamming_weight() for p in h)
                if ct0.norm_infinity() >= self.params.gamma2 or n_ones_in_h > self.params.omega:
                    (z, h) = (None, None)
            kappa += self.params.l

        assert(self.use_hint(h, w - cs2 + ct0, 2 * self.params.gamma2) == w1)

        return (c_tilde, z, h)

    def verify(self, pk, message_bytes, signature):
        (rho, t1) = pk
        (c_tilde, z, h) = signature

        ntt_A = self.get_ntt_A_from_seed(rho)
        mu = self.hash_H(self.hash_H(rho + t1.as_bytes(), 32) + message_bytes, 64)
        c = self.sample_in_ball(c_tilde)

        z_ntt = z.ntt()
        c_ntt = self.ntt_ring.ntt(c)
        t1_ntt = t1.ntt()

        r = self.matrix_poly_vec_product(ntt_A, z_ntt) - ((t1_ntt * c_ntt) * (2**self.params.d))
        w1 = self.use_hint(h, r.inv_ntt(), 2 * self.params.gamma2)

        if (z.norm_infinity() >= self.params.gamma1 - self.params.beta):
            return False

        if (c_tilde != self.hash_H(mu + w1.as_bytes(), 32)):
            return False

        if sum(p.hamming_weight() for p in h) > self.params.omega:
            return False

        return True


def test_dilithium():

    for security_level in [2, 3, 5]:
        print(f'Testing Dilithium {security_level}')
        dilithium = Dilithium(security_level)
        message = get_random_bytes(100)
        pk, sk = dilithium.keygen()
        signature = dilithium.sign(sk, message)
        verification = dilithium.verify(pk, message, signature)
        assert verification is True

        verification2 = dilithium.verify(pk, message + b'a', signature)
        assert verification2 is False

        signature2 = dilithium.sign(sk, message + b'a')

        verification2 = dilithium.verify(pk, message, signature2)
        assert verification2 == False

        print(f'Dilithium {security_level}: PASSED')
