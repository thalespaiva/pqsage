from sage.all import *
from dataclasses import dataclass

from Crypto.Hash import SHAKE128
from Crypto.Hash import SHAKE256
from Crypto.Hash import SHA3_512 as HASH_G
from Crypto.Hash import SHAKE256 as XOF_H
from Crypto.Random import get_random_bytes


class PolynomialVector():

    def __init__(self, module, poly_vec_coefficients):
        self.base_module = module
        assert all(len(p) == module.n for p in poly_vec_coefficients)
        self.poly_vec = [vector(module, p) for p in poly_vec_coefficients]

    def __add__(self, that_poly_vec):





class DilithiumModule():

    def __init__(self):
        self.field = GF(8380417)
        self.n = 256
        self.omega_2n = self.field(1753)

    def bit_rev(self, x):
        b = bin(x)[2:]
        b = '0' * (8 - len(b)) + b
        return int(''.join(reversed(b)), 2)

    def ntt_polynomial(self, a):
        a_hat = copy(a)
        for l in range(7, -1, -1):
            for i in range(0, 2**(7 - l)):
                phi = self.omega_2n ** self.bit_rev(2**(7 - l) + i)
                for j in range(i * 2**(l + 1), i * 2**(l + 1) + 2**l):
                    t0 = a_hat[j]
                    t1 = phi * a_hat[j + 2**l]
                    a_hat[j] = t0 + t1
                    a_hat[j + 2**l] = t0 - t1
        return a_hat

    def inv_ntt_polynomial(self, a_hat):
        a = copy(a_hat)
        for l in range(8):
            for i in range(2**(7 - l)):
                phi = self.omega_2n ** -self.bit_rev(2**(7 - l) + i)
                for j in range(i * 2**(l + 1), i * 2**(l + 1) + 2**l):
                    t0 = a[j] + a[j + 2**l]
                    t1 = a[j] - a[j + 2**l]
                    a[j] = t0
                    a[j + 2**l] = phi * t1
        return vector(self.field, a) * self.field(self.n)**-1

    def poly_product_ntt_domain(self, a_hat, b_hat):
        return vector(self.field, [c_a * c_b for c_a, c_b in zip(a_hat, b_hat)])

    def dot_product_ntt_domain(self, poly_vec_a_hat, poly_vec_b_hat):
        return sum(self.poly_product_ntt_domain(poly_a, poly_b)
                   for poly_a, poly_b in zip(poly_vec_a_hat, poly_vec_b_hat))

    def matrix_vector_product_ntt_domain(self, matrix, poly_vec):
        return [self.dot_product_ntt_domain(poly_vec_row, poly_vec) for poly_vec_row in matrix]

    def ntt(self, poly_vector):
        return [self.ntt_polynomial(v) for v in poly_vector]

    def inv_ntt(self, poly_vector_hat):
        return [self.inv_ntt_polynomial(v) for v in poly_vector_hat]

    def poly_vector_sum(self, poly_vec_a, poly_vec_b):
        return [vector(self.field, poly_a) + vector(self.field, poly_b)
                for poly_a, poly_b in zip(poly_vec_a, poly_vec_b)]

    def poly_vector_sub(self, poly_vec_a, poly_vec_b):
        return [vector(self.field, poly_a) - vector(self.field, poly_b)
                for poly_a, poly_b in zip(poly_vec_a, poly_vec_b)]

    def poly_vector_as_bytes(self, poly_vec):
        out = b''
        n_bytes = ceil(log(self.field.order(), 2**8))
        for poly in poly_vec:
            out += b''.join(int(c).to_bytes(n_bytes) for c in poly)
        return out

    def poly_vector_poly_product_ntt_domain(self, poly_vec, poly):
        return [self.poly_product_ntt_domain(p, poly) for p in poly_vec]

    def poly_vector_poly_product_ntt_domain_to_normal(self, poly_vec, poly):
        ntt_prod = poly_vector_poly_product_ntt_domain(poly_vec, poly)
        return self.inv_ntt(ntt_prod)

    def norm_infinity(self, poly_vec):
        return max(abs(c) for c in poly for poly in poly_vector)

    def minus(self, poly_vec):
        return [-vector(self.field, p) for p in poly_vec]

@dataclass
class DilithiumParameters:
    security_level: int
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
        # Security Level : parameters
        2: DilithiumParameters(
            security_level=2, q=8380417, d=13, tau=39, gamma1=2**17, gamma2=95232,
            n=256, k=4, l=4, eta=2, beta=78, omega=80,
        ),
        3: DilithiumParameters(
            security_level=3, q=8380417, d=13, tau=49, gamma1=2**19, gamma2=261888,
            n=256, k=6, l=5, eta=4, beta=196, omega=55,
        ),
        5: DilithiumParameters(
            security_level=5, q=8380417, d=13, tau=60, gamma1=2**19, gamma2=261888,
            n=256, k=8, l=7, eta=2, beta=120, omega=75,
        )
    }

    def __init__(self, security_level):
        assert(security_level in self.SecurityParameters)

        self.params = self.SecurityParameters[security_level]

        self.F = GF(self.params.q)
        self.module = DilithiumModule()

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
            for j in range(self.params.l):
                ntt_A[i][j] = self.gen_uniformly_random_polynomial_with_xof(rho, j, i)

        return ntt_A

    def mod_centered(self, v, modulo):
        v = v % modulo
        if v <= modulo//2:
            return v
        return - (modulo - v)

    def power2round_poly_vector(self, poly_vector, d):

        def power2round(r, d):
            r = int(r) % self.params.q
            r0 = self.mod_centered(r, 2**d)
            return (r - r0)//2**d, r0

        poly_vector0 = [[] for _ in poly_vector]
        poly_vector1 = [[] for _ in poly_vector]
        for poly in poly_vector:
            for r in poly:
                r1, r0 = power2round(r, d)
                poly_vector0[-1].append(r0)
                poly_vector1[-1].append(r1)

        return poly_vector1, poly_vector0

    def expand_S(self, rho_prime):
        # shake256 = SHAKE256.new(rho_prime)
        s_1 = []
        for i in range(self.params.l):
            s_1.append([])
            for j in range(self.params.n):
                s_1[i].append(randint(-self.params.eta, self.params.eta))

        s_2 = []
        for i in range(self.params.k):
            s_2.append([])
            for j in range(self.params.n):
                s_2[i].append(randint(-self.params.eta, self.params.eta))

        return s_1, s_2

    def keygen(self):
        zeta = get_random_bytes(32)
        xof_h = XOF_H.new(zeta)
        rho = xof_h.read(32)
        rho_prime = xof_h.read(64)
        K = xof_h.read(32)

        ntt_A = self.get_ntt_A_from_seed(rho)
        s1, s2 = self.expand_S(rho_prime)
        ntt_s1 = self.module.ntt(s1)

        ntt_A_times_s1 = self.module.matrix_vector_product_ntt_domain(ntt_A, ntt_s1)
        t = self.module.poly_vector_sum(self.module.inv_ntt(ntt_A_times_s1), s2)
        t1, t0 = self.power2round_poly_vector(t, self.params.d)
        tr = self.hash_H(rho + self.module.poly_vector_as_bytes(t1), 32)

        return (rho, t1), (rho, K, tr, s1, s2, t0)

    def hash_H(self, seed_bytes, n_bytes):
        xof_h = XOF_H.new(seed_bytes)
        return xof_h.read(n_bytes)

    def sample_in_ball(self, c_tilde):
        xof = SHAKE256.new(c_tilde)
        c = [0] * 256
        for i in range(256 - self.params.tau, 256):
            j = int.from_bytes(xof.read(1))
            s = int.from_bytes(xof.read(1)) & 1
            c[i] = c[j]
            c[j] = (-1)**s

        return c

    def decompose(self, r, alpha):
        r = int(r) % self.params.q
        r0 = self.mod_centered(r, alpha)
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

    def use_hint_coefficient(h, r, alpha):
        m = (self.params.q - 1) // alpha
        (r1, r0) = self.decompose(r, alpha)
        if h and r0 > 0:
            return (r1 + 1) % m
        if h and r0 <= 0:
            return (r1 - 1) % m
        return r1

    def high_bits(self, r, alpha):
        return [[self.high_bits_coefficient(c, alpha) for c in poly] for poly in r]

    def low_bits(self, r, alpha):
        return [[self.low_bits_coefficient(c, alpha) for c in poly] for poly in r]

    def make_hint(self, z, r, alpha):
        return [[self.make_hint_coefficient(c_z, c_r, alpha) for c_z, c_r in zip(poly_z, poly_r)]
                for poly_z, poly_r in zip(z, r)]

    def use_hint(self, h, r, alpha):
        return [[self.use_hint_coefficient(c_h, c_r, alpha) for c_h, c_r in zip(poly_h, poly_r)]
                for poly_h, poly_r in zip(h, r)]




    def sign(sk, message_bytes):
        (rho, K, tr, s1, s2, t0) = sk

        ntt_A = self.get_ntt_A_from_seed(rho)
        mu = self.hash_H(tr + M)
        kappa = 0
        rho_prime = get_random_bytes(64)

        (z, h) = (None, None)
        while (z, h) == (None, None):
            y = self.expand_mask(rho_prime, kappa)
            ntt_y = self.module.ntt(y)
            w = self.module.matrix_vector_product_ntt_domain(ntt_A, ntt_y)
            w1 = self.high_bits(w, 2 * self.params.gamma2)

            c_tilde = self.hash_H(mu + self.module.poly_vector_as_bytes(w1))
            c = self.sample_in_ball(c_tilde)
            hat_c = self.module.ntt_polynomial(c)
            c_s1_hat = self.module.poly_vector_poly_product_ntt_domain(s1, hat_c)
            z = self.module.poly_vector_sum(y, self.module.inv_ntt(c_s1_hat))

            z_norm_condition = (self.module.norm_infinity(z) >=
                                self.params.gamma_1 - self.params.beta)
            r0_norm_condition = (self.module.norm_infinity(r0) >=
                                 self.params.gamma_2 - self.params.beta)

            if z_norm_condition or r0_norm_condition:
                (z, h) = (None, None)
            else:
                ct0 = self.module.poly_vector_poly_product_ntt_domain_to_normal(t0, hat_c)
                cs2 = self.module.poly_vector_poly_product_ntt_domain_to_normal(s2, hat_c)

                h = self.make_hint(self.module.poly_vector_sub(ct0, w - cs2), 2 * self.params.gamma2)


            kappa += self.params.l

        return (c_tilde, z, h)

    def verify(pk, message_bytes, signature):
        (rho, t1) = pk
        (c_tilde, z, h) = signature

        ntt_A = self.get_ntt_A_from_seed(rho)


dilithium = Dilithium(2)