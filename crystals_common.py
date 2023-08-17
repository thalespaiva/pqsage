from sage.all import *


def mod_centered(v, modulo):
    v = int(v) % modulo
    if v <= modulo//2:
        return v
    return - (modulo - v)


def bit_rev(x, length):
    b = bin(x)[2:]
    b = '0' * (length - len(b)) + b
    return int(''.join(reversed(b)), 2)


def ntt_leveled_negacyclic_256(a, field, omega, n_levels):
    assert len(a) == 256
    omega = field(omega)
    assert omega.multiplicative_order() == 2**(n_levels + 1)

    a_hat = copy(a)
    for l in range(7, 7 - n_levels, -1):
        for i in range(0, 2**(7 - l)):
            phi = omega ** bit_rev(2**(7 - l) + i, n_levels)
            for j in range(i * 2**(l + 1), i * 2**(l + 1) + 2**l):
                t0 = a_hat[j]
                t1 = phi * a_hat[j + 2**l]
                a_hat[j] = t0 + t1
                a_hat[j + 2**l] = t0 - t1
    return vector(field, a_hat)


def inv_ntt_leveled_negacyclic_256(a_hat, field, omega, n_levels):
    assert len(a_hat) == 256
    omega = field(omega)
    assert omega.multiplicative_order() == 2**(n_levels + 1)

    a = copy(a_hat)
    for l in range(8 - n_levels, 8):
        for i in range(2**(7 - l)):
            phi = omega ** -bit_rev(2**(7 - l) + i, n_levels)
            for j in range(i * 2**(l + 1), i * 2**(l + 1) + 2**l):
                t0 = a[j] + a[j + 2**l]
                t1 = a[j] - a[j + 2**l]
                a[j] = t0
                a[j + 2**l] = phi * t1
    return vector(field, a) * field(2**n_levels)**(-1)


class PolynomialVector():

    def __init__(self, ntt_ring, poly_vec_coefficients, in_ntt_domain=False):
        assert all(len(p) == ntt_ring.n for p in poly_vec_coefficients)
        self.ntt_ring = ntt_ring
        self.poly_vec = [vector(ntt_ring.field, p) for p in poly_vec_coefficients]
        self.in_ntt_domain = in_ntt_domain

    def test_compatibility_of_domains(self, poly_vec2):
        assert self.ntt_ring.field == poly_vec2.ntt_ring.field
        assert self.in_ntt_domain == poly_vec2.in_ntt_domain

    def __add__(self, poly_vec2):
        self.test_compatibility_of_domains(poly_vec2)
        sum_poly_vec = [v1 + v2 for v1, v2 in zip(self.poly_vec, poly_vec2.poly_vec)]
        return PolynomialVector(self.ntt_ring, sum_poly_vec, in_ntt_domain=self.in_ntt_domain)

    def __sub__(self, poly_vec2):
        self.test_compatibility_of_domains(poly_vec2)
        sum_poly_vec = [v1 - v2 for v1, v2 in zip(self.poly_vec, poly_vec2.poly_vec)]
        return PolynomialVector(self.ntt_ring, sum_poly_vec)

    def __neg__(self):
        return PolynomialVector(self.ntt_ring, [-p for p in self.poly_vec])

    def __iter__(self):
        return iter(self.poly_vec)

    def _multiply_poly_vecs(self, poly_vec2):
        self.test_compatibility_of_domains(poly_vec2)

        if (self.in_ntt_domain == True):
            prod = sum(self.ntt_ring.poly_product_ntt_domain(p1, p2)
                       for p1, p2 in zip(self, poly_vec2))
            return prod

        else:
            raise NotImplementedError

    def _multiply_poly_vec_and_poly(self, poly):
        assert self.in_ntt_domain

        prod = [self.ntt_ring.poly_product_ntt_domain(poly, p) for p in self]
        return PolynomialVector(self.ntt_ring, prod, in_ntt_domain=True)

    def _multiply_poly_vec_by_scalar(self, field_element):
        return PolynomialVector(self.ntt_ring, [p * field_element for p in self], self.in_ntt_domain)

    def __mul__(self, poly_or_poly_vec_or_int):
        if isinstance(poly_or_poly_vec_or_int, PolynomialVector):
            return self._multiply_poly_vecs(poly_or_poly_vec_or_int)
        elif poly_or_poly_vec_or_int in self.ntt_ring.field:
            return self._multiply_poly_vec_by_scalar(poly_or_poly_vec_or_int)
        else:
            return self._multiply_poly_vec_and_poly(poly_or_poly_vec_or_int)

    def ntt(self):
        poly_vec_ntt = [self.ntt_ring.ntt(p) for p in self]
        return PolynomialVector(self.ntt_ring, poly_vec_ntt, in_ntt_domain=True)

    def inv_ntt(self):
        poly_vec = [self.ntt_ring.inv_ntt(p) for p in self]
        return PolynomialVector(self.ntt_ring, poly_vec, in_ntt_domain=False)

    def __repr__(self):
        return str(self.poly_vec)

    def as_bytes(self):
        out = b''
        n_bytes = ceil(log(self.ntt_ring.field.order(), 2**8))
        for poly in self:
            out += b''.join(int(c).to_bytes(n_bytes) for c in poly)
        return out

    def norm_infinity(self):
        def abs_value(x):
            return abs(mod_centered(x, self.ntt_ring.field.order()))
        return max(abs_value(i) for p in self for i in p)

    def __eq__(self, other):
        if not isinstance(other, PolynomialVector):
            return False
        return all(a == b for a, b in zip(self, other))
