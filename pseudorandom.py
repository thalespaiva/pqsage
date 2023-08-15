from sage.all import *

MAX_MOD = 2**256
MAX_MOD_NBYTES = ceil(log(MAX_MOD, 2**8))

def xof_random_bit(xof):
    byte = int.from_bytes(xof.read(1))
    return (byte & 1)

def xof_random_int_mod(xof, mod):
    assert mod < MAX_MOD

    bias_region = MAX_MOD - (MAX_MOD % mod)
    v = int.from_bytes(xof.read(MAX_MOD_NBYTES))
    while v >= bias_region:
        v = int.from_bytes(xof.read(MAX_MOD_NBYTES))
    return v % mod

def xof_randrange(xof, min_include, max_exclude):
    diff = max_exclude - min_include
    return min_include + xof_random_int_mod(xof, diff)