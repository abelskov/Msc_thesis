def polyMult(a, b):
    t = 0
    while a:
        if a & 1:
            t = t ^ b
        b = b << 1
        a = a >> 1
    return t

def gfMod(t, modulus):
    modulus = modulus << 7
    for i in range(8):
        tt = t ^ modulus
        if tt < t:
            t = tt
        modulus = modulus >> 1
    return t

def gfMult(a, b, modulus):
    return gfMod(polyMult(a, b), modulus)
