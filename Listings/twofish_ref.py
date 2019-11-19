import sys
# GF modulus polynomial for MDS matrix
GF_MOD = 2**8 + 2**6 + 2**5 + 2**3 + 1

# GF modulus polynomial for RS code
RS_MOD = 2**8 + 2**6 + 2**3 + 2**2 + 1

ROUNDS=16

import struct
import string

def to32Char(X):
    return list(struct.unpack('>BBBB', struct.pack('>I', X)))

def bytesTo32Bits(l):
    t = 0L
    for i in l:
        t = t << 8
        t = t + i
    return t

def ROR(x, n):
    #assumes 32 bit words
    mask = (2L**n) - 1
    mask_bits = x & mask
    return (x >> n) | (mask_bits << (32 - n))

def ROL(x, n):
    return ROR(x, 32 - n)

def ROR4(x, n): #rotate 4 bit value
    mask = (2**n) - 1
    mask_bits = x & mask
    return (x >> n) | (mask_bits << (4 - n))

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

def matrixMultiply(md, sd, modulus):
    #uses GF(2**8)
    #can cheese since second arg is 1 dimensional
    r = []
    i = 0
    for j in range(len(md)):
        t = 0L
        for k in range(len(sd)):
            t = t ^ gfMult(md[j][k], sd[k], modulus)
        r.insert(0, t)
    return r

MDS = [
    [ 0x01, 0xEF, 0x5B, 0x5B ],
    [ 0x5B, 0xEF, 0xEF, 0x01 ],
    [ 0xEF, 0x5B, 0x01, 0xEF ],
    [ 0xEF, 0x01, 0xEF, 0x5B ],
    ]

RS = [
    [ 0x01, 0xA4, 0x55, 0x87, 0x5A, 0x58, 0xDB, 0x9E ],
    [ 0xA4, 0x56, 0x82, 0xF3, 0x1E, 0xC6, 0x68, 0xE5 ],
    [ 0x02, 0xA1, 0xFC, 0xC1, 0x47, 0xAE, 0x3D, 0x19 ],
    [ 0xA4, 0x55, 0x87, 0x5A, 0x58, 0xDB, 0x9E, 0x03 ],
    ]

Q0 = [
    [ 0x8,0x1,0x7,0xD, 0x6,0xF,0x3,0x2, 0x0,0xB,0x5,0x9, 0xE,0xC,0xA,0x4 ],
    [ 0xE,0xC,0xB,0x8, 0x1,0x2,0x3,0x5, 0xF,0x4,0xA,0x6, 0x7,0x0,0x9,0xD ],
    [ 0xB,0xA,0x5,0xE, 0x6,0xD,0x9,0x0, 0xC,0x8,0xF,0x3, 0x2,0x4,0x7,0x1 ],
    [ 0xD,0x7,0xF,0x4, 0x1,0x2,0x6,0xE, 0x9,0xB,0x3,0x0, 0x8,0x5,0xC,0xA ],
    ]

Q1 = [
    [ 0x2,0x8,0xB,0xD, 0xF,0x7,0x6,0xE, 0x3,0x1,0x9,0x4, 0x0,0xA,0xC,0x5 ],
    [ 0x1,0xE,0x2,0xB, 0x4,0xC,0x3,0x7, 0x6,0xD,0xA,0x5, 0xF,0x9,0x0,0x8 ],
    [ 0x4,0xC,0x7,0x5, 0x1,0x6,0x9,0xA, 0x0,0xE,0xD,0x8, 0x2,0xB,0x3,0xF ],
    [ 0xB,0x9,0x5,0x1, 0xC,0x3,0xD,0xE, 0x6,0x4,0x7,0xF, 0x2,0x0,0x8,0xA ],
    ]

def fillWithMyValues():
      K = [1388662238,  300966400 ,
           2091687242,  1293634048,
           3082304016,  511511040 ,
           4003214367,  3487648256,
           4186963705,  2623224832,
           363102992 ,  875187200 ,
           1112377854,  3242664960,
           823886668 ,  4259869184,
           855799695 ,  650995200 ,
           2053923682,  3267032576,
           873576852 ,  3648178176,
           2225975786,  2816402432,
           1423087119,  2734148096,
           2797141900,  2148844544,
           1786023196,  3988452864,
           2458843020,  54062592  ,
           2571753150,  3358670848,
           130055528 ,  3970858496,
           535238724 ,  2243976192,
           4070060318,  1768859136]
      return K

def printRoundKeys(K):
    for i in range(0, len(K), 2):
        print '%8s %8s' % (K[i], K[i+1])

def keySched(M, N): #M is key text in 32 bit words, N is bit width of M
    k = (N+63)/64

    Me = map(lambda x, M=M: M[x], range(0, (2*k-1), 2))
    Mo = map(lambda x, M=M: M[x], range(1, (2*k), 2))

    S = []
    for i in range(0, k):
        x1 = to32Char(Me[i])#; x1.reverse()
        x2 = to32Char(Mo[i])#; x2.reverse()
        vector = x1 + x2
        prod = matrixMultiply(RS, vector, RS_MOD)
        prod.reverse()
        S.insert(0, bytesTo32Bits(prod))
    ## Use my K from my solution to check if encrypt works
    K = fillWithMyValues()
    return K, k, S

def makeKey(Me, Mo, k):
    K = []
    rho = 0x01010101L
    for i in range(ROUNDS + 4):
        A = h(2*i*rho, Me, k)
        B = h((2*i+1)*rho, Mo, k)

        B = ROL(B, 8)
        K.append( (A+B) & 0xFFFFFFFFL )
        K.append(ROL((A + 2*B) & 0xFFFFFFFFL, 9))
    return K

def Qpermute(x, Q):
    x=int(x)
    a0, b0 = x/16, x % 16
    a1 = a0 ^ b0
    b1 = (   a0 ^ ROR4(b0, 1) ^ (8*a0)  ) % 16
    a2, b2 = Q[0][a1], Q[1][b1]
    a3 = a2 ^ b2
    b3 = (   a2 ^ ROR4(b2, 1) ^ (8*a2)  ) % 16
    a4, b4 = Q[2][a3], Q[3][b3]
    return (16 * b4) + a4


def h(X, L, k):
    #X is 32 bit word
    #L is list (L[0] - L[K-1]) of 32 bit words  (Sbox keys)
    x = []
    l = []

    x = to32Char(X)
    x.reverse()
    l = map(to32Char, L)
    y = x[:]

    Qdones = [
        [Q1, Q0, Q1, Q0],
        [Q0, Q0, Q1, Q1],
        [Q0, Q1, Q0, Q1],
        [Q1, Q1, Q0, Q0],
        [Q1, Q0, Q0, Q1],
    ]
    for i in range(k-1, -1, -1):
        for j in range(4):
            y[j] = Qpermute(y[j], Qdones[i+1][j]) ^ l[i][j]

    for j in range(4):
        y[j] = Qpermute(y[j], Qdones[0][j])

    z = matrixMultiply(MDS, y, GF_MOD)
    return bytesTo32Bits(z)

def g(X, S, k):
    return h(X, S, k)

def F(R0, R1, r, K, k, S):
    T0 = g(R0, S, k)
    T1 = g(ROL(R1, 8), S, k)
    F0 = (T0 + T1 + K[2*r+8]) & 0xFFFFFFFFL
    F1 = (T0 + 2*T1 + K[2*r+9]) & 0xFFFFFFFFL
    return F0, F1

def encrypt(K, k, S, PT): #pt is array of 4 32bit L's
    R = map(lambda i, PT=PT, K=K: PT[i] ^ K[i], range(4))

    for r in range(ROUNDS):
        NR = [0,0,0,0]
        FR0, FR1 = F(R[0], R[1], r, K, k, S)
        NR[2] = ROR(R[2] ^ FR0, 1)
        NR[3] = ROL(R[3], 1) ^ FR1
        NR[0] = R[0]
        NR[1] = R[1]
        R = NR
        if (r < ROUNDS - 1): #/* swap for next round */
            R[0], R[2] = R[2], R[0]
            R[1], R[3] = R[3], R[1]

    R = [R[2], R[3], R[0], R[1]]
    R = map(lambda i, R=R, K=K: R[(i+2) % 4] ^ K[i+4], range(4))
    return R

def decrypt(K, k, S, PT): #pt is array of 4 32bit L's
    R = map(lambda i, PT=PT, K=K: PT[i] ^ K[i+4], range(4))

    for r in range(ROUNDS-1, -1, -1):
        NR = [0,0,0,0]
        FR0, FR1 = F(R[0], R[1], r, K, k, S)
        NR[2] = ROL(R[2], 1) ^ FR0
        NR[3] = ROR(R[3] ^ FR1, 1)
        NR[0] = R[0]
        NR[1] = R[1]
        R = NR
        if (r > 0): #/* swap for next round */
            R[0], R[2] = R[2], R[0]
            R[1], R[3] = R[3], R[1]

    R = [R[2], R[3], R[0], R[1]]
    R = map(lambda i, R=R, K=K: R[(i+2) % 4] ^ K[i], range(4))
    return R

def dispLongList(v):
    return string.join(map(lambda x:string.zfill(hex(x)[2:-1], 8), v), '')

if __name__ == '__main__':
    K, k, S = keySched([0xefcdab89l, 0x67452301l,
                        0x10325476l, 0x98badcfel], 128)
    PT= [0xDEADBEAFL, 0xCAFEBABEL, 0x86753090L, 0x04554013L]
    print "Original: ", PT
    CT = encrypt(K, k, S, PT)
    print "Encrypted:", CT
    PT = decrypt(K, k, S, CT)
    print "Decrypted:", PT
