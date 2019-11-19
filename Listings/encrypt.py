def encrypt(K, S, PT): #pt is array of 4 32bit L's
    R = map(lambda i, PT=PT, K=K: PT[i] ^ K[i], range(4))

    for r in range(ROUNDS):
        NR = [0,0,0,0]
        FR0, FR1 = F(R[0], R[1], r, K, S)
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

def decrypt(K, S, CT): #ct is array of 4 32bit L's
    R = map(lambda i, CT=CT, K=K: CT[i] ^ K[i+4], range(4))

    for r in range(ROUNDS-1, -1, -1):
        NR = [0,0,0,0]
        FR0, FR1 = F(R[0], R[1], r, K, S)
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
