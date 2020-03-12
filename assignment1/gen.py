# generates 100 random small matrices and takes their product

import random
MAX_VAL = 10
MAX_SZ = 6


def get_sizes():
    a = random.randint(1, MAX_SZ)
    b = random.randint(1, MAX_SZ)
    c = random.randint(1, MAX_SZ)
    return a, b, c


def mult_mat(m1, m2, a, b, c):
    res = [[0 for _ in range(c)] for __ in range(a)]
    for i in range(a):
        for j in range(c):
            for k in range(b):
                res[i][j] += m1[i][k] * m2[k][j]
    return res


def get_matrices():
    a, b, c = get_sizes()
    mat1 = [[random.randint(0, MAX_VAL) for _ in range(b)] for __ in range(a)]
    mat2 = [[random.randint(0, MAX_VAL) for _ in range(c)] for __ in range(b)]
    return mat1, mat2, mult_mat(mat1, mat2, a, b, c), a, b, c


def row_str(row):
    return "{" + ",".join(map(str, row)) + "}"


def mat_str(mat):
    return "{" + ",".join(row_str(x) for x in mat) + "}"


def print_assertion():
    m1, m2, res, p, q, r = get_matrices()
    s = f"assert productSK({p}, {q}, {q}, {r}, "
    s += mat_str(m1)
    s += ","
    s += mat_str(m2)
    s += ") == "

    s += mat_str(res)
    s += ";"

    print(s)


random.seed(42)
for i in range(1):
    print_assertion()
