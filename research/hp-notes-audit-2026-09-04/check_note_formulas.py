"""Exact finite checks of the formulas printed in the defect-probe notes.

The basis in section 16 is treated as orthonormal, as in its definition of
the truncated adjoints. No floating point eigenvalues are used.
"""
import json
from pathlib import Path


def capacity(alpha):
    p, q, r = alpha
    return 2 * (p*q + p*r + q*r)


def creator(vector, i):
    if vector is None:
        return None
    alpha, k = vector
    beta = list(alpha)
    beta[i] += 1
    return tuple(beta), k


def annihilator(vector, i):
    if vector is None:
        return None
    alpha, k = vector
    if alpha[i] == 0:
        return None
    beta = list(alpha)
    beta[i] -= 1
    return (tuple(beta), k) if k <= capacity(beta) else None


def defect_rank(n):
    images = []
    for p in range(n+1):
        for q in range(n-p+1):
            alpha = (p, q, n-p-q)
            for k in range(capacity(alpha)+1):
                vector = alpha, k
                left = annihilator(creator(vector, 1), 0)
                right = creator(annihilator(vector, 0), 1)
                if left != right:
                    assert left is not None and right is None
                    images.append(left)
    # Every nonzero column has one nonzero entry in a different row.
    assert len(images) == len(set(images))
    return len(images)


result = {
    "arithmetic": "integer basis action, no numerical rank tolerance",
    "defect": "C_0^* C_1 - C_1 C_0^* (color names immaterial by symmetry)",
    "ranks": [{"n": n, "computed": defect_rank(n),
               "printed": 2*(n-1)*n*(n+1)//3} for n in range(1, 9)],
    "camera_generator": {
        "measure": "dSigma_bc = M0_bc 1_(0,ell_bc] dx; y=1+log(x)",
        "derived": "G_bc exp(s*(1+log(ell_bc)))/(1+s)",
        "domain": "Re(s)>-1; ell_bc>0; G_bc=M0_bc*ell_bc",
        "at_s_zero": "derived=G_bc; printed=M0_bc",
        "method": "integrate exp(s)*x^s exactly; algebraic derivation, not Lean"
    }
}
if __name__ == "__main__":
    output = Path(__file__).with_name("note-formula-checks.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
