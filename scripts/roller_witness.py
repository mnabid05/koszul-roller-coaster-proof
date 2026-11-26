"""Construct a compressed Koszul Roller Coaster witness using integer arithmetic.

Usage: python3 roller_witness.py 8 3 1 4 2
Each block is a count of complete multipartite graphs with equal parts.
"""
import argparse
from fractions import Fraction
from itertools import permutations
from math import comb, lcm


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def hilbert_from_blocks(d, blocks):
    """Count old faces, their colored extensions, and the dual facet terms."""
    p = d - 1
    old = [int(k == 0) for k in range(d)]
    for parts, size, count in blocks:
        for k in range(1, parts + 1):
            old[k] += count * comb(parts, k) * size**k
    faces = [
        sum(old[s] * choose(p - s, k - s) for s in range(min(p, k) + 1))
        for k in range(d + 1)
    ]
    return [faces[k] + faces[d - k] for k in range(d + 1)]


def build(d, order):
    p, m = d - 1, d // 2
    if d < 3 or sorted(order) != list(range(1, m + 1)):
        raise ValueError("supply a degree at least 3 and a permutation of its first half")
    # Invert the upper triangular matrix of the first m columns.
    perturb = [Fraction(0)] * p
    for k in range(m, 0, -1):
        def entry(i):
            return choose(i, k - 1) + choose(i, p - k)
        tail = sum(perturb[i] * entry(i) for i in range(k, m))
        perturb[k - 1] = (Fraction(order.index(k)) - tail) / entry(k - 1)
    baseline = 1 + max(int(abs(c)) for c in perturb)
    q = [Fraction(0)] + [baseline * 2**(s - 1) + perturb[p - s] for s in range(1, p + 1)]
    assert all(x > 0 for x in q[1:])

    # Invert the coefficient transform of (1+N*x)^j. The leading term
    # in N^j*b_j is q_j>0, so doubling N eventually makes every b_j positive.
    size = 1
    while True:
        b = [Fraction(0)] + [
            sum((-1)**(s-j) * comb(s, j) * q[s] / size**s for s in range(j, p + 1))
            for j in range(1, p + 1)
        ]
        if min(b[1:]) > 0:
            break
        size *= 2
    denominator = lcm(*(v.denominator for v in b[1:]))
    scale = denominator * (1 + comb(d, m) // denominator)
    blocks = [(j, size, int(scale * b[j])) for j in range(1, p+1)]
    h = hilbert_from_blocks(d, blocks)
    for k in range(1, m + 1):
        assert h[k] == comb(d, k) + scale * (baseline * 2**p + order.index(k))
    assert all(h[i] < h[j] for i, j in zip(order, order[1:]))
    assert h == h[::-1] and h[0] == h[-1] == 1
    return blocks, h


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree", type=int, nargs="?")
    parser.add_argument("order", type=int, nargs="*")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        count = 0
        for d in range(3, 13):
            for order in permutations(range(1, d // 2 + 1)):
                build(d, order)
                count += 1
        print(f"Checked all {count} orderings in degrees 3 through 12.")
    if args.degree is not None:
        blocks, h = build(args.degree, args.order)
        print("parts, size of each part, copies")
        for block in blocks:
            print(*block)
        print("Hilbert function:", *h)
    elif not args.self_test:
        parser.error("supply a degree and order, or --self-test")


if __name__ == "__main__":
    main()
