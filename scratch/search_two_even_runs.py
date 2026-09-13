"""Exhaustive search of gap-<=2 representations of 1 with EXACTLY TWO runs of even
denominators.  Such a configuration has at most five maximal step-2 runs (parity
alternates), so it is determined by the start n_0 and the run lengths L_1..L_s."""
import sys
from math import gcd

def factorint(m):
    f = {}
    d = 2
    while d * d <= m:
        while m % d == 0:
            f[d] = f.get(d, 0) + 1
            m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f

def search(a, cap, verbose=False):
    # suffix harmonic bounds: H[v] = sum_{m=v}^{cap} 1/m  (upper bound on what is reachable)
    H = [0.0] * (cap + 3)
    for v in range(cap, a - 1, -1):
        H[v] = H[v + 1] + 1.0 / v
    # allowed number of runs so that exactly two runs are even
    ss = [3, 4] if a % 2 == 0 else [4, 5]
    found = []

    def padic_ok(num, den, v):
        """necessary: every prime power exactly dividing den has a multiple in [v, cap]"""
        for p, e in factorint(den).items():
            q = p ** e
            if q > cap:
                return False
            if (cap // q) < ((v + q - 1) // q):
                return False
        return True

    def run(j, s, v, num, den, acc):
        """start run j (1-based) at v; remaining value num/den"""
        if v > cap:
            return
        # take L >= 1 elements v, v+2, ...
        x = v
        n, d = num, den
        L = 0
        while x <= cap:
            n, d = n * x - d, d * x
            g = gcd(n, d)
            n //= g; d //= g
            L += 1
            if n < 0:
                return
            acc2 = acc + [x]
            if n == 0:
                if j == s:
                    found.append(list(acc2))
                    return
                return  # sum already 1 but runs remain -> not this configuration
            if j == s:
                # last run: must finish exactly, keep extending
                if n / d > H[x + 2] + 1e-12:
                    return
                x += 2
                continue
            nxt = x + 1        # next run starts one above the last element taken
            if nxt <= cap and n / d <= H[nxt] + 1e-12 and padic_ok(n, d, nxt):
                run(j + 1, s, nxt, n, d, acc2)
            if n / d > H[x + 2] + 1e-12:
                return
            x += 2

    for s in ss:
        run(1, s, a, 1, 1, [])
    return found

lo, hi = int(sys.argv[1]), int(sys.argv[2])
for a in range(lo, hi + 1):
    cap = 8 * a + 12
    # justify the cap: the sparsest gap-<=2 set spanning [a,cap] already sums past 1
    m = 0.0
    x = a
    while x <= cap:
        m += 1.0 / x
        x += 2
    while m <= 1.0:
        cap += 2
        m = 0.0
        x = a
        while x <= cap:
            m += 1.0 / x
            x += 2
    res = search(a, cap)
    print(f"n0={a:5d} cap={cap:6d} minspan_sum={m:.4f} -> {'NONE' if not res else res}", flush=True)
