#!/usr/bin/env python3
"""Independent check of the integrality of OEIS A074740,
       a(n) = n! * 2^(n-1) / prod_{k=1..n} tau(k),   tau = number of divisors.

Method (standard library only):
  * a sieve of smallest prime factors gives the factorization k = prod p^e of
    every k <= N, hence tau(k) = prod (e+1) and, for every prime q,
    v_q(tau(k)) = sum over p^e || k of v_q(e+1);
  * v_2 of the numerator is computed in closed form, v_2(n! 2^(n-1)) = 2n-1-s_2(n)
    (Legendre), and for odd primes q the numerator valuation v_q(n!) is
    accumulated from the factorizations;
  * a(n) is an integer iff v_q(numerator) >= v_q(denominator) for every prime q
    dividing some tau(k), k <= n (other primes do not divide the denominator).
  * the first 24 values are recomputed with exact integers and compared with
    the OEIS data line, and n = 1833, 1834 are recomputed with exact integers.
Usage: python3 verify.py [N]   (default N = 2000000)
"""
import sys, time
from fractions import Fraction
from math import factorial

t0 = time.time()
N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000

# smallest-prime-factor sieve
spf = list(range(N + 1))
i = 2
while i * i <= N:
    if spf[i] == i:
        for m in range(i * i, N + 1, i):
            if spf[m] == m:
                spf[m] = i
    i += 1

def vq(q, x):
    c = 0
    while x % q == 0:
        x //= q; c += 1
    return c

den = {}      # q -> v_q(prod tau(k)), k <= n
numodd = {}   # odd q -> v_q(n!)   (only tracked for q that ever divide a tau)
taus = [0]
integer_after_first_fail = []
first_fail = None
last_integer = 0
obstructing = set()
details = {}
for n in range(1, N + 1):
    # factorize n
    x = n; tau = 1; fac = []
    while x > 1:
        p = spf[x]; e = 0
        while x % p == 0:
            x //= p; e += 1
        fac.append((p, e)); tau *= e + 1
        # contribution of p^e to v_q(tau(n)) for each prime q | e+1
        y = e + 1
        while y > 1:
            q = spf[y]
            while y % q == 0:
                y //= q
                den[q] = den.get(q, 0) + 1
                if q != 2 and q not in numodd:
                    # start tracking: v_q((n-1)!) by Legendre; n's own factor is added below
                    s, qq = 0, q
                    while qq <= n - 1:
                        s += (n - 1) // qq; qq *= q
                    numodd[q] = s
    for p, e in fac:
        if p in numodd:
            numodd[p] += e
    if n <= 24:
        taus.append(tau)
    # check
    bad = []
    v2num = 2 * n - 1 - bin(n).count("1")
    if v2num < den.get(2, 0):
        bad.append(2)
    for q, d in den.items():
        if q != 2 and numodd[q] < d:
            bad.append(q)
    if n in (1833, 1834):
        details[n] = (v2num, den.get(2, 0), dict(numodd), {q: d for q, d in den.items()}, tau, fac)
    if bad:
        obstructing.update(bad)
        if first_fail is None:
            first_fail = n
    else:
        last_integer = n
        if first_fail is not None:
            integer_after_first_fail.append(n)

# sanity: v_q(n!) tracking against Legendre at the end
for q, s in numodd.items():
    leg, qq = 0, q
    while qq <= N:
        leg += N // qq; qq *= q
    assert s == leg, (q, s, leg)

# OEIS data check (first 24 terms), exact rational arithmetic
oeis = [1,2,6,16,80,240,1680,6720,40320,201600,2217600,8870400,115315200,
        807206400,6054048000,38745907200,658680422400,3952082534400,
        75089568153600,500597121024000,5256269770752000,57818967478272000,
        1329836252000256000,7979017512001536000]
prod = 1; ok = True
for n in range(1, 25):
    prod *= taus[n]
    a = Fraction(factorial(n) * 2 ** (n - 1), prod)
    ok &= (a.denominator == 1 and a.numerator == oeis[n - 1])
print("N =", N)
print("first 24 terms match OEIS data line:", ok)
print("first non-integer n:", first_fail)
print("integer n after the first failure:", integer_after_first_fail)
print("number of integer n <= N:", first_fail - 1 + len(integer_after_first_fail))
print("last integer n:", last_integer)
print("primes that ever obstruct:", sorted(obstructing))
print("primes dividing some tau(k), k <= N, with v_q(prod tau):", dict(sorted(den.items())))
for n in (1833, 1834):
    v2n, v2d, no, dd, tau, fac = details[n]
    print("n = %d = %s, tau(n) = %d: v_2(num) = %d, v_2(den) = %d; odd q: %s" % (
        n, "*".join("%d^%d" % f if f[1] > 1 else str(f[0]) for f in fac), tau, v2n, v2d,
        {q: (no[q], dd[q]) for q in sorted(no)}))
# exact-integer recomputation at n = 1833, 1834
P = 1
for k in range(1, 1835):
    t = sum(1 for d in range(1, int(k**0.5) + 1) if k % d == 0) * 2 - (1 if int(k**0.5)**2 == k else 0)
    P *= t
    if k in (1833, 1834):
        a = Fraction(factorial(k) * 2 ** (k - 1), P)
        print("exact: a(%d) has reduced denominator %d" % (k, a.denominator))

# Analytic tail (Lemma in the note): for every n,
#   v_2(prod_{k<=n} tau(k)) >= sum_{p<=M} (floor(n/p) - floor(n/p^2)) > n*S_M - pi(M),
#   S_M = sum_{p<=M} (1/p - 1/p^2).
# With M = 30000 we certify S_M > 2 using integer arithmetic rounded downwards,
# and compute the smallest n0 with n*(S_M - 2) >= pi(M); then v_2(den) > 2n > v_2(num) for n >= n0.
M = 30000
ps = [p for p in range(2, M + 1) if spf[p] == p] if M <= N else None
SC = 10 ** 40
low = sum(SC // p - (-(-SC // (p * p))) for p in ps)   # low <= SC * S_M
assert low > 2 * SC
n0 = -(-len(ps) * SC // (low - 2 * SC))
print("tail: M = %d, pi(M) = %d, S_M >= %.12f, tail valid for n >= n0 = %d; n0 <= N: %s"
      % (M, len(ps), low / SC, n0, n0 <= N))
print("runtime %.1f s" % (time.time() - t0))
