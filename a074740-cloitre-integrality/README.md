# Cloitre's integrality observation for OEIS A074740

**Status:** disproved, with a complete classification of the integer values. The counterexample n = 1834 (and integrality at n = 1833) is checked in Lean 4; the full classification is not formalized (◐). No earlier disproof was found in a search on November 19, 2026, which does not guarantee that none exists.

## Statement

[OEIS A074740](https://oeis.org/A074740) (Benoit Cloitre, September 5, 2002) is the sequence

a(n) = n!·2^(n−1) / ∏_{k=1..n} τ(k),

where τ(k) is the number of divisors of k. Its first terms are 1, 2, 6, 16, 80, 240. The entry's only comment is "Appears to be an integer for n >= 1." This is an observation, not a formally stated conjecture.

**Theorem.** a(n) is an integer if and only if n ≤ 1833 or n ∈ {1856, 1864, 1868, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880}. Only the prime 2 ever appears in the reduced denominator.

**Corollary.** The observation is false. The first failure is n = 1834 = 2·7·131: v₂(1834!·2^1833) = 3661 but v₂(∏_{k≤1834} τ(k)) = 3662, so a(1834) has reduced denominator 2.

**Proof in brief.** v₂ of the numerator is 2n − 1 − s₂(n) < 2n. Every prime p dividing k exactly once contributes a factor 2 to τ(k), so v₂ of the denominator is greater than n·S_M − π(M) with S_M = Σ_{p≤M} (1/p − 1/p²). For M = 30000 a certified computation gives S_M > 2.14266 and π(M) = 3245, so the denominator has more factors of 2 than the numerator for every n ≥ 22747. The range n ≤ 2,000,000 is checked exactly by `verify.py`.

## Files

| File | What it is |
|---|---|
| [A074740.pdf](A074740.pdf) | The written proof (4 pages). |
| [verify.py](verify.py) | The verification program (Python 3, standard library only; about 7 seconds). It checks the integrality criterion at every prime for all n ≤ 2,000,000, compares the first 24 terms with the OEIS data, and certifies the constant used in the analytic tail. |
| [A074740.lean](A074740.lean) | Lean 4 / Mathlib check of the counterexample: `a074740_not_integer` (a(1834) is not an integer) and `a074740_integer_1833` (a(1833) is an integer). |

## Lean verification

- **Formal statements:** written by us, not taken from Formal Conjectures:
  `theorem a074740_not_integer : ¬ ((∏ k ∈ Finset.Icc 1 1834, (Nat.divisors k).card) ∣ Nat.factorial 1834 * 2 ^ 1833)`
  and the corresponding divisibility for n = 1833.
- **Scope:** only these two numerical facts. The analytic tail and the computation up to 2,000,000 are not formalized.
- **Method:** for 0 < k ≤ 1849 the divisor count is rewritten, by the pairing d ↔ k/d, as a scan over d ≤ 43; the product is evaluated by the Lean kernel with `decide +kernel` in eleven chunks with numeric certificates. `native_decide` is not used.
- **Lean version:** v4.27.0, with the Mathlib from Formal Conjectures used for the other entries in this repository (commit `67338a1`). The file imports only `Mathlib.NumberTheory.Divisors` and `Mathlib.Algebra.BigOperators.Intervals`.
- **Result:** compiles with no errors and no `sorry` (about 40 seconds). Both theorems depend only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
- **Last checked:** November 19, 2026.

To repeat the check, inside a Formal Conjectures checkout (see the root README):

```
lake env lean /path/to/A074740.lean
```

It passes if the command prints no `error` lines.

## Relation to earlier work

- **Priority.** A search on November 19, 2026 (the OEIS entry, both in a mirror dated that day and on oeis.org; web searches for "A074740" and for the statement; GitHub code search) found no earlier disproof or classification. The only hits besides the entry itself were programs that compute the sequence. This does not guarantee that none exists.
- **Prime estimates.** The proof needs only a finite computation. The note also records an alternative tail argument through the explicit estimates of Rosser and Schoenfeld (1962), as quoted by C. Axler (arXiv:1703.08032) and S. Zhang (arXiv:0908.2943); the original paper was not consulted directly.

## History

- November 19, 2026: classification proved, counterexample checked in Lean, and added to this repository.
