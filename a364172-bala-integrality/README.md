# Integrality and Bala's supercongruence for OEIS A364172

**Status:** proved, and checked in Lean 4 (☑). Integrality: no earlier proof was found in a search on November 19, 2026, which does not guarantee that none exists. Supercongruence: it also follows from integrality by a theorem of Bajaj and Burns (see "Relation to earlier work" below).

## Statement

[OEIS A364172](https://oeis.org/A364172) is the sequence

a(n) = (6n)!·(n/3)! / ((3n)!·(2n)!·(4n/3)!),

where x! means Γ(x+1). Its first terms are 1, 45, 6237, 1021020.

**Theorem 1 (integrality).** a(n) is a positive integer for every n ≥ 0.

**Theorem 2 (supercongruence).** For every prime p ≥ 5 and all positive integers n and r,

a(n·p^r) ≡ a(n·p^(r−1)) (mod p^(3r)).

The OEIS entry, by Peter Bala, says that the sequence is only conjecturally an integer sequence, and conjectures Theorem 2.

## Files

| File | What it is |
|---|---|
| [A364172.pdf](A364172.pdf) | The written proof (4 pages). |
| [A364172.lean](A364172.lean) | The Lean 4 / Mathlib proof of both theorems. The main theorem is `oeis_364172_conjecture_0`, the last theorem in the file; integrality is proved by the lemmas `integrality` and `val_eq`. |

## Lean verification

- **Formal statement:** `oeis_364172_conjecture_0`. Formal Conjectures has no statement for A364172; this one was written by us, modelled word for word on the statement for A364175 in `FormalConjectures/OEIS/Auto/364175_1518df7a.lean` in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) at commit `67338a1` (branch `auto_oeis`). Only the sequence number and the gamma arguments (1/3 and 4/3 in place of 2/3 and 5/3) differ.
- **Lean version:** v4.27.0, against Formal Conjectures at commit `67338a1`.
- **Result:** compiles with no errors and no `sorry`. It depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
- **Last checked:** November 19, 2026.

To repeat the check:

```
git clone https://github.com/google-deepmind/formal-conjectures
cd formal-conjectures
git checkout 67338a1
lake exe cache get
lake env lean /path/to/A364172.lean
```

It passes if the last command prints no `error` lines.

## Relation to earlier work

- **Supercongruence.** R. A. Bajaj and A. Burns, in the note *Rational gamma ratios inherit a cubic tower* (August 2026) in [rbajaj5/a183068-supercongruence](https://github.com/rbajaj5/a183068-supercongruence), prove that for A364172–A364184 the p^(3r) congruence holds once the values are known to be integral, and list the integrality of the remaining records, A364172 among them, as unresolved. So Theorem 2 follows from Theorem 1 by their theorem; the note here gives a direct, self-contained proof of both.
- **Twin sequence.** David G. Radcliffe proved integrality of A364175: [Integrality of a Ratio of Fractional Factorials](https://oeis.org/A364175/a364175.pdf), July 19, 2026.
- **Priority.** A search on November 19, 2026 (the OEIS entry, GitHub, the Bajaj–Burns repository) found no earlier proof of the integrality of A364172. This does not guarantee that none exists.

## Earlier work this builds on

- **The A364175 proof in this repository.** The Lean file is adapted from [`a364175-bala-supercongruence/A364175.lean`](../a364175-bala-supercongruence/A364175.lean), with the product n + 3k in place of 2n + 3k.
- **Benchmark submissions reused through that file.** Both are by Claude Opus 4.8 in the run `oeis-full-50usd-ant-j0j0g4uzligm1k41` of Epoch AI's [OEIS Open results](https://github.com/epoch-research/LeanOpenProblems-results), described in T. Adamczewski, *OEIS Open: How many conjectures can language models turn into theorems?*, [arXiv:2608.11941](https://arxiv.org/abs/2608.11941).
  - The integrality argument and the gamma-function reduction come from that run's attempt at the A364175 conjecture, which the benchmark rejected because it still contained `sorry`.
  - The block-product lemmas come from that run's accepted proof for the sibling sequence A364176.
- **New here.** The adaptation to n + 3k and 4n/3 (including the 3-adic case n = 3m′, which reduces to Vasyunin's ratio (18m′)!·m′!/((9m′)!·(6m′)!·(4m′)!)), the floor lemmas `fl_scale`, `fl_lt`, `fl_E`, `core172` and the final theorem. The Lean header lists the adapted lemmas.

## History

- November 19, 2026: proof completed, checked in Lean, and added to this repository.
