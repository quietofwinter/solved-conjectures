# Integrality and Bala's supercongruence for OEIS A364178

**Status:** proved, and checked in Lean 4 (☑). This is the first Lean-verified proof as far as a search on November 19, 2026 found. It is not the first proof: see "Earlier proof" below.

## Statement

[OEIS A364178](https://oeis.org/A364178) is the sequence

a(n) = (10n)!·(3n)!·(n/2)! / ((6n)!·(5n)!·(3n/2)!·n!),

where x! means Γ(x+1). Its first terms are 1, 168, 83980, 48664320.

**Theorem 1 (integrality).** a(n) is a positive integer for every n ≥ 0.

**Theorem 2 (supercongruence).** For every prime p ≥ 5 and all positive integers n and r,

a(n·p^r) ≡ a(n·p^(r−1)) (mod p^(3r)).

The OEIS entry, by Peter Bala, says that the sequence is only conjecturally an integer sequence, and conjectures Theorem 2. It also notes that the sequence is essentially A295470(n/2), where A295470 is one of Vasyunin's 52 sporadic integral factorial ratios.

## Files

| File | What it is |
|---|---|
| [A364178.pdf](A364178.pdf) | The written proof (4 pages). |
| [A364178.lean](A364178.lean) | The Lean 4 / Mathlib proof. The main theorem is `oeis_364178_conjecture_0`, the last theorem in the file; integrality is lemma `integrality178`. |

## Lean verification

- **Formal statement:** `oeis_364178_conjecture_0`, copied unchanged from `FormalConjectures/OEIS/Auto/364178_4c681d65.lean` in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) at commit `67338a1` (branch `auto_oeis`). The same statement is used in Epoch AI's OEIS Open benchmark. Because a(n) is defined there through the gamma function, the Lean file also proves Theorem 1.
- **Lean version:** v4.27.0.
- **Result:** compiles with no errors and no `sorry`. It depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
- **Last checked:** November 19, 2026.

To repeat the check:

```
git clone https://github.com/google-deepmind/formal-conjectures
cd formal-conjectures
git checkout 67338a1
lake exe cache get
lake env lean /path/to/A364178.lean
```

It passes if the last command prints no `error` lines.

## Earlier proof

R. A. Bajaj and A. Burns, in the note *A uniform half-index theorem for Bober factorial ratios* (file `related-results/BoberHalfIndexIntegralityTheorem.md` in [rbajaj5/a183068-supercongruence](https://github.com/rbajaj5/a183068-supercongruence), dated August 12, 2026 in the repository history), state integrality and the full p^(3r) congruence for p ≥ 5 for all eleven half-index variants of Bober records in Bala's packet, A295470(N/2) = A364178 among them. For the congruence they use the cubic-transfer theorem of their note *Rational gamma ratios inherit a cubic tower* in the same repository. They label the half-index note a "complete elementary proof candidate; exact checks pass; independent review and literature priority remain open". Their proof is written, not formalized.

The proof in this folder is independent of theirs in method: it follows the published proof for A364176 (see below). What this folder adds is a machine-checked proof.

## Earlier work this builds on

- **Benchmark submissions reused in the Lean file.** Both are by Claude Opus 4.8 in the run `oeis-full-50usd-ant-j0j0g4uzligm1k41` of Epoch AI's [OEIS Open results](https://github.com/epoch-research/LeanOpenProblems-results), described in T. Adamczewski, *OEIS Open: How many conjectures can language models turn into theorems?*, [arXiv:2608.11941](https://arxiv.org/abs/2608.11941).
  - The integrality argument follows the structure of the formal integrality proof in that run's attempt at the A364175 conjecture, which the benchmark rejected because it still contained `sorry`. The gamma-function reduction (`gamma_shift`, `val_eq`, `a_eq`) is adapted from the same attempt.
  - The block-product lemmas, including the step-2 shifted blocks, come from that run's accepted proof for the sibling sequence A364176 (Appendix A of the paper above).
- **The written proof** of the congruence follows the published A364176 proof.

## History

- November 18, 2026: proof completed.
- November 19, 2026: citation of the earlier proof by Bajaj and Burns added; the Lean file was given a descriptive header and recompiled; the proof is unchanged.
