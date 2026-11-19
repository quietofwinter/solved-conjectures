# Bala's supercongruence for OEIS A364175

**Status:** proved, and checked in Lean 4 (☑).

## Statement

[OEIS A364175](https://oeis.org/A364175) is the sequence

a(n) = (6n)!·(2n/3)! / ((3n)!·(2n)!·(5n/3)!),

where x! means Γ(x+1).

**Theorem.** For every prime p ≥ 5 and all positive integers n and r,

a(n·p^r) ≡ a(n·p^(r−1)) (mod p^(3r)).

This was conjectured by Peter Bala in the comments of the OEIS entry.

## Files

| File | What it is |
|---|---|
| [A364175.pdf](A364175.pdf) | The written proof (3 pages). |
| [A364175.lean](A364175.lean) | The Lean 4 / Mathlib proof. The main theorem is `oeis_364175_conjecture_0`, the last theorem in the file. |

## Lean verification

- **Formal statement:** `oeis_364175_conjecture_0`, copied unchanged from `FormalConjectures/OEIS/Auto/364175_1518df7a.lean` in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) at commit `67338a1` (branch `auto_oeis`). The same statement is used in Epoch AI's OEIS Open benchmark.
- **Lean version:** v4.27.0.
- **Result:** compiles with no errors and no `sorry`. It depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
- **Last checked:** November 19, 2026.

To repeat the check:

```
git clone https://github.com/google-deepmind/formal-conjectures
cd formal-conjectures
git checkout 67338a1
lake exe cache get
lake env lean /path/to/A364175.lean
```

It passes if the last command prints no `error` lines. It prints several warnings (deprecated lemma names and unused variables), which are harmless.

## Earlier work this builds on

- **Integrality.** David G. Radcliffe proved that a(n) is always an integer: [Integrality of a Ratio of Fractional Factorials](https://oeis.org/A364175/a364175.pdf), July 19, 2026. The Lean file also proves this independently (lemma `integrality`).
- **Benchmark submissions reused in the Lean file.** Both are by Claude Opus 4.8 in the run `oeis-full-50usd-ant-j0j0g4uzligm1k41` of Epoch AI's [OEIS Open results](https://github.com/epoch-research/LeanOpenProblems-results), described in T. Adamczewski, *OEIS Open: How many conjectures can language models turn into theorems?*, [arXiv:2608.11941](https://arxiv.org/abs/2608.11941).
  - The integrality argument and the gamma-function reduction come from that run's attempt at this same conjecture, which the benchmark rejected because it still contained `sorry`.
  - The block-product lemmas come from that run's accepted proof for the sibling sequence A364176.
- **New here.** The step-3 block congruence, the splitting of the product Q(Mp), and the final assembly. In the Lean file these are `block_cong3`, `BG3`, `bg3_succ`, `BG3_cong`, `QG`, `Q_split`, `qg_coprime`, `Qseq_ne'`, `core175` and the final theorem.

## Prior attempts

In the public OEIS Open results as of November 5, 2026, four benchmark runs attempted this conjecture (Claude Opus 4.8, GPT-5.5, Gemini 3.5 Flash and Gemini 3.1 Pro). None was accepted.

## History

- November 18, 2026: proof completed and submitted to the OEIS entry.
- November 19, 2026: references and file names revised for this repository; the proof is unchanged.
