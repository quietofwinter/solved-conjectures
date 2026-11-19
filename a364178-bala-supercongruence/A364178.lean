/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
Integrality and the supercongruence conjecture for OEIS A364178.
Jason Benham, November 18, 2026; revised November 19, 2026.

MAIN RESULTS

  1. Integrality. For every n, the real number

         (10n)! (3n)! Γ(n/2 + 1) / ((6n)! (5n)! Γ(3n/2 + 1) n!)

     equals the natural number `aexact n` (lemma `val_eq`). This rests on
     lemma `integrality178`, which shows that (6n)! (5n)! n! P(n) divides
     2^n (10n)! (3n)!, where P(n) = ∏_{k=1}^n (n + 2k) is `Pseq n`.

  2. Supercongruence. `oeis_364178_conjecture_0`, the last theorem in this
     file: for every prime p >= 5 and all positive integers n and r,

         a(n p^r) ≡ a(n p^(r-1))  (mod p^(3r)),

     where a(n) = (10n)! (3n)! (n/2)! / ((6n)! (5n)! (3n/2)! n!), with
     x! := Γ(x+1), is OEIS A364178. The supercongruence was conjectured by
     Peter Bala in the OEIS entry https://oeis.org/A364178, which also says
     that the sequence is only conjecturally an integer sequence. A written
     proof is in `A364178.pdf`, in the same folder as this file.

WHERE THE FORMAL STATEMENT COMES FROM

  The definition `a` and the statement of `oeis_364178_conjecture_0` are
  copied unchanged from Formal Conjectures
  (https://github.com/google-deepmind/formal-conjectures),

      FormalConjectures/OEIS/Auto/364178_4c681d65.lean

  at commit 67338a1 (branch `auto_oeis`), which carries the Apache 2.0 notice
  above. The same statement is used in Epoch AI's OEIS Open benchmark.

A NOTE ON THE DOCSTRING OF `a`

  The docstring calls the sequence "conjecturally integral", following the
  Formal Conjectures source. This file proves that it is an integer sequence
  (lemmas `integrality178` and `val_eq`).

EARLIER PROOF

  This is not the first proof of these results. R. A. Bajaj and A. Burns,
  in the note "A uniform half-index theorem for Bober factorial ratios"
  (file `related-results/BoberHalfIndexIntegralityTheorem.md` in
  https://github.com/rbajaj5/a183068-supercongruence, August 12, 2026),
  state integrality and the full p^(3r) congruence for p >= 5 for the
  half-index variants of eleven Bober records, A295470(N/2) = A364178 among
  them. They label the note a "complete elementary proof candidate", with
  independent review open. Their proof is written, not formalized. The proof
  in this file uses a different method (see below).

EARLIER WORK REUSED IN THIS FILE

  1. The integrality argument follows the structure of the earlier formal
     integrality proof for A364175 in the submission by Claude Opus 4.8 for
     the A364175 conjecture in Epoch AI's OEIS Open run
     `oeis-full-50usd-ant-j0j0g4uzligm1k41`,
     `oeis_364175_conjecture_0/Submission/Spec.lean`, published at
     https://github.com/epoch-research/LeanOpenProblems-results (see
     T. Adamczewski, "OEIS Open: How many conjectures can language models turn
     into theorems?", arXiv:2608.11941). That submission was rejected by the
     verifier because it still contained `sorry`. The gamma-function
     reduction (`gamma_shift`, `val_eq`, `a_eq`) and `aexact`, `aexact_spec`
     and `prod_Icc_ascFactorial` are adapted from the same submission.

  2. The block-product lemmas (`sum_units_sq_eq_zero` through `gcop_coprime`,
     including the step-2 shifted blocks `block_cong2`, `BG2`, `bg2_succ`,
     `BG2_cong`) come from that run's accepted proof for the sibling sequence
     A364176, `oeis_364176_conjecture_0/Submission/Spec.lean`.

HOW TO CHECK IT

  Lean v4.27.0, against Formal Conjectures at commit 67338a1:

      git clone https://github.com/google-deepmind/formal-conjectures
      cd formal-conjectures
      git checkout 67338a1
      lake exe cache get
      lake env lean /path/to/A364178.lean

  The last command should finish without errors. The proof contains no `sorry`
  and depends only on the standard axioms `propext`, `Classical.choice` and
  `Quot.sound`.

The proof was developed with the assistance of Claude (Anthropic).
-/

import FormalConjectures.Util.ProblemImports

open Real
open Nat

/--
A364178: The conjecturally integral sequence
$$a(n) = \frac{(10n)! (3n)! (n/2)!}{(6n)! (5n)! (3n/2)! n!}$$
where $x! := \Gamma(x+1)$ for real $x$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (round
    ((Gamma (10 * (↑n : ℝ) + 1) * Gamma (3 * (↑n : ℝ) + 1) * Gamma ((↑n : ℝ) / 2 + 1)) /
     (Gamma (6 * (↑n : ℝ) + 1) * Gamma (5 * (↑n : ℝ) + 1) * Gamma (3 * (↑n : ℝ) / 2 + 1) * Gamma (↑n + 1)))
  ).toNat


open Finset

lemma prod_Icc_ascFactorial (a K : ℕ) :
    ∏ k ∈ Finset.Icc 1 K, (a + k) = (a+1).ascFactorial K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ K+1), ih, Nat.ascFactorial_succ]
    ring

/-! ## Integrality of A364178 (new)

With `Pseq n = ∏_{k=1}^n (n + 2k)` we have `Γ(3n/2+1) = Γ(n/2+1) · 2^(-n) · Pseq n`, so
`a(n) = 2^n (10n)! (3n)! / ((6n)! (5n)! n! Pseq n)`.  We show the denominator divides the
numerator prime by prime, via Legendre's formula and floor-function inequalities. -/

lemma fl_scale (s m k e : ℕ) (he : 0 < e) : k*s/m = (k*e*s/m)/e := by
  rw [Nat.div_div_eq_div_mul, show k*e*s = e*(k*s) by ring, mul_comm m e,
      Nat.mul_div_mul_left _ _ he]

lemma fl_lt (s m k : ℕ) (hm : 0 < m) (hs : s < m) (hk : 0 < k) : k*s/m < k :=
  (Nat.div_lt_iff_lt_mul hm).2 (by nlinarith)

lemma fl_E (m q s k : ℕ) (hm : 0 < m) : k*(m*q+s)/m = k*q + (k*s)/m := by
  have h : k*(m*q+s) = m*(k*q) + k*s := by ring
  rw [h, Nat.mul_add_div hm]

/-- Odd-prime floor inequality (parity-free form). -/
lemma landau178 (n m : ℕ) (hm : 0 < m) :
    6*n/m + 5*n/m + n/m + (3*n/m - n/m + 1)/2 ≤ 10*n/m + 3*n/m := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < m ∧ n = m*q+s :=
    ⟨n/m, n%m, Nat.mod_lt _ hm, by rw [Nat.div_add_mod]⟩
  have h1 : (m*q+s)/m = q := by
    have := fl_E m q s 1 hm; simp only [one_mul] at this; rw [this, Nat.div_eq_of_lt hs]; ring
  rw [h1, fl_E m q s 6 hm, fl_E m q s 5 hm, fl_E m q s 10 hm, fl_E m q s 3 hm]
  have hT := fl_lt s m 30 hm hs (by norm_num)
  rw [fl_scale s m 6 5 (by norm_num), fl_scale s m 5 6 (by norm_num),
      fl_scale s m 10 3 (by norm_num), fl_scale s m 3 10 (by norm_num)]
  norm_num only
  generalize 30*s/m = T at hT ⊢
  interval_cases T <;> omega

/-- `2`-adic floor inequality for odd `n` (also valid for every modulus). -/
lemma landauL (n m : ℕ) (hm : 0 < m) :
    6*n/m + 5*n/m + n/m ≤ 10*n/m + 3*n/m := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < m ∧ n = m*q+s :=
    ⟨n/m, n%m, Nat.mod_lt _ hm, by rw [Nat.div_add_mod]⟩
  have h1 : (m*q+s)/m = q := by
    have := fl_E m q s 1 hm; simp only [one_mul] at this; rw [this, Nat.div_eq_of_lt hs]; ring
  rw [h1, fl_E m q s 6 hm, fl_E m q s 5 hm, fl_E m q s 10 hm, fl_E m q s 3 hm]
  have hT := fl_lt s m 30 hm hs (by norm_num)
  rw [fl_scale s m 6 5 (by norm_num), fl_scale s m 5 6 (by norm_num),
      fl_scale s m 10 3 (by norm_num), fl_scale s m 3 10 (by norm_num)]
  norm_num only
  generalize 30*s/m = T at hT ⊢
  interval_cases T <;> omega

/-- Vasyunin's inequality for `(20m)!(6m)!m! / ((12m)!(10m)!(3m)!(2m)!)`. -/
lemma landauV (n m : ℕ) (hm : 0 < m) :
    12*n/m + 10*n/m + 3*n/m + 2*n/m ≤ 20*n/m + 6*n/m + n/m := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < m ∧ n = m*q+s :=
    ⟨n/m, n%m, Nat.mod_lt _ hm, by rw [Nat.div_add_mod]⟩
  have h1 : (m*q+s)/m = q := by
    have := fl_E m q s 1 hm; simp only [one_mul] at this; rw [this, Nat.div_eq_of_lt hs]; ring
  rw [h1, fl_E m q s 12 hm, fl_E m q s 10 hm, fl_E m q s 3 hm, fl_E m q s 2 hm,
      fl_E m q s 20 hm, fl_E m q s 6 hm]
  have hT := fl_lt s m 60 hm hs (by norm_num)
  rw [fl_scale s m 12 5 (by norm_num), fl_scale s m 10 6 (by norm_num),
      fl_scale s m 3 20 (by norm_num), fl_scale s m 2 30 (by norm_num),
      fl_scale s m 20 3 (by norm_num), fl_scale s m 6 10 (by norm_num)]
  norm_num only
  generalize 60*s/m = T at hT ⊢
  interval_cases T <;> omega

lemma residue_count_le2 (a b c : ℕ) :
    #{x ∈ Ioc a b | x % 2 = c} ≤ (b - a + 1) / 2 := by
  rw [← Finset.card_range ((b - a + 1) / 2)]
  apply Finset.card_le_card_of_injOn (fun x => (x - 1 - a) / 2)
  · intro x hx; simp only [Finset.mem_coe, mem_filter, mem_Ioc, mem_range] at *; omega
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_filter, mem_Ioc] at hx hy
    simp only at hxy; omega

lemma bij_k_x2 (n m : ℕ) :
    #{k ∈ Icc 1 n | m ∣ n+2*k}
      = #{x ∈ Ioc n (3*n) | m ∣ x ∧ x % 2 = n % 2} := by
  apply Finset.card_bij (fun k _ => n+2*k)
  · intro k hk; rw [mem_filter, mem_Icc] at hk; rw [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, hk.2, by omega⟩
  · intro a ha b hb h; rw [mem_filter, mem_Icc] at ha hb; omega
  · intro x hx; rw [mem_filter, mem_Ioc] at hx
    refine ⟨(x - n)/2, ?_, by omega⟩
    rw [mem_filter, mem_Icc]; exact ⟨by omega, by
      have : n+2*((x-n)/2) = x := by omega
      rw [this]; exact hx.2.1⟩

lemma mult_count_eq2 (n m c : ℕ) (hm : 0 < m) :
    #{x ∈ Ioc n (3*n) | m ∣ x ∧ x % 2 = c}
      = #{t ∈ Ioc (n/m) (3*n/m) | (m*t) % 2 = c} := by
  apply Finset.card_bij (fun x _ => x/m)
  · intro x hx
    rw [mem_filter, mem_Ioc] at hx ⊢
    obtain ⟨⟨h1, h2⟩, hd, h3⟩ := hx
    obtain ⟨w, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left w hm]
    refine ⟨⟨(Nat.div_lt_iff_lt_mul hm).2 (by nlinarith [h1]),
            (Nat.le_div_iff_mul_le hm).2 (by nlinarith [h2])⟩, h3⟩
  · intro a ha b hb h
    rw [mem_filter] at ha hb
    obtain ⟨wa, rfl⟩ := ha.2.1; obtain ⟨wb, rfl⟩ := hb.2.1
    rw [Nat.mul_div_cancel_left wa hm, Nat.mul_div_cancel_left wb hm] at h; rw [h]
  · intro t ht
    rw [mem_filter, mem_Ioc] at ht
    obtain ⟨⟨h1, h2⟩, h3⟩ := ht
    refine ⟨m*t, ?_, Nat.mul_div_cancel_left t hm⟩
    rw [mem_filter, mem_Ioc]
    have l1 : n < t*m := (Nat.div_lt_iff_lt_mul hm).1 h1
    have l2 : t*m ≤ 3*n := (Nat.le_div_iff_mul_le hm).1 h2
    exact ⟨⟨by nlinarith [l1], by nlinarith [l2]⟩, ⟨t, rfl⟩, h3⟩

lemma count_mt_le2 (A B m c : ℕ) (hm2 : ¬ 2 ∣ m) :
    #{t ∈ Ioc A B | (m*t) % 2 = c} ≤ (B - A + 1)/2 := by
  have key : {t ∈ Ioc A B | (m*t) % 2 = c} = {t ∈ Ioc A B | t % 2 = c} :=
    Finset.filter_congr (fun t _ => by rw [Nat.mul_mod]; have : m % 2 = 1 := by omega
                                       rw [this, one_mul, Nat.mod_mod])
  rw [key]; exact residue_count_le2 A B c

lemma term_count_bound2 (n m : ℕ) (hm : 0 < m) (hm2 : ¬ 2 ∣ m) :
    6*n/m + 5*n/m + n/m + #{k ∈ Icc 1 n | m ∣ n+2*k} ≤ 10*n/m + 3*n/m := by
  rw [bij_k_x2 n m, mult_count_eq2 n m (n%2) hm]
  have h1 := count_mt_le2 (n/m) (3*n/m) m (n%2) hm2
  have h2 := landau178 n m hm
  omega

def Pseq (n : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 n, (n+2*k)

lemma Pseq_ne (n : ℕ) : Pseq n ≠ 0 := by
  unfold Pseq; apply Finset.prod_ne_zero_iff.2; intro k hk; rw [mem_Icc] at hk; omega

lemma small_bound2 (n q k : ℕ) (hq : 2 ≤ q) (hk : k ∈ Icc 1 n) : n+2*k < q^(10*n+1) := by
  rw [mem_Icc] at hk
  have h1 : 3*n < 2^(3*n) := Nat.lt_two_pow_self
  have h2 : 2^(10*n+1) ≤ q^(10*n+1) := Nat.pow_le_pow_left hq _
  have h3 : (2:ℕ)^(3*n) ≤ 2^(10*n+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma vq_Pseq_swap (n q : ℕ) (hq : q.Prime) :
    (Pseq n).factorization q
      = ∑ i ∈ Ico 1 (10*n+1), #{k ∈ Icc 1 n | q^i ∣ n+2*k} := by
  have hq2 : 2 ≤ q := hq.two_le
  unfold Pseq
  rw [Nat.factorization_prod (by intro k hk; rw [mem_Icc] at hk; omega)]
  simp only [Finsupp.finset_sum_apply]
  have step : ∀ k ∈ Icc 1 n, (n+2*k).factorization q
      = ∑ i ∈ Ico 1 (10*n+1), (if q^i ∣ n+2*k then 1 else 0) := by
    intro k hk
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hq (by rw [mem_Icc] at hk; omega)
          (small_bound2 n q k hq2 hk)]
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.card_filter]

lemma log_bound10 (q n : ℕ) (hq : 2 ≤ q) (K : ℕ) (hK : K ≤ 10*n) : Nat.log q K < 10*n+1 := by
  rcases Nat.eq_zero_or_pos K with h | h
  · simp [h]
  · have hb : K < q^(10*n+1) := by
      have h2 : 10*n < 2^(10*n) := Nat.lt_two_pow_self
      calc K ≤ 10*n := hK
        _ < 2^(10*n) := h2
        _ ≤ q^(10*n) := Nat.pow_le_pow_left hq _
        _ ≤ q^(10*n+1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.log_lt_of_lt_pow (by omega) hb

lemma vq_odd_bound (n q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    (6*n)!.factorization q + (5*n)!.factorization q + (n)!.factorization q
      + (Pseq n).factorization q ≤ (10*n)!.factorization q + (3*n)!.factorization q := by
  have hqq := hq.two_le
  have h2nd : ∀ i, ¬ (2 ∣ q^i) := by
    intro i hd
    have hdq : (2:ℕ) ∣ q := Nat.prime_two.dvd_of_dvd_pow hd
    have : (2:ℕ) = q := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hdq
    omega
  rw [Nat.factorization_factorial hq (log_bound10 q n hqq (6*n) (by omega)),
      Nat.factorization_factorial hq (log_bound10 q n hqq (5*n) (by omega)),
      Nat.factorization_factorial hq (log_bound10 q n hqq n (by omega)),
      Nat.factorization_factorial hq (log_bound10 q n hqq (10*n) (by omega)),
      Nat.factorization_factorial hq (log_bound10 q n hqq (3*n) (by omega)),
      vq_Pseq_swap n q hq]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact term_count_bound2 n (q^i) (pow_pos hq.pos i) (h2nd i)

lemma Pseq_two (m : ℕ) : Pseq (2*m) * m ! = 2^(2*m) * (3*m)! := by
  have key : Pseq (2*m) = 2^(2*m) * (m+1).ascFactorial (2*m) := by
    unfold Pseq
    have h1 : ∀ k ∈ Finset.Icc 1 (2*m), 2*m+2*k = 2*(m+k) := by intro k _; ring
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const,
        prod_Icc_ascFactorial, Nat.card_Icc, show (2*m+1)-1 = 2*m from by omega]
  rw [key, mul_assoc, mul_comm ((m+1).ascFactorial (2*m)) (m !),
      Nat.factorial_mul_ascFactorial]
  congr 2
  omega

lemma v2_bound (n : ℕ) :
    (6*n)!.factorization 2 + (5*n)!.factorization 2 + (n)!.factorization 2
      + (Pseq n).factorization 2 ≤ n + (10*n)!.factorization 2 + (3*n)!.factorization 2 := by
  have h2 : Nat.Prime 2 := Nat.prime_two
  have L : ∀ K N : ℕ, K ≤ 20*N → Nat.log 2 K < 20*N+1 := by
    intro K N hK; exact lt_of_le_of_lt (Nat.log_le_self 2 K) (by omega)
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · -- n = 2m
    have hn : n = 2*m := by omega
    subst hn
    have hQ := Pseq_two m
    have hval : (Pseq (2*m)).factorization 2 + (m)!.factorization 2
        = 2*m + (3*m)!.factorization 2 := by
      have := congrArg (fun t => t.factorization 2) hQ
      simp only at this
      rw [Nat.factorization_mul (Pseq_ne _) (Nat.factorial_ne_zero _),
          Nat.factorization_mul (by positivity) (Nat.factorial_ne_zero _),
          Nat.factorization_pow] at this
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at this
      rw [Nat.Prime.factorization_self h2] at this
      omega
    have hV : (12*m)!.factorization 2 + (10*m)!.factorization 2 + (3*m)!.factorization 2
        + (2*m)!.factorization 2
        ≤ (20*m)!.factorization 2 + (6*m)!.factorization 2 + (m)!.factorization 2 := by
      rw [Nat.factorization_factorial h2 (L (12*m) m (by omega)),
          Nat.factorization_factorial h2 (L (10*m) m (by omega)),
          Nat.factorization_factorial h2 (L (3*m) m (by omega)),
          Nat.factorization_factorial h2 (L (2*m) m (by omega)),
          Nat.factorization_factorial h2 (L (20*m) m (by omega)),
          Nat.factorization_factorial h2 (L (6*m) m (by omega)),
          Nat.factorization_factorial h2 (L m m (by omega))]
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      exact landauV m (2^i) (pow_pos (by norm_num) i)
    rw [show 6*(2*m) = 12*m by ring, show 5*(2*m) = 10*m by ring,
        show 10*(2*m) = 20*m by ring, show 3*(2*m) = 6*m by ring]
    omega
  · -- n odd: every factor of Pseq n is odd
    have hP0 : (Pseq n).factorization 2 = 0 := by
      unfold Pseq
      rw [Nat.factorization_prod (fun k hk => by
            simp only [Finset.mem_Icc] at hk; omega), Finsupp.finset_sum_apply]
      apply Finset.sum_eq_zero
      intro k hk
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      obtain ⟨j, hj⟩ := hodd
      omega
    have hLs : (6*n)!.factorization 2 + (5*n)!.factorization 2 + (n)!.factorization 2
        ≤ (10*n)!.factorization 2 + (3*n)!.factorization 2 := by
      rw [Nat.factorization_factorial h2 (L (6*n) n (by omega)),
          Nat.factorization_factorial h2 (L (5*n) n (by omega)),
          Nat.factorization_factorial h2 (L n n (by omega)),
          Nat.factorization_factorial h2 (L (10*n) n (by omega)),
          Nat.factorization_factorial h2 (L (3*n) n (by omega))]
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      exact landauL n (2^i) (pow_pos (by norm_num) i)
    omega

theorem integrality178 (n : ℕ) :
    (6*n)! * (5*n)! * n ! * Pseq n ∣ 2^n * (10*n)! * (3*n)! := by
  have hL : (6*n)! * (5*n)! * n ! * Pseq n ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _)) (Pseq_ne n)
  have hR : 2^n * (10*n)! * (3*n)! ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _)
  apply (Nat.factorization_le_iff_dvd hL hR).mp
  rw [Finsupp.le_def]
  intro q
  by_cases hq : q.Prime
  · rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _)
          (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)) (Pseq_ne n),
        Nat.factorization_mul (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
          (Nat.factorial_ne_zero _),
        Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
        Nat.factorization_mul (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.factorial_ne_zero _))
          (Nat.factorial_ne_zero _),
        Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (Nat.factorial_ne_zero _),
        Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hq2 : q = 2
    · subst hq2
      rw [Nat.Prime.factorization_self Nat.prime_two]
      have := v2_bound n
      omega
    · have h20 : (2:ℕ).factorization q = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hd
        exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hd)
      have := vq_odd_bound n q hq hq2
      rw [h20]; omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq]
    exact Nat.zero_le _

def aexact (n : ℕ) : ℕ := (2^n * (10*n)! * (3*n)!) / ((6*n)! * (5*n)! * n ! * Pseq n)

lemma aexact_spec (n : ℕ) : ((6*n)! * (5*n)! * n ! * Pseq n) * aexact n = 2^n * (10*n)! * (3*n)! :=
  Nat.mul_div_cancel' (integrality178 n)
/-! ## Foundational lemmas -/

theorem sum_units_sq_eq_zero (n : ℕ) [NeZero n] (h2 : IsUnit (2 : ZMod n)) (h3 : IsUnit (3 : ZMod n)) :
    ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 = 0 := by
  set u2 := h2.unit with hu2
  have hspec : (u2 : ZMod n) = 2 := h2.unit_spec
  set S := ∑ u : (ZMod n)ˣ, ((u : ZMod n))^2 with hS
  have reindex : ∑ u : (ZMod n)ˣ, (((u2 * u : (ZMod n)ˣ) : ZMod n))^2 = S := by
    rw [hS]; exact Equiv.sum_comp (Equiv.mulLeft u2) (fun v => ((v : ZMod n))^2)
  have expand : ∑ u : (ZMod n)ˣ, (((u2 * u : (ZMod n)ˣ) : ZMod n))^2 = 4 * S := by
    rw [hS, Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _
    push_cast; rw [hspec]; ring
  have hEq : S = 4 * S := reindex.symm.trans expand
  have h3S : (3 : ZMod n) * S = 0 := by linear_combination -hEq
  exact h3.mul_right_eq_zero.mp h3S

theorem prod_add_delta {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℤ) (δ : ℤ) :
    (∏ i ∈ s, (b i + δ)) ≡ (∏ i ∈ s, b i) + δ * (∑ i ∈ s, ∏ j ∈ s.erase i, b j) [ZMOD δ^2] := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hcong : (b a + δ) * (∏ i ∈ s, (b i + δ)) ≡
        (b a + δ) * ((∏ i ∈ s, b i) + δ * (∑ i ∈ s, ∏ j ∈ s.erase i, b j)) [ZMOD δ^2] :=
      Int.ModEq.mul_left _ ih
    refine hcong.trans ?_
    have e1 : ∏ j ∈ (insert a s).erase a, b j = ∏ j ∈ s, b j := by rw [Finset.erase_insert ha]
    have e2 : ∀ i ∈ s, ∏ j ∈ (insert a s).erase i, b j = b a * ∏ j ∈ s.erase i, b j := by
      intro i hi
      rw [Finset.erase_insert_of_ne (by rintro rfl; exact ha hi)]
      rw [Finset.prod_insert (by simp [Finset.mem_erase]; tauto)]
    rw [e1]
    calc (b a + δ) * ((∏ i ∈ s, b i) + δ * (∑ i ∈ s, ∏ j ∈ s.erase i, b j))
        = (b a * (∏ i ∈ s, b i)) + δ * ((∏ i ∈ s, b i) + b a * (∑ i ∈ s, ∏ j ∈ s.erase i, b j)) + δ^2 * (∑ i ∈ s, ∏ j ∈ s.erase i, b j) := by ring
      _ ≡ (b a * (∏ i ∈ s, b i)) + δ * ((∏ i ∈ s, b i) + b a * (∑ i ∈ s, ∏ j ∈ s.erase i, b j)) + 0 [ZMOD δ^2] := by
            apply Int.ModEq.add_left
            exact (Int.modEq_zero_iff_dvd.mpr (dvd_mul_right (δ^2) _))
      _ = (b a * ∏ i ∈ s, b i) + δ * ((∏ i ∈ s, b i) + ∑ i ∈ s, b a * ∏ j ∈ s.erase i, b j) := by
            rw [Finset.mul_sum]; ring
      _ = (b a * ∏ i ∈ s, b i) + δ * ((∏ j ∈ s, b j) + ∑ i ∈ s, ∏ j ∈ (insert a s).erase i, b j) := by
            rw [Finset.sum_congr rfl e2]

theorem prod_pair {M : Type*} [CommMonoid M] (q : ℕ) (hq : Odd q) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ e, 1 ≤ e → e ≤ q - 1 → (P e ↔ P (q - e))) (f : ℕ → M) :
    ∏ e ∈ (Finset.Icc 1 (q-1)).filter P, f e
      = ∏ e ∈ (Finset.Icc 1 ((q-1)/2)).filter P, (f e * f (q - e)) := by
  obtain ⟨k, hk⟩ := hq
  have hqpos : 1 ≤ q := by omega
  set L := (Finset.Icc 1 ((q-1)/2)).filter P with hL
  set Up := (Finset.Icc ((q-1)/2 + 1) (q-1)).filter P with hUp
  have hsplit : (Finset.Icc 1 (q-1)).filter P = L ∪ Up := by
    rw [hL, hUp, ← Finset.filter_union]; congr 1
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint L Up := by
    rw [hL, hUp]; apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  have hinj : Set.InjOn (fun e => q - e) L := by
    intro a ha b hb hab
    simp only [hL, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
    simp only at hab; omega
  have himg : Up = L.image (fun e => q - e) := by
    ext x
    simp only [hUp, hL, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hPx⟩
      refine ⟨q - x, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      have := (hP (q - x) (by omega) (by omega))
      rw [show q - (q - x) = x by omega] at this
      exact this.mpr hPx
    · rintro ⟨e, ⟨⟨he1, he2⟩, hPe⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      exact (hP e (by omega) (by omega)).mp hPe
  rw [hsplit, Finset.prod_union hdisj, himg, Finset.prod_image hinj, ← Finset.prod_mul_distrib]

theorem sum_pair {M : Type*} [AddCommMonoid M] (q : ℕ) (hq : Odd q) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ e, 1 ≤ e → e ≤ q - 1 → (P e ↔ P (q - e))) (f : ℕ → M) :
    ∑ e ∈ (Finset.Icc 1 (q-1)).filter P, f e
      = ∑ e ∈ (Finset.Icc 1 ((q-1)/2)).filter P, (f e + f (q - e)) := by
  obtain ⟨k, hk⟩ := hq
  have hqpos : 1 ≤ q := by omega
  set L := (Finset.Icc 1 ((q-1)/2)).filter P with hL
  set Up := (Finset.Icc ((q-1)/2 + 1) (q-1)).filter P with hUp
  have hsplit : (Finset.Icc 1 (q-1)).filter P = L ∪ Up := by
    rw [hL, hUp, ← Finset.filter_union]; congr 1
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint L Up := by
    rw [hL, hUp]; apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  have hinj : Set.InjOn (fun e => q - e) L := by
    intro a ha b hb hab
    simp only [hL, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
    simp only at hab; omega
  have himg : Up = L.image (fun e => q - e) := by
    ext x
    simp only [hUp, hL, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hPx⟩
      refine ⟨q - x, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      have := (hP (q - x) (by omega) (by omega))
      rw [show q - (q - x) = x by omega] at this
      exact this.mpr hPx
    · rintro ⟨e, ⟨⟨he1, he2⟩, hPe⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      exact (hP e (by omega) (by omega)).mp hPe
  rw [hsplit, Finset.sum_union hdisj, himg, Finset.sum_image hinj, ← Finset.sum_add_distrib]

theorem sum_Ucop_eq_units {M : Type*} [AddCommMonoid M] (q : ℕ) [NeZero q] (hq : 1 < q) (g : ZMod q → M) :
    ∑ e ∈ (Finset.Icc 1 (q-1)).filter (fun e => Nat.Coprime e q), g (e : ZMod q)
      = ∑ u : (ZMod q)ˣ, g (u : ZMod q) := by
  haveI : Fact (1 < q) := ⟨hq⟩
  refine Finset.sum_bij'
    (i := fun e he => ZMod.unitOfCoprime e ((Finset.mem_filter.mp he).2))
    (j := fun u _ => (u : ZMod q).val)
    (fun a ha => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro u _
    dsimp only
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ZMod.val_coe_unit_coprime u⟩
    · have h0 : (u : ZMod q) ≠ 0 := u.isUnit.ne_zero
      have hv0 : (u : ZMod q).val ≠ 0 := fun h => h0 ((ZMod.val_eq_zero _).mp h)
      omega
    · have := ZMod.val_lt (u : ZMod q); omega
  · intro a ha
    dsimp only
    have ha' := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  · intro u _
    dsimp only
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, ZMod.natCast_val, ZMod.cast_id]
  · intro a ha
    dsimp only
    rw [ZMod.coe_unitOfCoprime]

/- Generalized Wolstenholme (W2) for q = p^r -/

theorem neg_inv_sq {n:ℕ} (a : ZMod n) (h : IsUnit a) : ((-a)⁻¹)^2 = (a⁻¹)^2 := by
  obtain ⟨u, rfl⟩ := h
  have h1 : (-(↑u:ZMod n)) = ↑((-1) * u) := by push_cast; ring
  rw [h1, ZMod.inv_coe_unit, ZMod.inv_coe_unit, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
  congr 1
  rw [mul_inv_rev, mul_pow]
  simp


theorem zmod_inv_sq {n:ℕ}(a:ZMod n)(h:IsUnit a): (a⁻¹)^2 = (a^2)⁻¹ := by
  obtain ⟨u,rfl⟩ := h
  rw [ZMod.inv_coe_unit, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ZMod.inv_coe_unit, inv_pow]

theorem zmod_neg_inv {n:ℕ}(a:ZMod n)(h:IsUnit a): (-a)⁻¹ = -(a⁻¹) := by
  obtain ⟨u,rfl⟩ := h
  rw [← Units.val_neg, ZMod.inv_coe_unit, ZMod.inv_coe_unit, ← Units.val_neg]
  congr 1

theorem zmod_mul_inv {n:ℕ}(a b:ZMod n)(ha:IsUnit a)(hb:IsUnit b): (a*b)⁻¹ = a⁻¹*b⁻¹ := by
  obtain ⟨u,rfl⟩ := ha; obtain ⟨v,rfl⟩ := hb
  rw [← Units.val_mul, ZMod.inv_coe_unit, ZMod.inv_coe_unit, ZMod.inv_coe_unit,
      ← Units.val_mul, mul_inv_rev, mul_comm]


theorem zmod_leave_one {n:ℕ}{ι:Type*}[DecidableEq ι](s:Finset ι)(f:ι→ZMod n)(e:ι)(he:e∈s)
    (hu:IsUnit (f e)) : (∏ e' ∈ s, f e') * (f e)⁻¹ = ∏ e' ∈ s.erase e, f e' := by
  have h1 : f e * ∏ e' ∈ s.erase e, f e' = ∏ e' ∈ s, f e' := Finset.mul_prod_erase s f he
  have h2 : (f e)⁻¹ * f e = 1 := ZMod.inv_mul_of_unit _ hu
  calc (∏ e' ∈ s, f e') * (f e)⁻¹ = ((f e)⁻¹ * f e) * ∏ e' ∈ s.erase e, f e' := by rw [← h1]; ring
    _ = ∏ e' ∈ s.erase e, f e' := by rw [h2, one_mul]

section Wolstenholme
variable (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r)
include hp hp5 hr

theorem coprime_iff_not_dvd (e : ℕ) : Nat.Coprime e (p^r) ↔ ¬ p ∣ e := by
  rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd]

theorem two_unit : IsUnit (2 : ZMod (p^r)) := by
  rw [show (2:ZMod (p^r)) = ((2:ℕ):ZMod (p^r)) by push_cast; ring, ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right r ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))

theorem three_unit : IsUnit (3 : ZMod (p^r)) := by
  rw [show (3:ZMod (p^r)) = ((3:ℕ):ZMod (p^r)) by push_cast; ring, ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right r ((Nat.coprime_primes (by norm_num) hp).mpr (by omega))

theorem full_W2 :
    ∑ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((e:ZMod (p^r))⁻¹)^2 = 0 := by
  have hq : 1 < p^r := by
    have : p^1 ≤ p^r := Nat.pow_le_pow_right (by omega) hr
    simp at this; omega
  haveI : NeZero (p^r) := ⟨by omega⟩
  have hfe : (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e)
           = (Finset.Icc 1 (p^r-1)).filter (fun e => Nat.Coprime e (p^r)) := by
    apply Finset.filter_congr; intro e _; rw [coprime_iff_not_dvd p r hp hp5 hr]
  rw [hfe]
  rw [sum_Ucop_eq_units (p^r) hq (fun x => (x⁻¹)^2)]
  have : ∀ u : (ZMod (p^r))ˣ, ((u:ZMod (p^r))⁻¹)^2 = ((u⁻¹ : (ZMod (p^r))ˣ):ZMod (p^r))^2 := by
    intro u; rw [ZMod.inv_coe_unit]
  simp_rw [this]
  refine (Fintype.sum_bijective (fun x : (ZMod (p^r))ˣ => x⁻¹) (Equiv.inv _).bijective
    (fun x => ((x⁻¹:(ZMod (p^r))ˣ):ZMod (p^r))^2) (fun x => ((x:ZMod (p^r)))^2) (fun x => rfl)).trans ?_
  exact sum_units_sq_eq_zero _ (two_unit p r hp hp5 hr) (three_unit p r hp hp5 hr)

theorem half_W2 :
    ∑ e ∈ (Finset.Icc 1 ((p^r-1)/2)).filter (fun e => ¬ p ∣ e), ((e:ZMod (p^r))⁻¹)^2 = 0 := by
  have hq : 1 < p^r := by
    have : p^1 ≤ p^r := Nat.pow_le_pow_right (by omega) hr
    simp at this; omega
  haveI : NeZero (p^r) := ⟨by omega⟩
  have hodd : Odd (p^r) := (hp.odd_of_ne_two (by omega)).pow
  set L := (Finset.Icc 1 ((p^r-1)/2)).filter (fun e => ¬ p ∣ e) with hLdef
  set F : ℕ → ZMod (p^r) := fun e => ((e:ZMod (p^r))⁻¹)^2 with hFdef
  have hP : ∀ e, 1 ≤ e → e ≤ (p^r) - 1 → ((¬ p ∣ e) ↔ (¬ p ∣ (p^r - e))) := by
    intro e he1 he2
    have hpq : p ∣ p^r := dvd_pow_self p (by omega)
    constructor
    · intro h hd; exact h (by have := Nat.dvd_sub hpq hd; rwa [Nat.sub_sub_self (by omega)] at this)
    · intro h hd; exact h (Nat.dvd_sub hpq hd)
  have hpair := sum_pair (p^r) hodd (fun e => ¬ p ∣ e) hP F
  have hterm : ∀ e ∈ L, F e + F (p^r - e) = 2 * F e := by
    intro e he
    simp only [hLdef, Finset.mem_filter, Finset.mem_Icc] at he
    have hele : e ≤ p^r := by omega
    have hcast : ((p^r - e : ℕ) : ZMod (p^r)) = -(e : ZMod (p^r)) := by
      rw [Nat.cast_sub hele, ZMod.natCast_self]; ring
    have hunit : IsUnit ((e:ZMod (p^r))) := by
      rw [ZMod.isUnit_iff_coprime]; exact (coprime_iff_not_dvd p r hp hp5 hr e).mpr he.2
    show F e + F (p^r - e) = 2 * F e
    rw [hFdef]; simp only; rw [hcast, neg_inv_sq _ hunit]; ring
  rw [full_W2 p r hp hp5 hr] at hpair  -- hpair: 0 = ∑_L (F e + F(q-e))
  rw [Finset.sum_congr rfl hterm] at hpair
  rw [← Finset.mul_sum] at hpair
  have h2 := two_unit p r hp hp5 hr
  have := h2.mul_right_eq_zero.mp hpair.symm
  exact this

theorem block_cong (c : ℕ) :
    (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((c*p^r + e : ℕ) : ℤ))
      ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((e:ℕ) : ℤ)) [ZMOD ((p^r : ℕ) : ℤ)^3] := by
  have hq1 : 1 < p^r := by
    have : p^1 ≤ p^r := Nat.pow_le_pow_right (by omega) hr
    simp at this; omega
  haveI : NeZero (p^r) := ⟨by omega⟩
  have hodd : Odd (p^r) := (hp.odd_of_ne_two (by omega)).pow
  have hP : ∀ e, 1 ≤ e → e ≤ (p^r) - 1 → ((¬ p ∣ e) ↔ (¬ p ∣ (p^r - e))) := by
    intro e he1 he2
    have hpq : p ∣ p^r := dvd_pow_self p (by omega)
    constructor
    · intro h hd; exact h (by have := Nat.dvd_sub hpq hd; rwa [Nat.sub_sub_self (by omega)] at this)
    · intro h hd; exact h (Nat.dvd_sub hpq hd)
  set Lf := (Finset.Icc 1 ((p^r-1)/2)).filter (fun e => ¬ p ∣ e) with hLf
  set b : ℕ → ℤ := fun e => (e:ℤ) * ((p^r:ℤ) - (e:ℤ)) with hbdef
  set δ : ℤ := (c:ℤ) * ((c:ℤ)+1) * (p^r:ℤ)^2 with hδdef
  have hLHS := prod_pair (p^r) hodd (fun e => ¬ p ∣ e) hP (fun e => ((c*p^r+e:ℕ):ℤ))
  have hRHS := prod_pair (p^r) hodd (fun e => ¬ p ∣ e) hP (fun e => ((e:ℕ):ℤ))
  rw [hLHS, hRHS]
  have hbe : ∀ e ∈ Lf, ((c*p^r+e:ℕ):ℤ) * ((c*p^r+(p^r-e):ℕ):ℤ) = b e + δ := by
    intro e he
    simp only [hLf, Finset.mem_filter, Finset.mem_Icc] at he
    have hle : e ≤ p^r := by omega
    rw [hbdef, hδdef]; push_cast [Nat.cast_sub hle]; ring
  have hbe2 : ∀ e ∈ Lf, ((e:ℕ):ℤ) * ((p^r-e:ℕ):ℤ) = b e := by
    intro e he
    simp only [hLf, Finset.mem_filter, Finset.mem_Icc] at he
    have hle : e ≤ p^r := by omega
    rw [hbdef]; push_cast [Nat.cast_sub hle]; ring
  rw [Finset.prod_congr rfl hbe, Finset.prod_congr rfl hbe2]
  -- Now: ∏_{Lf}(b e + δ) ≡ ∏_{Lf} b e  [ZMOD (p^r)^3]
  have hpad := prod_add_delta Lf b δ
  have hq3δ2 : ((p^r:ℤ))^3 ∣ δ^2 := ⟨(c:ℤ)^2*((c:ℤ)+1)^2*(p^r:ℤ), by rw [hδdef]; ring⟩
  have h1 := hpad.of_dvd hq3δ2
  -- q ∣ D
  have hunit : ∀ e' ∈ Lf, IsUnit ((e':ZMod (p^r))) := by
    intro e' he'
    simp only [hLf, Finset.mem_filter] at he'
    rw [ZMod.isUnit_iff_coprime]; exact (coprime_iff_not_dvd p r hp hp5 hr e').mpr he'.2
  have hbcast : ∀ e', ((b e' : ℤ) : ZMod (p^r)) = -(((e':ℕ):ZMod (p^r)))^2 := by
    intro e'; rw [hbdef]; push_cast
    rw [show ((p:ZMod (p^r)))^r = 0 by rw [← Nat.cast_pow, ZMod.natCast_self]]; ring
  have hDcast : ((∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e' : ℤ) : ZMod (p^r)) = 0 := by
    push_cast
    simp_rw [hbcast]
    have key : ∀ e ∈ Lf, ∏ e' ∈ Lf.erase e, (-(((e':ℕ):ZMod (p^r)))^2)
        = (∏ e' ∈ Lf, (-(((e':ℕ):ZMod (p^r)))^2)) * (-(((e:ℕ):ZMod (p^r)))^2)⁻¹ := by
      intro e he
      rw [zmod_leave_one Lf (fun e' => -(((e':ℕ):ZMod (p^r)))^2) e he
          (((hunit e he).pow 2).neg)]
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
    have hz : ∑ e ∈ Lf, (-(((e:ℕ):ZMod (p^r)))^2)⁻¹ = 0 := by
      have heq : ∀ e ∈ Lf, (-(((e:ℕ):ZMod (p^r)))^2)⁻¹ = -((((e:ℕ):ZMod (p^r)))⁻¹)^2 := by
        intro e he
        rw [zmod_neg_inv _ ((hunit e he).pow 2), zmod_inv_sq _ (hunit e he)]
      rw [Finset.sum_congr rfl heq]
      rw [Finset.sum_neg_distrib, half_W2 p r hp hp5 hr, neg_zero]
    rw [hz, mul_zero]
  have hD : (p^r:ℤ) ∣ (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^r)).mp hDcast
    exact_mod_cast this
  have hδD : ((p^r:ℤ))^3 ∣ δ * (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') := by
    obtain ⟨D', hD'⟩ := hD
    exact ⟨(c:ℤ)*((c:ℤ)+1)*D', by rw [hδdef, hD']; ring⟩
  calc (∏ e ∈ Lf, (b e + δ)) ≡ (∏ e ∈ Lf, b e) + δ * (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') [ZMOD ((p^r:ℤ))^3] := h1
    _ ≡ (∏ e ∈ Lf, b e) + 0 [ZMOD ((p^r:ℤ))^3] := by
        apply Int.ModEq.add_left; exact (Int.modEq_zero_iff_dvd.mpr hδD)
    _ = ∏ e ∈ Lf, b e := by ring

end Wolstenholme

/- Gauss factorial product and its block structure -/

def Gcop (p N : ℕ) : ℕ := ∏ e ∈ (Finset.Icc 1 N).filter (fun e => ¬ p ∣ e), e

theorem gcop_succ (p q K : ℕ) (hpq : p ∣ q) :
    Gcop p ((K+1)*q) = Gcop p (K*q) * ∏ e ∈ (Finset.Icc 1 q).filter (fun e => ¬ p ∣ e), (K*q + e) := by
  unfold Gcop
  have hexp : (K+1)*q = K*q + q := by ring
  have hsplit : (Finset.Icc 1 ((K+1)*q)).filter (fun e => ¬ p ∣ e)
      = ((Finset.Icc 1 (K*q)).filter (fun e => ¬ p ∣ e))
        ∪ ((Finset.Icc (K*q+1) ((K+1)*q)).filter (fun e => ¬ p ∣ e)) := by
    rw [← Finset.filter_union]; congr 1
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint ((Finset.Icc 1 (K*q)).filter (fun e => ¬ p ∣ e))
        ((Finset.Icc (K*q+1) ((K+1)*q)).filter (fun e => ¬ p ∣ e)) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  rw [hsplit, Finset.prod_union hdisj]
  congr 1
  rw [show (Finset.Icc (K*q+1) ((K+1)*q)).filter (fun e => ¬ p ∣ e)
        = ((Finset.Icc 1 q).filter (fun e => ¬ p ∣ e)).image (fun e => K*q + e) from ?_]
  · rw [Finset.prod_image (by intro a _ b _ h; exact Nat.add_left_cancel h)]
  · ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hpx⟩
      refine ⟨x - K*q, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      intro hd; apply hpx
      have h2 : p ∣ K*q := Dvd.dvd.mul_left hpq K
      have := Nat.dvd_add h2 hd
      rwa [Nat.add_sub_cancel' (by omega : K*q ≤ x)] at this
    · rintro ⟨e, ⟨⟨he1, he2⟩, hpe⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro hd; apply hpe
      have h2 : p ∣ K*q := Dvd.dvd.mul_left hpq K
      have := Nat.dvd_sub hd h2
      rwa [Nat.add_sub_cancel_left] at this

theorem core_G (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (K : ℕ) :
    (Gcop p (K*p^r) : ℤ) ≡ (Gcop p (p^r) : ℤ)^K [ZMOD ((p^r : ℕ) : ℤ)^3] := by
  have hpq : p ∣ p^r := dvd_pow_self p (by omega)
  have hpr1 : 1 ≤ p^r := Nat.one_le_pow _ _ hp.pos
  have hqf : (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e)
           = (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1,h2⟩, hpx⟩
      refine ⟨⟨h1, ?_⟩, hpx⟩
      rcases Nat.lt_or_ge x (p^r) with h|h
      · omega
      · exfalso; have hx : x = p^r := by omega
        rw [hx] at hpx; exact hpx hpq
    · rintro ⟨⟨h1,h2⟩, hpx⟩
      exact ⟨⟨h1, by omega⟩, hpx⟩
  induction K with
  | zero =>
      simp only [Nat.zero_mul, pow_zero]
      unfold Gcop
      norm_num
  | succ K IH =>
      rw [gcop_succ p (p^r) K hpq]
      have hcast : ((Gcop p (K*p^r) * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), (K*p^r + e) : ℕ) : ℤ)
          = (Gcop p (K*p^r):ℤ) * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), ((K*p^r + e : ℕ):ℤ) := by
        push_cast; ring
      rw [hcast]
      have hGcop : (Gcop p (p^r):ℤ) = ∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((e:ℕ):ℤ) := by
        unfold Gcop; rw [hqf]; push_cast; rfl
      have hblock : (∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), ((K*p^r + e : ℕ):ℤ))
          ≡ (Gcop p (p^r):ℤ) [ZMOD ((p^r:ℕ):ℤ)^3] := by
        rw [hqf, hGcop]
        exact block_cong p r hp hp5 hr K
      calc (Gcop p (K*p^r):ℤ) * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), ((K*p^r + e : ℕ):ℤ)
          ≡ (Gcop p (p^r):ℤ)^K * (Gcop p (p^r):ℤ) [ZMOD ((p^r:ℕ):ℤ)^3] := Int.ModEq.mul IH hblock
        _ = (Gcop p (p^r):ℤ)^(K+1) := by rw [pow_succ]


theorem block_cong2 (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (c : ℕ) :
    (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((c*p^r + 2*e : ℕ) : ℤ))
      ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ) : ℤ)) [ZMOD ((p^r : ℕ) : ℤ)^3] := by
  have hq1 : 1 < p^r := by
    have : p^1 ≤ p^r := Nat.pow_le_pow_right (by omega) hr
    simp at this; omega
  haveI : NeZero (p^r) := ⟨by omega⟩
  have hodd : Odd (p^r) := (hp.odd_of_ne_two (by omega)).pow
  have hP : ∀ e, 1 ≤ e → e ≤ (p^r) - 1 → ((¬ p ∣ e) ↔ (¬ p ∣ (p^r - e))) := by
    intro e he1 he2
    have hpq : p ∣ p^r := dvd_pow_self p (by omega)
    constructor
    · intro h hd; exact h (by have := Nat.dvd_sub hpq hd; rwa [Nat.sub_sub_self (by omega)] at this)
    · intro h hd; exact h (Nat.dvd_sub hpq hd)
  set Lf := (Finset.Icc 1 ((p^r-1)/2)).filter (fun e => ¬ p ∣ e) with hLf
  set b : ℕ → ℤ := fun e => (4:ℤ) * ((e:ℤ) * ((p^r:ℤ) - (e:ℤ))) with hbdef
  set δ : ℤ := (c:ℤ) * ((c:ℤ)+2) * (p^r:ℤ)^2 with hδdef
  have hLHS := prod_pair (p^r) hodd (fun e => ¬ p ∣ e) hP (fun e => ((c*p^r+2*e:ℕ):ℤ))
  have hRHS := prod_pair (p^r) hodd (fun e => ¬ p ∣ e) hP (fun e => ((2*e:ℕ):ℤ))
  rw [hLHS, hRHS]
  have hbe : ∀ e ∈ Lf, ((c*p^r+2*e:ℕ):ℤ) * ((c*p^r+2*(p^r-e):ℕ):ℤ) = b e + δ := by
    intro e he
    simp only [hLf, Finset.mem_filter, Finset.mem_Icc] at he
    have hle : e ≤ p^r := by omega
    rw [hbdef, hδdef]; push_cast [Nat.cast_sub hle]; ring
  have hbe2 : ∀ e ∈ Lf, ((2*e:ℕ):ℤ) * ((2*(p^r-e):ℕ):ℤ) = b e := by
    intro e he
    simp only [hLf, Finset.mem_filter, Finset.mem_Icc] at he
    have hle : e ≤ p^r := by omega
    rw [hbdef]; push_cast [Nat.cast_sub hle]; ring
  rw [Finset.prod_congr rfl hbe, Finset.prod_congr rfl hbe2]
  have hpad := prod_add_delta Lf b δ
  have hq3δ2 : ((p^r:ℤ))^3 ∣ δ^2 := ⟨(c:ℤ)^2*((c:ℤ)+2)^2*(p^r:ℤ), by rw [hδdef]; ring⟩
  have h1 := hpad.of_dvd hq3δ2
  have hunit : ∀ e' ∈ Lf, IsUnit ((e':ZMod (p^r))) := by
    intro e' he'
    simp only [hLf, Finset.mem_filter] at he'
    rw [ZMod.isUnit_iff_coprime]; exact (coprime_iff_not_dvd p r hp hp5 hr e').mpr he'.2
  have h4unit : IsUnit (4 : ZMod (p^r)) := by
    have := (two_unit p r hp hp5 hr).pow 2
    rwa [show (2:ZMod (p^r))^2 = 4 by ring] at this
  have hbcast : ∀ e', ((b e' : ℤ) : ZMod (p^r)) = -((4:ZMod (p^r)) * (((e':ℕ):ZMod (p^r)))^2) := by
    intro e'; rw [hbdef]; push_cast
    rw [show ((p:ZMod (p^r)))^r = 0 by rw [← Nat.cast_pow, ZMod.natCast_self]]; ring
  have hDcast : ((∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e' : ℤ) : ZMod (p^r)) = 0 := by
    push_cast
    simp_rw [hbcast]
    have key : ∀ e ∈ Lf, ∏ e' ∈ Lf.erase e, (-((4:ZMod (p^r)) * (((e':ℕ):ZMod (p^r)))^2))
        = (∏ e' ∈ Lf, (-((4:ZMod (p^r)) * (((e':ℕ):ZMod (p^r)))^2)))
          * (-((4:ZMod (p^r)) * (((e:ℕ):ZMod (p^r)))^2))⁻¹ := by
      intro e he
      rw [zmod_leave_one Lf (fun e' => -((4:ZMod (p^r)) * (((e':ℕ):ZMod (p^r)))^2)) e he
          ((h4unit.mul ((hunit e he).pow 2)).neg)]
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
    have hz : ∑ e ∈ Lf, (-((4:ZMod (p^r)) * (((e:ℕ):ZMod (p^r)))^2))⁻¹ = 0 := by
      have heq : ∀ e ∈ Lf, (-((4:ZMod (p^r)) * (((e:ℕ):ZMod (p^r)))^2))⁻¹
          = (-((4:ZMod (p^r))⁻¹)) * ((((e:ℕ):ZMod (p^r)))⁻¹)^2 := by
        intro e he
        rw [zmod_neg_inv _ (h4unit.mul ((hunit e he).pow 2)),
            zmod_mul_inv _ _ h4unit ((hunit e he).pow 2), ← zmod_inv_sq _ (hunit e he)]
        ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum, half_W2 p r hp hp5 hr, mul_zero]
    rw [hz, mul_zero]
  have hD : (p^r:ℤ) ∣ (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^r)).mp hDcast
    exact_mod_cast this
  have hδD : ((p^r:ℤ))^3 ∣ δ * (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') := by
    obtain ⟨D', hD'⟩ := hD
    exact ⟨(c:ℤ)*((c:ℤ)+2)*D', by rw [hδdef, hD']; ring⟩
  calc (∏ e ∈ Lf, (b e + δ)) ≡ (∏ e ∈ Lf, b e) + δ * (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') [ZMOD ((p^r:ℤ))^3] := h1
    _ ≡ (∏ e ∈ Lf, b e) + 0 [ZMOD ((p^r:ℤ))^3] := by
        apply Int.ModEq.add_left; exact (Int.modEq_zero_iff_dvd.mpr hδD)
    _ = ∏ e ∈ Lf, b e := by ring


theorem fact_split (p Y : ℕ) (hp : 0 < p) :
    (Y*p)! = p^Y * Y ! * Gcop p (Y*p) := by
  have hfac : ∏ x ∈ Finset.Icc 1 (Y*p), x = (Y*p)! := by
    rw [← Finset.Ico_add_one_right_eq_Icc]; exact Finset.prod_Ico_id_eq_factorial (Y*p)
  have hmul : (∏ k ∈ (Finset.Icc 1 (Y*p)).filter (fun k => p ∣ k), k) = p^Y * Y ! := by
    have hset : (Finset.Icc 1 (Y*p)).filter (fun k => p ∣ k) = (Finset.Icc 1 Y).image (fun m => p * m) := by
      ext k
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hk1, hk2⟩, c, rfl⟩
        have hc0 : c ≠ 0 := by rintro rfl; simp at hk1
        have hcY : c ≤ Y := Nat.le_of_mul_le_mul_left (by rw [mul_comm Y p] at hk2; exact hk2) hp
        exact ⟨c, ⟨Nat.one_le_iff_ne_zero.mpr hc0, hcY⟩, rfl⟩
      · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
        exact ⟨⟨Nat.mul_pos hp hm1, by rw [mul_comm p m]; exact mul_le_mul_right' hm2 p⟩, dvd_mul_right p m⟩
    have hfacY : ∏ x ∈ Finset.Icc 1 Y, x = Y ! := by
      rw [← Finset.Ico_add_one_right_eq_Icc]; exact Finset.prod_Ico_id_eq_factorial Y
    rw [hset, Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h),
        Finset.prod_mul_distrib, Finset.prod_const, hfacY, Nat.card_Icc, Nat.add_sub_cancel]
  unfold Gcop
  rw [← hfac, ← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (Y*p)) (fun k => p ∣ k), hmul]

def BG2 (p r C K : ℕ) : ℕ := ∏ j ∈ (Finset.Icc 1 (K*p^r)).filter (fun j => ¬ p ∣ j), (C*p^r + 2*j)

theorem bg2_succ (p r C K : ℕ) (hp : 0 < p) (hr : 1 ≤ r) :
    BG2 p r C (K+1)
      = BG2 p r C K * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), ((C+2*K)*p^r + 2*e) := by
  unfold BG2
  set q := p^r with hq
  have hexp : (K+1)*q = K*q + q := by ring
  have hqdvd : p ∣ K*q := by rw [hq]; exact (dvd_pow_self p (by omega : r ≠ 0)).mul_left K
  have hsplit : (Finset.Icc 1 ((K+1)*q)).filter (fun j => ¬ p ∣ j)
      = ((Finset.Icc 1 (K*q)).filter (fun j => ¬ p ∣ j))
        ∪ ((Finset.Icc (K*q+1) ((K+1)*q)).filter (fun j => ¬ p ∣ j)) := by
    rw [← Finset.filter_union]; congr 1
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint ((Finset.Icc 1 (K*q)).filter (fun j => ¬ p ∣ j))
        ((Finset.Icc (K*q+1) ((K+1)*q)).filter (fun j => ¬ p ∣ j)) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  rw [hsplit, Finset.prod_union hdisj]
  congr 1
  rw [show (Finset.Icc (K*q+1) ((K+1)*q)).filter (fun j => ¬ p ∣ j)
        = ((Finset.Icc 1 q).filter (fun e => ¬ p ∣ e)).image (fun e => K*q + e) from ?_]
  · rw [Finset.prod_image (by intro a _ b _ h; exact Nat.add_left_cancel h)]
    apply Finset.prod_congr rfl
    intro e _; ring
  · ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hpx⟩
      refine ⟨x - K*q, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      intro hd; apply hpx
      have := Nat.dvd_add hqdvd hd
      rwa [Nat.add_sub_cancel' (by omega : K*q ≤ x)] at this
    · rintro ⟨e, ⟨⟨he1, he2⟩, hpe⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro hd; apply hpe
      have := Nat.dvd_sub hd hqdvd
      rwa [Nat.add_sub_cancel_left] at this

theorem BG2_cong (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (C K : ℕ) :
    (BG2 p r C K : ℤ)
      ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))^K
        [ZMOD ((p^r:ℕ):ℤ)^3] := by
  have hpr1 : 1 ≤ p^r := Nat.one_le_pow _ _ hp.pos
  have hpq : p ∣ p^r := dvd_pow_self p (by omega)
  have hqf : (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e)
           = (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1,h2⟩, hpx⟩
      refine ⟨⟨h1, ?_⟩, hpx⟩
      rcases Nat.lt_or_ge x (p^r) with h|h
      · omega
      · exfalso; have hx : x = p^r := by omega
        rw [hx] at hpx; exact hpx hpq
    · rintro ⟨⟨h1,h2⟩, hpx⟩
      exact ⟨⟨h1, by omega⟩, hpx⟩
  induction K with
  | zero => simp [BG2]
  | succ K IH =>
      rw [bg2_succ p r C K hp.pos hr]
      have hcast : ((BG2 p r C K * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), ((C+2*K)*p^r + 2*e) : ℕ) : ℤ)
          = (BG2 p r C K:ℤ) * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), (((C+2*K)*p^r + 2*e : ℕ):ℤ) := by
        push_cast; ring
      rw [hcast]
      have hblock : (∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), (((C+2*K)*p^r + 2*e : ℕ):ℤ))
          ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ)) [ZMOD ((p^r:ℕ):ℤ)^3] := by
        rw [hqf]
        exact block_cong2 p r hp hp5 hr (C+2*K)
      calc (BG2 p r C K:ℤ) * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), (((C+2*K)*p^r + 2*e : ℕ):ℤ)
          ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))^K
            * (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ)) [ZMOD ((p^r:ℕ):ℤ)^3] :=
              Int.ModEq.mul IH hblock
        _ = (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))^(K+1) := by rw [pow_succ]

theorem card_U (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) :
    ((Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e)).card = p^r - p^(r-1) := by
  have hpr : p^r = p * p^(r-1) := by
    conv_lhs => rw [show r = (r-1)+1 from by omega]
    rw [pow_succ]; ring
  have hpr1 : 1 ≤ p^(r-1) := Nat.one_le_pow _ _ hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  have hcompl : (Finset.Icc 1 (p^r-1)).filter (fun e => p ∣ e)
      = (Finset.Icc 1 (p^(r-1)-1)).image (fun k => p*k) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hj1, hj2⟩, k, rfl⟩
      have hk0 : k ≠ 0 := by rintro rfl; simp at hj1
      refine ⟨k, ⟨Nat.one_le_iff_ne_zero.mpr hk0, ?_⟩, rfl⟩
      have hlt : p*k < p*p^(r-1) := by omega
      have := Nat.lt_of_mul_lt_mul_left hlt
      omega
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hp.pos hk1, ?_⟩, dvd_mul_right p k⟩
      have hkle : p * k ≤ p * (p^(r-1)-1) := Nat.mul_le_mul_left p hk2
      have hprod : p * (p^(r-1)-1) + p = p^r := by
        rw [hpr]
        generalize p^(r-1) = s at hpr1 ⊢
        cases s with
        | zero => omega
        | succ t => simp [Nat.mul_succ]
      omega
  have hcardcompl : ((Finset.Icc 1 (p^r-1)).filter (fun e => p ∣ e)).card = p^(r-1) - 1 := by
    rw [hcompl, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp.pos h),
        Nat.card_Icc, Nat.add_sub_cancel]
  have htot := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.Icc 1 (p^r-1)) (p := fun e => p ∣ e)
  rw [hcardcompl, Nat.card_Icc, Nat.add_sub_cancel] at htot
  omega
theorem gcop_coprime (p X : ℕ) (hp : p.Prime) : Nat.Coprime (Gcop p X) p := by
  unfold Gcop
  apply Nat.Coprime.prod_left
  intro e he
  simp only [Finset.mem_filter] at he
  exact (hp.coprime_iff_not_dvd.mpr he.2).symm


/-! ## Gamma bridge for A364178 -/

lemma gamma_shift (x : ℝ) (hx : 0 < x) : ∀ k : ℕ,
    Real.Gamma (x + k) = Real.Gamma x * ∏ i ∈ Finset.range k, (x + i) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hxk : x + (k:ℝ) ≠ 0 := by
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      have : (0:ℝ) < x + (k:ℝ) := by linarith
      exact this.ne'
    rw [Finset.prod_range_succ]
    have hstep : Real.Gamma (x + (↑(k+1))) = (x + k) * Real.Gamma (x + k) := by
      rw [show x + (↑(k+1)) = (x + k) + 1 by push_cast; ring, Real.Gamma_add_one hxk]
    rw [hstep, ih]; ring

lemma hPQ178 (n : ℕ) :
    (2:ℝ)^n * ∏ i ∈ Finset.range n, ((n:ℝ)/2+1+(i:ℝ)) = (Pseq n : ℝ) := by
  have hcard : (2:ℝ)^n = ∏ i ∈ Finset.range n, (2:ℝ) := by
    rw [Finset.prod_const, Finset.card_range]
  have hcast : (Pseq n : ℝ) = ∏ i ∈ Finset.range n, ((n:ℝ)+2+2*(i:ℝ)) := by
    rw [Pseq]; push_cast
    rw [show Finset.Icc 1 n = Finset.Ico 1 (n+1) from by
          ext x; simp [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff],
        Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.prod_congr rfl; intro i _; push_cast; ring
  rw [hcard, ← Finset.prod_mul_distrib, hcast]
  apply Finset.prod_congr rfl; intro i _; ring

lemma val_eq (n : ℕ) :
    (Real.Gamma (10 * (↑n : ℝ) + 1) * Real.Gamma (3 * (↑n : ℝ) + 1) * Real.Gamma ((↑n : ℝ) / 2 + 1)) /
     (Real.Gamma (6 * (↑n : ℝ) + 1) * Real.Gamma (5 * (↑n : ℝ) + 1) * Real.Gamma (3 * (↑n : ℝ) / 2 + 1)
       * Real.Gamma (↑n + 1))
    = (aexact n : ℝ) := by
  have hx : (0:ℝ) < (n:ℝ)/2 + 1 := by positivity
  have hG : (0:ℝ) < Real.Gamma ((n:ℝ)/2 + 1) := Real.Gamma_pos_of_pos hx
  have hf6 : (0:ℝ) < ((6*n)! : ℝ) := by exact_mod_cast (6*n).factorial_pos
  have hf5 : (0:ℝ) < ((5*n)! : ℝ) := by exact_mod_cast (5*n).factorial_pos
  have hf1 : (0:ℝ) < ((n)! : ℝ) := by exact_mod_cast (n).factorial_pos
  have hPpos : (0:ℝ) < ∏ i ∈ Finset.range n, ((n:ℝ)/2+1+(i:ℝ)) :=
    Finset.prod_pos (fun i _ => by positivity)
  have hshift : Real.Gamma (3 * (n:ℝ) / 2 + 1)
      = Real.Gamma ((n:ℝ)/2+1) * ∏ i ∈ Finset.range n, ((n:ℝ)/2+1+(i:ℝ)) := by
    have h := gamma_shift ((n:ℝ)/2+1) hx n
    rw [show ((n:ℝ)/2+1)+(n:ℝ) = 3*(n:ℝ)/2+1 by ring] at h
    exact h
  have hden0 : ((6*n)! * (5*n)! * n ! * Pseq n : ℕ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _)) (Pseq_ne n)
  have haex : (aexact n : ℝ) = ↑(2^n * (10*n)! * (3*n)!) / ↑((6*n)! * (5*n)! * n ! * Pseq n) := by
    rw [eq_div_iff (by exact_mod_cast hden0)]
    have hspec := congrArg (fun t : ℕ => (t : ℝ)) (aexact_spec n)
    push_cast
    push_cast at hspec
    linear_combination hspec
  rw [show (10:ℝ)*(n:ℝ)+1 = ((10*n:ℕ):ℝ)+1 by push_cast; ring,
      show (3:ℝ)*(n:ℝ)+1 = ((3*n:ℕ):ℝ)+1 by push_cast; ring,
      show (6:ℝ)*(n:ℝ)+1 = ((6*n:ℕ):ℝ)+1 by push_cast; ring,
      show (5:ℝ)*(n:ℝ)+1 = ((5*n:ℕ):ℝ)+1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      hshift, haex]
  rw [div_eq_div_iff
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hf6.ne' hf5.ne') (mul_ne_zero hG.ne' hPpos.ne')) hf1.ne')
      (by exact_mod_cast hden0)]
  push_cast
  linear_combination (-(((10*n)! : ℝ) * ((3*n)! : ℝ) * Real.Gamma ((n:ℝ)/2 + 1)
    * ((6*n)! : ℝ) * ((5*n)! : ℝ) * ((n)! : ℝ))) * hPQ178 n

lemma a_eq (n : ℕ) : a n = aexact n := by
  show (round _).toNat = aexact n
  rw [val_eq n, round_natCast, Int.toNat_natCast]

/-! ## The supercongruence core for A364178 -/

/-- The `p`-free part of `Pseq (M*p)`. -/
def PG178 (p M : ℕ) : ℕ := ∏ k ∈ (Finset.Icc 1 (M*p)).filter (fun k => ¬ p ∣ k), (M*p + 2*k)

theorem P_split178 (p M : ℕ) (hp : 0 < p) :
    Pseq (M*p) = p^M * Pseq M * PG178 p M := by
  unfold Pseq PG178
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (M*p)) (fun k => p ∣ k)]
  have hA : (∏ k ∈ (Finset.Icc 1 (M*p)).filter (fun k => p ∣ k), (M*p+2*k))
      = p^M * ∏ k ∈ Finset.Icc 1 M, (M+2*k) := by
    have hset : (Finset.Icc 1 (M*p)).filter (fun k => p ∣ k) = (Finset.Icc 1 M).image (fun k => p*k) := by
      ext j
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hj1, hj2⟩, k, rfl⟩
        have hk0 : k ≠ 0 := by rintro rfl; simp at hj1
        have hkM : k ≤ M := Nat.le_of_mul_le_mul_left (by rw [mul_comm M p] at hj2; exact hj2) hp
        exact ⟨k, ⟨Nat.one_le_iff_ne_zero.mpr hk0, hkM⟩, rfl⟩
      · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
        exact ⟨⟨Nat.mul_pos hp hk1, by rw [mul_comm p k]; exact Nat.mul_le_mul_right p hk2⟩, dvd_mul_right p k⟩
    rw [hset, Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h)]
    rw [Finset.prod_congr rfl (fun k _ => show M*p + 2*(p*k) = p*(M+2*k) from by ring)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hA]

theorem pg178_coprime (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : Nat.Coprime (PG178 p M) p := by
  unfold PG178
  apply Nat.Coprime.prod_left
  intro j hj
  simp only [Finset.mem_filter] at hj
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hd
  apply hj.2
  have h5 : p ∣ M*p := ⟨M, by ring⟩
  have h2j : p ∣ 2*j := by
    have := Nat.dvd_sub hd h5; rwa [Nat.add_sub_cancel_left] at this
  rcases hp.dvd_mul.mp h2j with h|h
  · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  · exact h

theorem core178 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    (p : ℤ) ^ (3 * r) ∣ ((aexact (n * p ^ r) : ℕ) : ℤ) - ((aexact (n * p ^ (r - 1)) : ℕ) : ℤ) := by
  have hp0 : 0 < p := hp.pos
  set M := n * p ^ (r - 1) with hM
  have hNM : n * p ^ r = M * p := by
    rw [hM, mul_assoc, ← pow_succ, show (r - 1) + 1 = r from by omega]
  have hcoef : ∀ c : ℕ, c * M * p = (c * n) * p ^ r := by
    intro c; rw [mul_assoc, ← hNM]; ring
  rw [hNM]
  set A : ℤ := ((aexact (M*p) : ℕ) : ℤ) with hAdef
  set B : ℤ := ((aexact M : ℕ) : ℤ) with hBdef
  have hAi : A * (((6*(M*p))! * (5*(M*p))! * (M*p)! * Pseq (M*p) : ℕ):ℤ)
      = ((2^(M*p) * (10*(M*p))! * (3*(M*p))! : ℕ):ℤ) := by
    rw [hAdef, ← Nat.cast_mul, mul_comm, aexact_spec]
  have hBi : B * (((6*M)! * (5*M)! * M ! * Pseq M : ℕ):ℤ)
      = ((2^M * (10*M)! * (3*M)! : ℕ):ℤ) := by
    rw [hBdef, ← Nat.cast_mul, mul_comm, aexact_spec]
  set SL := PG178 p M * Gcop p (6*M*p) * Gcop p (5*M*p) * Gcop p (M*p) with hSL
  set SR := 2^(M*(p-1)) * Gcop p (10*M*p) * Gcop p (3*M*p) with hSR
  have e10 : (10*(M*p))! = p^(10*M) * (10*M)! * Gcop p (10*M*p) := by
    rw [show 10*(M*p) = (10*M)*p from by ring]; exact fact_split p (10*M) hp0
  have e3 : (3*(M*p))! = p^(3*M) * (3*M)! * Gcop p (3*M*p) := by
    rw [show 3*(M*p) = (3*M)*p from by ring]; exact fact_split p (3*M) hp0
  have e6 : (6*(M*p))! = p^(6*M) * (6*M)! * Gcop p (6*M*p) := by
    rw [show 6*(M*p) = (6*M)*p from by ring]; exact fact_split p (6*M) hp0
  have e5 : (5*(M*p))! = p^(5*M) * (5*M)! * Gcop p (5*M*p) := by
    rw [show 5*(M*p) = (5*M)*p from by ring]; exact fact_split p (5*M) hp0
  have e1 : (M*p)! = p^M * M ! * Gcop p (M*p) := fact_split p M hp0
  have eP : Pseq (M*p) = p^M * Pseq M * PG178 p M := P_split178 p M hp0
  have e2pow : (2:ℕ)^(M*p) = 2^M * 2^(M*(p-1)) := by
    rw [← pow_add]; congr 1
    conv_lhs => rw [show (p:ℕ) = (p-1)+1 from by omega]
    ring
  have hK : (2^(M*p) * (10*(M*p))! * (3*(M*p))!) * SL * ((6*M)! * (5*M)! * M ! * Pseq M)
      = (2^M * (10*M)! * (3*M)!) * SR * ((6*(M*p))! * (5*(M*p))! * (M*p)! * Pseq (M*p)) := by
    rw [e10, e3, e6, e5, e1, eP, e2pow, hSL, hSR]
    ring
  have hKz : ((2^(M*p) * (10*(M*p))! * (3*(M*p))! : ℕ):ℤ) * (SL:ℤ) * (((6*M)! * (5*M)! * M ! * Pseq M : ℕ):ℤ)
      = ((2^M * (10*M)! * (3*M)! : ℕ):ℤ) * (SR:ℤ) * (((6*(M*p))! * (5*(M*p))! * (M*p)! * Pseq (M*p) : ℕ):ℤ) := by
    exact_mod_cast hK
  rw [← hAi, ← hBi] at hKz
  have hDN0 : (((6*(M*p))! * (5*(M*p))! * (M*p)! * Pseq (M*p) : ℕ):ℤ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_ne_zero _)
      (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)) (Pseq_ne _)
  have hDM0 : (((6*M)! * (5*M)! * M ! * Pseq M : ℕ):ℤ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_ne_zero _)
      (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)) (Pseq_ne _)
  have hABSL : A * (SL:ℤ) = B * (SR:ℤ) := by
    have hprod : (A * (SL:ℤ)) * ((((6*(M*p))! * (5*(M*p))! * (M*p)! * Pseq (M*p) : ℕ):ℤ) * (((6*M)! * (5*M)! * M ! * Pseq M : ℕ):ℤ))
        = (B * (SR:ℤ)) * ((((6*(M*p))! * (5*(M*p))! * (M*p)! * Pseq (M*p) : ℕ):ℤ) * (((6*M)! * (5*M)! * M ! * Pseq M : ℕ):ℤ)) := by
      linear_combination hKz
    exact mul_right_cancel₀ (mul_ne_zero hDN0 hDM0) hprod
  have hgcong : ∀ c : ℕ, (Gcop p (c*M*p):ℤ) ≡ (Gcop p (p^r):ℤ)^(c*n) [ZMOD ((p^r:ℕ):ℤ)^3] := by
    intro c; rw [hcoef c]; exact core_G p r hp hp5 hr (c*n)
  have hg1 : (Gcop p (M*p):ℤ) ≡ (Gcop p (p^r):ℤ)^n [ZMOD ((p^r:ℕ):ℤ)^3] := by
    rw [← hNM]; exact core_G p r hp hp5 hr n
  have hPGeq : PG178 p M = BG2 p r n n := by
    unfold PG178 BG2; rw [hNM]
  have hPG : (PG178 p M:ℤ)
      ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))^n [ZMOD ((p^r:ℕ):ℤ)^3] := by
    rw [hPGeq]; exact BG2_cong p r hp hp5 hr n n
  have hSLcong : (SL:ℤ) ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))^n
      * (Gcop p (p^r):ℤ)^(6*n) * (Gcop p (p^r):ℤ)^(5*n) * (Gcop p (p^r):ℤ)^n [ZMOD ((p^r:ℕ):ℤ)^3] := by
    rw [hSL]; push_cast
    exact ((hPG.mul (hgcong 6)).mul (hgcong 5)).mul hg1
  have hSRcong : (SR:ℤ) ≡ (2:ℤ)^(M*(p-1)) * (Gcop p (p^r):ℤ)^(10*n) * (Gcop p (p^r):ℤ)^(3*n) [ZMOD ((p^r:ℕ):ℤ)^3] := by
    rw [hSR]; push_cast
    exact ((Int.ModEq.refl _).mul (hgcong 10)).mul (hgcong 3)
  have hpr1 : 1 ≤ p^r := Nat.one_le_pow _ _ hp.pos
  have hpq : p ∣ p^r := dvd_pow_self p (by omega)
  have hqf : (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e)
           = (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1,h2⟩, hpx⟩
      refine ⟨⟨h1, ?_⟩, hpx⟩
      rcases Nat.lt_or_ge x (p^r) with h|h
      · omega
      · exfalso; have hx : x = p^r := by omega
        rw [hx] at hpx; exact hpx hpq
    · rintro ⟨⟨h1,h2⟩, hpx⟩
      exact ⟨⟨h1, by omega⟩, hpx⟩
  have hGU : (Gcop p (p^r):ℤ) = ∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((e:ℕ):ℤ) := by
    unfold Gcop; rw [hqf]; push_cast; rfl
  have h2eU : (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))
      = 2^(((Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e)).card) * (Gcop p (p^r):ℤ) := by
    rw [hGU, Finset.prod_congr rfl (fun e _ => by push_cast; ring :
        ∀ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ) = 2 * (e:ℤ)),
        Finset.prod_mul_distrib, Finset.prod_const]
  have hcardcard := card_U p r hp hr
  have hcardeq : n*(p^r - p^(r-1)) = M*(p-1) := by
    rw [hM]
    have hpr : p^r = p^(r-1)*p := by rw [← pow_succ]; congr 1; omega
    rw [hpr]
    generalize p^(r-1) = s
    have hss : s * p - s = s * (p-1) := by
      cases p with
      | zero => simp
      | succ t => rw [Nat.mul_succ, Nat.add_sub_cancel, Nat.succ_sub_one]
    rw [hss]; ring
  have hEQ : (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((2*e:ℕ):ℤ))^n
        * (Gcop p (p^r):ℤ)^(6*n) * (Gcop p (p^r):ℤ)^(5*n) * (Gcop p (p^r):ℤ)^n
      = (2:ℤ)^(M*(p-1)) * (Gcop p (p^r):ℤ)^(10*n) * (Gcop p (p^r):ℤ)^(3*n) := by
    rw [h2eU, mul_pow, ← pow_mul, hcardcard,
        show (p^r - p^(r-1))*n = M*(p-1) from by rw [mul_comm]; exact hcardeq]
    ring
  have hSLfinal : (SL:ℤ) ≡ (SR:ℤ) [ZMOD ((p^r:ℕ):ℤ)^3] :=
    (hSLcong.trans (hEQ ▸ Int.ModEq.refl _)).trans hSRcong.symm
  have hmod : ((p^r:ℕ):ℤ)^3 = (p:ℤ)^(3*r) := by push_cast; rw [← pow_mul, Nat.mul_comm]
  have hdvd1 : (p:ℤ)^(3*r) ∣ ((SR:ℤ) - (SL:ℤ)) := by
    have := Int.ModEq.dvd hSLfinal
    rwa [hmod] at this
  have hmul : (A - B) * (SL:ℤ) = B * ((SR:ℤ) - (SL:ℤ)) := by
    linear_combination hABSL
  have hdvd2 : (p:ℤ)^(3*r) ∣ (A - B) * (SL:ℤ) := by
    rw [hmul]; exact Dvd.dvd.mul_left hdvd1 _
  have hcopSL : Nat.Coprime SL p := by
    rw [hSL]
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left
      (pg178_coprime p M hp hp5) (gcop_coprime p (6*M*p) hp)) (gcop_coprime p (5*M*p) hp))
      (gcop_coprime p (M*p) hp)
  have hcop : IsCoprime ((p:ℤ)^(3*r)) (SL:ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hcopSL).symm.pow_left
  exact hcop.dvd_of_dvd_mul_right hdvd2

/-- A364178 Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r. -/
theorem oeis_364178_conjecture_0 (p n r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] :=
by
  rw [a_eq, a_eq, Nat.modEq_iff_dvd, dvd_sub_comm]
  push_cast
  exact core178 p hp h5 n r hn hr

#print axioms oeis_364178_conjecture_0
