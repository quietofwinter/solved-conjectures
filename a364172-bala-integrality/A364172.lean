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
Integrality and the supercongruence conjecture for OEIS A364172.
Jason Benham, November 19, 2026.

MAIN RESULTS

  1. Integrality. For every n, the real number

         (6n)! Γ(n/3 + 1) / ((3n)! (2n)! Γ(4n/3 + 1))

     equals the natural number `aexact n` (lemma `val_eq`). This rests on
     lemma `integrality`, which shows that (3n)! (2n)! P(n) divides
     3^n (6n)!, where P(n) = ∏_{k=1}^n (n + 3k) is `Qseq n`.

  2. Supercongruence. `oeis_364172_conjecture_0`, the last theorem in this
     file: for every prime p >= 5 and all positive integers n and r,

         a(n p^r) ≡ a(n p^(r-1))  (mod p^(3r)),

     where a(n) = (6n)! (n/3)! / ((3n)! (2n)! (4n/3)!), with x! := Γ(x+1),
     is OEIS A364172. The supercongruence was conjectured by Peter Bala in
     the OEIS entry https://oeis.org/A364172, which also says that the
     sequence is only conjecturally an integer sequence. A written proof is in
     `A364172.pdf`, in the same folder as this file.

WHERE THE FORMAL STATEMENT COMES FROM

  Formal Conjectures (https://github.com/google-deepmind/formal-conjectures)
  has no statement for A364172. The definition `a` and the statement of
  `oeis_364172_conjecture_0` were written by us, modelled word for word on
  the Formal Conjectures statement for the twin sequence A364175,

      FormalConjectures/OEIS/Auto/364175_1518df7a.lean

  at commit 67338a1 (branch `auto_oeis`), which carries the Apache 2.0 notice
  above. The only changes are the sequence number and the gamma arguments
  (1/3 and 4/3 in place of 2/3 and 5/3).

A NOTE ON THE DOCSTRING OF `a`

  The docstring says, following the OEIS entry and the A364175 model, that
  the sequence is only conjecturally an integer sequence. This file proves
  that it is an integer sequence (lemmas `integrality` and `val_eq`).

EARLIER WORK REUSED IN THIS FILE

  The proof is adapted from the verified Lean proof for A364175
  (`A364175.lean` in https://github.com/quietofwinter/solved-conjectures,
  folder `a364175-bala-supercongruence`), with the product n + 3k in place
  of 2n + 3k. The provenance of its parts is as described in the header of
  that file:

  1. The integrality argument and the gamma-function reduction (`div_add_div_le`
     through `aexact_spec`, and `gamma_shift` through `a_eq`) are adapted from
     the submission by Claude Opus 4.8 for the A364175 conjecture in Epoch AI's
     OEIS Open run `oeis-full-50usd-ant-j0j0g4uzligm1k41`,
     `oeis_364175_conjecture_0/Submission/Spec.lean`, published at
     https://github.com/epoch-research/LeanOpenProblems-results (see
     T. Adamczewski, "OEIS Open: How many conjectures can language models turn
     into theorems?", arXiv:2608.11941). That submission was rejected by the
     verifier because it still contained `sorry`.

  2. The block-product lemmas (`sum_units_sq_eq_zero` through `gcop_coprime`)
     come from that run's accepted proof for the sibling sequence A364176,
     `oeis_364176_conjecture_0/Submission/Spec.lean`.

  3. The step-3 shifted-block lemmas (`block_cong3`, `BG3`, `bg3_succ`,
     `BG3_cong`) and the splitting lemmas (`QG`, `Q_split`, `qg_coprime`,
     `Qseq_ne'`) were new in `A364175.lean`; here `QG` uses M p + 3k.

  New in this file: `fl_scale`, `fl_lt`, `fl_E`, `core172` and the final
  theorem. Adapted from `A364175.lean` to the product n + 3k and to 4n/3:
  `a`, `landau_floor`, `bij_k_x`, `mult_count_eq`, `term_count_bound`,
  `Qseq`, `Qseq_ne`, `small_bound`, `vq_Qseq_swap`, `vq_prime_bound`,
  `landau_floor3`, `Qseq_three`, `vq3_B`, `vq3_bound`, `QG`, `Q_split`,
  `qg_coprime`, `hPQ` and `val_eq`. All other lemmas are unchanged from
  `A364175.lean`.

HOW TO CHECK IT

  Lean v4.27.0, against Formal Conjectures at commit 67338a1:

      git clone https://github.com/google-deepmind/formal-conjectures
      cd formal-conjectures
      git checkout 67338a1
      lake exe cache get
      lake env lean /path/to/A364172.lean

  The last command should finish without errors. The proof contains no `sorry`
  and depends only on the standard axioms `propext`, `Classical.choice` and
  `Quot.sound`.

The proof was developed with the assistance of Claude (Anthropic).
-/

import FormalConjectures.Util.ProblemImports

open Real Nat Int Finset

/--
A364172: $a(n) = \frac{(6n)! (n/3)!}{(3n)! (2n)! (4n/3)!}$.
The fractional factorial $x!$ is defined as $\Gamma(x+1)$.
This sequence is only conjecturally an integer sequence. We round the real-valued result to obtain a natural number.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (1 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (4 / 3 * n_r + 1))
  (round val_R).toNat

lemma div_add_div_le (a b m : ℕ) : a/m + b/m ≤ (a+b)/m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · rw [Nat.le_div_iff_mul_le h, add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self a m) (Nat.div_mul_le_self b m)

lemma div_add_le (a b m : ℕ) (hm : 0 < m) : (a+b)/m ≤ a/m + b/m + 1 := by
  have ha := Nat.div_add_mod a m; have hb := Nat.div_add_mod b m
  have ha' := Nat.mod_lt a hm; have hb' := Nat.mod_lt b hm
  have : (a+b) < (a/m + b/m + 2) * m := by nlinarith [ha, hb, ha', hb']
  have := (Nat.div_lt_iff_lt_mul hm).2 this; omega

lemma fl_scale (s m k e : ℕ) (he : 0 < e) : k*s/m = (k*e*s/m)/e := by
  rw [Nat.div_div_eq_div_mul, show k*e*s = e*(k*s) by ring, mul_comm m e,
      Nat.mul_div_mul_left _ _ he]

lemma fl_lt (s m k : ℕ) (hm : 0 < m) (hs : s < m) (hk : 0 < k) : k*s/m < k :=
  (Nat.div_lt_iff_lt_mul hm).2 (by nlinarith)

lemma fl_E (m q s k : ℕ) (hm : 0 < m) : k*(m*q+s)/m = k*q + (k*s)/m := by
  have h : k*(m*q+s) = m*(k*q) + k*s := by ring
  rw [h, Nat.mul_add_div hm]

lemma landau_floor (n m : ℕ) (hm : 0 < m) :
    (4*n/m - n/m + 2)/3 ≤ 6*n/m - 3*n/m - 2*n/m := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < m ∧ n = m*q+s :=
    ⟨n/m, n%m, Nat.mod_lt _ hm, by rw [Nat.div_add_mod]⟩
  have h1 : (m*q+s)/m = q := by
    have := fl_E m q s 1 hm; simp only [one_mul] at this; rw [this, Nat.div_eq_of_lt hs]; ring
  rw [h1, fl_E m q s 4 hm, fl_E m q s 6 hm, fl_E m q s 3 hm, fl_E m q s 2 hm]
  have hT := fl_lt s m 12 hm hs (by norm_num)
  rw [fl_scale s m 4 3 (by norm_num), fl_scale s m 6 2 (by norm_num),
      fl_scale s m 3 4 (by norm_num), fl_scale s m 2 6 (by norm_num)]
  norm_num only
  generalize 12*s/m = T at hT ⊢
  interval_cases T <;> omega

lemma residue_count_le3 (a b c : ℕ) :
    #{x ∈ Ioc a b | x % 3 = c} ≤ (b - a + 2) / 3 := by
  rw [← Finset.card_range ((b - a + 2) / 3)]
  apply Finset.card_le_card_of_injOn (fun x => (x - 1 - a) / 3)
  · intro x hx; simp only [Finset.mem_coe, mem_filter, mem_Ioc, mem_range] at *; omega
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_filter, mem_Ioc] at hx hy
    simp only at hxy; omega

lemma bij_k_x (n m : ℕ) :
    #{k ∈ Icc 1 n | m ∣ n+3*k}
      = #{x ∈ Ioc n (4*n) | m ∣ x ∧ x % 3 = n % 3} := by
  apply Finset.card_bij (fun k _ => n+3*k)
  · intro k hk; rw [mem_filter, mem_Icc] at hk; rw [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, hk.2, by omega⟩
  · intro a ha b hb h; rw [mem_filter, mem_Icc] at ha hb; omega
  · intro x hx; rw [mem_filter, mem_Ioc] at hx
    refine ⟨(x - n)/3, ?_, by omega⟩
    rw [mem_filter, mem_Icc]; exact ⟨by omega, by
      have : n+3*((x-n)/3) = x := by omega
      rw [this]; exact hx.2.1⟩

lemma mult_count_eq (n m c : ℕ) (hm : 0 < m) :
    #{x ∈ Ioc n (4*n) | m ∣ x ∧ x % 3 = c}
      = #{t ∈ Ioc (n/m) (4*n/m) | (m*t) % 3 = c} := by
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
    have l2 : t*m ≤ 4*n := (Nat.le_div_iff_mul_le hm).1 h2
    exact ⟨⟨by nlinarith [l1], by nlinarith [l2]⟩, ⟨t, rfl⟩, h3⟩

lemma count_mt_le (A B m c : ℕ) (hm3 : ¬ 3 ∣ m) (hc : c < 3) :
    #{t ∈ Ioc A B | (m*t) % 3 = c} ≤ (B - A + 2)/3 := by
  have hmod : m % 3 = 1 ∨ m % 3 = 2 := by omega
  have key : ∃ r, {t ∈ Ioc A B | (m*t) % 3 = c} = {t ∈ Ioc A B | t % 3 = r} := by
    rcases hmod with h | h
    · exact ⟨c, Finset.filter_congr (fun t _ => by rw [Nat.mul_mod, h]; omega)⟩
    · refine ⟨(2*c) % 3, Finset.filter_congr (fun t _ => ?_)⟩
      rw [Nat.mul_mod, h]; have : t % 3 < 3 := Nat.mod_lt _ (by norm_num); omega
  obtain ⟨r, hr⟩ := key; rw [hr]; exact residue_count_le3 A B r

lemma term_count_bound (n m : ℕ) (hm : 0 < m) (hm3 : ¬ 3 ∣ m) :
    #{k ∈ Icc 1 n | m ∣ n+3*k} ≤ 6*n/m - 3*n/m - 2*n/m := by
  rw [bij_k_x n m, mult_count_eq n m (n%3) hm]
  refine le_trans (count_mt_le _ _ m (n%3) hm3 (Nat.mod_lt _ (by norm_num))) ?_
  exact landau_floor n m hm

def Qseq (n : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 n, (n+3*k)

lemma Qseq_ne (n : ℕ) : Qseq n ≠ 0 := by
  unfold Qseq; apply Finset.prod_ne_zero_iff.2; intro k hk; rw [mem_Icc] at hk; omega

-- bound: for k in [1,n], n+3k < q^(6n+1) when q ≥ 2
lemma small_bound (n q k : ℕ) (hq : 2 ≤ q) (hk : k ∈ Icc 1 n) : n+3*k < q^(6*n+1) := by
  rw [mem_Icc] at hk
  have h1 : 5*n < 2^(5*n+1) := by
    have : 5*n < 2^(5*n) := Nat.lt_two_pow_self; calc 5*n < 2^(5*n) := this
      _ ≤ 2^(5*n+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2^(6*n+1) ≤ q^(6*n+1) := Nat.pow_le_pow_left hq _
  have h3 : (2:ℕ)^(5*n+1) ≤ 2^(6*n+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma vq_Qseq_swap (n q : ℕ) (hq : q.Prime) :
    (Qseq n).factorization q
      = ∑ i ∈ Ico 1 (6*n+1), #{k ∈ Icc 1 n | q^i ∣ n+3*k} := by
  have hq2 : 2 ≤ q := hq.two_le
  unfold Qseq
  rw [Nat.factorization_prod (by intro k hk; rw [mem_Icc] at hk; omega)]
  simp only [Finsupp.finset_sum_apply]
  have step : ∀ k ∈ Icc 1 n, (n+3*k).factorization q
      = ∑ i ∈ Ico 1 (6*n+1), (if q^i ∣ n+3*k then 1 else 0) := by
    intro k hk
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hq (by rw [mem_Icc] at hk; omega)
          (small_bound n q k hq2 hk)]
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.card_filter]

lemma log_bound (q n : ℕ) (hq : 2 ≤ q) (K : ℕ) (hK : K ≤ 6*n) : Nat.log q K < 6*n+1 := by
  rcases Nat.eq_zero_or_pos K with h | h
  · simp [h]
  · have hb : K < q^(6*n+1) := by
      have h2 : 6*n < 2^(6*n) := Nat.lt_two_pow_self
      calc K ≤ 6*n := hK
        _ < 2^(6*n) := h2
        _ ≤ q^(6*n) := Nat.pow_le_pow_left hq _
        _ ≤ q^(6*n+1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.log_lt_of_lt_pow (by omega) hb

lemma vq_prime_bound (n q : ℕ) (hq : q.Prime) (hq3 : q ≠ 3) :
    (3*n)!.factorization q + (2*n)!.factorization q + (Qseq n).factorization q
      ≤ (6*n)!.factorization q := by
  have hq2 := hq.two_le
  have h3p : Nat.Prime 3 := by norm_num
  have h3nd : ∀ i, ¬ (3 ∣ q^i) := by
    intro i hd
    have hdq : (3:ℕ) ∣ q := h3p.dvd_of_dvd_pow hd
    have : (3:ℕ) = q := (Nat.prime_dvd_prime_iff_eq h3p hq).1 hdq
    omega
  rw [Nat.factorization_factorial hq (log_bound q n hq2 (6*n) (by omega)),
      Nat.factorization_factorial hq (log_bound q n hq2 (3*n) (by omega)),
      Nat.factorization_factorial hq (log_bound q n hq2 (2*n) (by omega)),
      vq_Qseq_swap n q hq]
  have key : ∀ i ∈ Ico 1 (6*n+1),
      #{k ∈ Icc 1 n | q^i ∣ n+3*k} ≤ 6*n/q^i - 3*n/q^i - 2*n/q^i := by
    intro i _
    exact term_count_bound n (q^i) (pow_pos hq.pos i) (h3nd i)
  have hSQ : ∑ i ∈ Ico 1 (6*n+1), #{k ∈ Icc 1 n | q^i ∣ n+3*k}
      ≤ ∑ i ∈ Ico 1 (6*n+1), (6*n/q^i - 3*n/q^i - 2*n/q^i) := Finset.sum_le_sum key
  have heq : ∑ i ∈ Ico 1 (6*n+1), 3*n/q^i + ∑ i ∈ Ico 1 (6*n+1), 2*n/q^i
      + ∑ i ∈ Ico 1 (6*n+1), (6*n/q^i - 3*n/q^i - 2*n/q^i)
      = ∑ i ∈ Ico 1 (6*n+1), 6*n/q^i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    have hle : 3*n/q^i + 2*n/q^i ≤ 6*n/q^i := by
      have := div_add_div_le (3*n) (2*n) (q^i)
      have h56 : (5*n)/q^i ≤ (6*n)/q^i := Nat.div_le_div_right (by omega)
      rw [show 3*n+2*n=5*n by ring] at this; omega
    omega
  omega

lemma landau_floor3 (a m : ℕ) (hm : 0 < m) :
    9*a/m + 6*a/m + 4*a/m ≤ 18*a/m + a/m := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < m ∧ a = m*q+s :=
    ⟨a/m, a%m, Nat.mod_lt _ hm, by rw [Nat.div_add_mod]⟩
  have h1 : (m*q+s)/m = q := by
    have := fl_E m q s 1 hm; simp only [one_mul] at this; rw [this, Nat.div_eq_of_lt hs]; ring
  rw [h1, fl_E m q s 9 hm, fl_E m q s 6 hm, fl_E m q s 4 hm, fl_E m q s 18 hm]
  have hT := fl_lt s m 36 hm hs (by norm_num)
  rw [fl_scale s m 9 4 (by norm_num), fl_scale s m 6 6 (by norm_num),
      fl_scale s m 4 9 (by norm_num), fl_scale s m 18 2 (by norm_num)]
  norm_num only
  generalize 36*s/m = T at hT ⊢
  interval_cases T <;> omega

lemma prod_Icc_ascFactorial (a K : ℕ) :
    ∏ k ∈ Finset.Icc 1 K, (a + k) = (a+1).ascFactorial K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ K+1), ih, Nat.ascFactorial_succ]
    ring

lemma Qseq_three (n : ℕ) : Qseq (3*n) * n ! = 3^(3*n) * (4*n)! := by
  have key : Qseq (3*n) = 3^(3*n) * (n+1).ascFactorial (3*n) := by
    unfold Qseq
    have h1 : ∀ k ∈ Finset.Icc 1 (3*n), 3*n+3*k = 3*(n+k) := by intro k _; ring
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const,
        prod_Icc_ascFactorial, Nat.card_Icc, show (3*n+1)-1 = 3*n from by omega]
  rw [key, mul_assoc, mul_comm ((n+1).ascFactorial (3*n)) (n !),
      Nat.factorial_mul_ascFactorial]
  congr 2
  omega

lemma vq3_B (n : ℕ) :
    (9*n)!.factorization 3 + (6*n)!.factorization 3 + (4*n)!.factorization 3
      ≤ (18*n)!.factorization 3 + (n !).factorization 3 := by
  have h3 : Nat.Prime 3 := by norm_num
  have L : ∀ m : ℕ, m ≤ 18*n → Nat.log 3 m < 18*n+1 := by
    intro m hm; exact lt_of_le_of_lt (Nat.log_le_self 3 m) (by omega)
  rw [Nat.factorization_factorial h3 (L (9*n) (by omega)),
      Nat.factorization_factorial h3 (L (6*n) (by omega)),
      Nat.factorization_factorial h3 (L (4*n) (by omega)),
      Nat.factorization_factorial h3 (L (18*n) (by omega)),
      Nat.factorization_factorial h3 (L n (by omega))]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact landau_floor3 n (3^i) (pow_pos (by norm_num) i)

lemma vq3_bound (n : ℕ) :
    (3*n)!.factorization 3 + (2*n)!.factorization 3 + (Qseq n).factorization 3
      ≤ n + (6*n)!.factorization 3 := by
  have h3 : Nat.Prime 3 := by norm_num
  rcases Nat.eq_zero_or_pos (n % 3) with hmod | hmod
  · -- 3 ∣ n
    obtain ⟨n', rfl⟩ : ∃ n', n = 3*n' := ⟨n/3, by omega⟩
    -- Qseq (3n') * n'! = 3^(3n') * (4n')!
    have hQ := Qseq_three n'
    have hQne : Qseq (3*n') ≠ 0 := Qseq_ne _
    have hfac2 : (n' ! : ℕ) ≠ 0 := Nat.factorial_ne_zero _
    have hfac5 : ((4*n')! : ℕ) ≠ 0 := Nat.factorial_ne_zero _
    -- take factorization 3 of both sides
    have hval : (Qseq (3*n')).factorization 3 + (n' !).factorization 3
        = 3*n' + (4*n')!.factorization 3 := by
      have := congrArg (fun t => t.factorization 3) hQ
      simp only at this
      rw [Nat.factorization_mul hQne hfac2, Nat.factorization_mul (by positivity) hfac5,
          Nat.factorization_pow] at this
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at this
      rw [Nat.Prime.factorization_self h3] at this
      omega
    have hB := vq3_B n'
    -- goal in terms of 3*n'
    -- (3*(3n'))! = (9n')!, (2*(3n'))! = (6n')!, (6*(3n'))!=(18n')!
    have e9 : 3*(3*n') = 9*n' := by ring
    have e6 : 2*(3*n') = 6*n' := by ring
    have e18 : 6*(3*n') = 18*n' := by ring
    rw [e9, e6, e18]
    omega
  · -- 3 ∤ n : v3(Qseq n) = 0
    have hnd : ¬ (3 ∣ n) := by omega
    have hQ0 : (Qseq n).factorization 3 = 0 := by
      unfold Qseq
      rw [Nat.factorization_prod (fun k hk => by
            simp only [Finset.mem_Icc] at hk; omega), Finsupp.finset_sum_apply]
      apply Finset.sum_eq_zero
      intro k hk
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      omega
    -- (3n)!(2n)! divides (6n)! via multinomial
    have hdvd : (3*n)! * (2*n)! ∣ (6*n)! := by
      have h1 : (3*n)! * (2*n)! ∣ (3*n+2*n)! := Nat.factorial_mul_factorial_dvd_factorial_add _ _
      rw [show 3*n+2*n = 5*n from by ring] at h1
      exact h1.trans (Nat.factorial_dvd_factorial (by omega))
    have hle : (3*n)!.factorization 3 + (2*n)!.factorization 3 ≤ (6*n)!.factorization 3 := by
      have h6 : ((6*n)! : ℕ) ≠ 0 := Nat.factorial_ne_zero _
      have := (Nat.factorization_le_iff_dvd (by positivity) h6).2 hdvd 3
      rwa [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
          Finsupp.add_apply] at this
    omega

lemma integrality (n : ℕ) : (3*n)! * (2*n)! * Qseq n ∣ 3^n * (6*n)! := by
  have hL : ((3*n)! * (2*n)! * Qseq n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) (Qseq_ne n)
  have hR : (3^n * (6*n)!) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.factorial_ne_zero _)
  apply (Nat.factorization_le_iff_dvd hL hR).mp
  rw [Finsupp.le_def]
  intro q
  by_cases hq : q.Prime
  · rw [Nat.factorization_mul (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) (Qseq_ne n),
        Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
        Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (Nat.factorial_ne_zero _),
        Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hq3 : q = 3
    · subst hq3
      rw [Nat.Prime.factorization_self (by norm_num)]
      have := vq3_bound n
      omega
    · have h30 : (3:ℕ).factorization q = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hd
        exact hq3 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 hd)
      have := vq_prime_bound n q hq hq3
      rw [h30]; omega
  · rw [Nat.factorization_eq_zero_of_non_prime _ hq]
    exact Nat.zero_le _

def aexact (n : ℕ) : ℕ := (3^n * (6*n)!) / ((3*n)! * (2*n)! * Qseq n)

lemma aexact_spec (n : ℕ) : ((3*n)! * (2*n)! * Qseq n) * aexact n = 3^n * (6*n)! :=
  Nat.mul_div_cancel' (integrality n)
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


/-! ## Step-3 shifted blocks (first introduced in the A364175 proof; QG adapted here) -/

theorem block_cong3 (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (c : ℕ) :
    (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((c*p^r + 3*e : ℕ) : ℤ))
      ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((3*e:ℕ) : ℤ)) [ZMOD ((p^r : ℕ) : ℤ)^3] := by
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
  set b : ℕ → ℤ := fun e => (9:ℤ) * ((e:ℤ) * ((p^r:ℤ) - (e:ℤ))) with hbdef
  set δ : ℤ := (c:ℤ) * ((c:ℤ)+3) * (p^r:ℤ)^2 with hδdef
  have hLHS := prod_pair (p^r) hodd (fun e => ¬ p ∣ e) hP (fun e => ((c*p^r+3*e:ℕ):ℤ))
  have hRHS := prod_pair (p^r) hodd (fun e => ¬ p ∣ e) hP (fun e => ((3*e:ℕ):ℤ))
  rw [hLHS, hRHS]
  have hbe : ∀ e ∈ Lf, ((c*p^r+3*e:ℕ):ℤ) * ((c*p^r+3*(p^r-e):ℕ):ℤ) = b e + δ := by
    intro e he
    simp only [hLf, Finset.mem_filter, Finset.mem_Icc] at he
    have hle : e ≤ p^r := by omega
    rw [hbdef, hδdef]; push_cast [Nat.cast_sub hle]; ring
  have hbe2 : ∀ e ∈ Lf, ((3*e:ℕ):ℤ) * ((3*(p^r-e):ℕ):ℤ) = b e := by
    intro e he
    simp only [hLf, Finset.mem_filter, Finset.mem_Icc] at he
    have hle : e ≤ p^r := by omega
    rw [hbdef]; push_cast [Nat.cast_sub hle]; ring
  rw [Finset.prod_congr rfl hbe, Finset.prod_congr rfl hbe2]
  have hpad := prod_add_delta Lf b δ
  have hq3δ2 : ((p^r:ℤ))^3 ∣ δ^2 := ⟨(c:ℤ)^2*((c:ℤ)+3)^2*(p^r:ℤ), by rw [hδdef]; ring⟩
  have h1 := hpad.of_dvd hq3δ2
  have hunit : ∀ e' ∈ Lf, IsUnit ((e':ZMod (p^r))) := by
    intro e' he'
    simp only [hLf, Finset.mem_filter] at he'
    rw [ZMod.isUnit_iff_coprime]; exact (coprime_iff_not_dvd p r hp hp5 hr e').mpr he'.2
  have h9unit : IsUnit (9 : ZMod (p^r)) := by
    have := (three_unit p r hp hp5 hr).pow 2
    rwa [show (3:ZMod (p^r))^2 = 9 by ring] at this
  have hbcast : ∀ e', ((b e' : ℤ) : ZMod (p^r)) = -((9:ZMod (p^r)) * (((e':ℕ):ZMod (p^r)))^2) := by
    intro e'; rw [hbdef]; push_cast
    rw [show ((p:ZMod (p^r)))^r = 0 by rw [← Nat.cast_pow, ZMod.natCast_self]]; ring
  have hDcast : ((∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e' : ℤ) : ZMod (p^r)) = 0 := by
    push_cast
    simp_rw [hbcast]
    have key : ∀ e ∈ Lf, ∏ e' ∈ Lf.erase e, (-((9:ZMod (p^r)) * (((e':ℕ):ZMod (p^r)))^2))
        = (∏ e' ∈ Lf, (-((9:ZMod (p^r)) * (((e':ℕ):ZMod (p^r)))^2)))
          * (-((9:ZMod (p^r)) * (((e:ℕ):ZMod (p^r)))^2))⁻¹ := by
      intro e he
      rw [zmod_leave_one Lf (fun e' => -((9:ZMod (p^r)) * (((e':ℕ):ZMod (p^r)))^2)) e he
          ((h9unit.mul ((hunit e he).pow 2)).neg)]
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
    have hz : ∑ e ∈ Lf, (-((9:ZMod (p^r)) * (((e:ℕ):ZMod (p^r)))^2))⁻¹ = 0 := by
      have heq : ∀ e ∈ Lf, (-((9:ZMod (p^r)) * (((e:ℕ):ZMod (p^r)))^2))⁻¹
          = (-((9:ZMod (p^r))⁻¹)) * ((((e:ℕ):ZMod (p^r)))⁻¹)^2 := by
        intro e he
        rw [zmod_neg_inv _ (h9unit.mul ((hunit e he).pow 2)),
            zmod_mul_inv _ _ h9unit ((hunit e he).pow 2), ← zmod_inv_sq _ (hunit e he)]
        ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum, half_W2 p r hp hp5 hr, mul_zero]
    rw [hz, mul_zero]
  have hD : (p^r:ℤ) ∣ (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^r)).mp hDcast
    exact_mod_cast this
  have hδD : ((p^r:ℤ))^3 ∣ δ * (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') := by
    obtain ⟨D', hD'⟩ := hD
    exact ⟨(c:ℤ)*((c:ℤ)+3)*D', by rw [hδdef, hD']; ring⟩
  calc (∏ e ∈ Lf, (b e + δ)) ≡ (∏ e ∈ Lf, b e) + δ * (∑ e ∈ Lf, ∏ e' ∈ Lf.erase e, b e') [ZMOD ((p^r:ℤ))^3] := h1
    _ ≡ (∏ e ∈ Lf, b e) + 0 [ZMOD ((p^r:ℤ))^3] := by
        apply Int.ModEq.add_left; exact (Int.modEq_zero_iff_dvd.mpr hδD)
    _ = ∏ e ∈ Lf, b e := by ring

def BG3 (p r C K : ℕ) : ℕ := ∏ j ∈ (Finset.Icc 1 (K*p^r)).filter (fun j => ¬ p ∣ j), (C*p^r + 3*j)

theorem bg3_succ (p r C K : ℕ) (hp : 0 < p) (hr : 1 ≤ r) :
    BG3 p r C (K+1)
      = BG3 p r C K * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), ((C+3*K)*p^r + 3*e) := by
  unfold BG3
  set q := p^r with hq
  have hqdvd : p ∣ K*q := by rw [hq]; exact (dvd_pow_self p (by omega : r ≠ 0)).mul_left K
  have hsplit : (Finset.Icc 1 ((K+1)*q)).filter (fun j => ¬ p ∣ j)
      = ((Finset.Icc 1 (K*q)).filter (fun j => ¬ p ∣ j))
        ∪ ((Finset.Icc (K*q+1) ((K+1)*q)).filter (fun j => ¬ p ∣ j)) := by
    rw [← Finset.filter_union]; congr 1
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_or_ge x (K*q+1) with h | h
      · left; exact ⟨h1, by omega⟩
      · right; exact ⟨h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_trans h2 (Nat.mul_le_mul_right q (Nat.le_succ K))⟩
      · exact ⟨by omega, h2⟩
  have hdisj : Disjoint ((Finset.Icc 1 (K*q)).filter (fun j => ¬ p ∣ j))
        ((Finset.Icc (K*q+1) ((K+1)*q)).filter (fun j => ¬ p ∣ j)) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  rw [hsplit, Finset.prod_union hdisj]
  congr 1
  have hKq : (K+1)*q = K*q + q := by ring
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

theorem BG3_cong (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (C K : ℕ) :
    (BG3 p r C K : ℤ)
      ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((3*e:ℕ):ℤ))^K
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
  | zero => simp [BG3]
  | succ K IH =>
      rw [bg3_succ p r C K hp.pos hr]
      have hcast : ((BG3 p r C K * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), ((C+3*K)*p^r + 3*e) : ℕ) : ℤ)
          = (BG3 p r C K:ℤ) * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), (((C+3*K)*p^r + 3*e : ℕ):ℤ) := by
        push_cast; ring
      rw [hcast]
      have hblock : (∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), (((C+3*K)*p^r + 3*e : ℕ):ℤ))
          ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((3*e:ℕ):ℤ)) [ZMOD ((p^r:ℕ):ℤ)^3] := by
        rw [hqf]
        exact block_cong3 p r hp hp5 hr (C+3*K)
      calc (BG3 p r C K:ℤ) * ∏ e ∈ (Finset.Icc 1 (p^r)).filter (fun e => ¬ p ∣ e), (((C+3*K)*p^r + 3*e : ℕ):ℤ)
          ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((3*e:ℕ):ℤ))^K
            * (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((3*e:ℕ):ℤ)) [ZMOD ((p^r:ℕ):ℤ)^3] :=
              Int.ModEq.mul IH hblock
        _ = (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((3*e:ℕ):ℤ))^(K+1) := by rw [pow_succ]

/-- The `p`-free part of `Qseq (M*p)`. -/
def QG (p M : ℕ) : ℕ := ∏ k ∈ (Finset.Icc 1 (M*p)).filter (fun k => ¬ p ∣ k), ((M*p) + 3*k)

theorem Q_split (p M : ℕ) (hp : 0 < p) :
    Qseq (M*p) = p^M * Qseq M * QG p M := by
  unfold Qseq QG
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (M*p)) (fun k => p ∣ k)]
  have hA : (∏ k ∈ (Finset.Icc 1 (M*p)).filter (fun k => p ∣ k), ((M*p)+3*k))
      = p^M * ∏ k ∈ Finset.Icc 1 M, (M+3*k) := by
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
    rw [Finset.prod_congr rfl (fun k _ => show (M*p) + 3*(p*k) = p*(M+3*k) from by ring)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hA]

theorem qg_coprime (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : Nat.Coprime (QG p M) p := by
  unfold QG
  apply Nat.Coprime.prod_left
  intro j hj
  simp only [Finset.mem_filter] at hj
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hd
  apply hj.2
  have h5 : p ∣ (M*p) := ⟨M, by ring⟩
  have h3j : p ∣ 3*j := by
    have := Nat.dvd_sub hd h5; rwa [Nat.add_sub_cancel_left] at this
  rcases hp.dvd_mul.mp h3j with h|h
  · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  · exact h

theorem Qseq_ne' (n : ℕ) : Qseq n ≠ 0 := by
  unfold Qseq
  exact Finset.prod_ne_zero_iff.mpr (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)

/-- Core supercongruence for the exact integer form `aexact`. -/
theorem core172 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
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
  have hAi : A * (((3*(M*p))! * (2*(M*p))! * Qseq (M*p) : ℕ):ℤ)
      = ((3^(M*p) * (6*(M*p))! : ℕ):ℤ) := by
    rw [hAdef, ← Nat.cast_mul, mul_comm, aexact_spec]
  have hBi : B * (((3*M)! * (2*M)! * Qseq M : ℕ):ℤ)
      = ((3^M * (6*M)! : ℕ):ℤ) := by
    rw [hBdef, ← Nat.cast_mul, mul_comm, aexact_spec]
  set SL := QG p M * Gcop p (3*M*p) * Gcop p (2*M*p) with hSL
  set SR := 3^(M*(p-1)) * Gcop p (6*M*p) with hSR
  have e6 : (6*(M*p))! = p^(6*M) * (6*M)! * Gcop p (6*M*p) := by
    rw [show 6*(M*p) = (6*M)*p from by ring]; exact fact_split p (6*M) hp0
  have e3 : (3*(M*p))! = p^(3*M) * (3*M)! * Gcop p (3*M*p) := by
    rw [show 3*(M*p) = (3*M)*p from by ring]; exact fact_split p (3*M) hp0
  have e2 : (2*(M*p))! = p^(2*M) * (2*M)! * Gcop p (2*M*p) := by
    rw [show 2*(M*p) = (2*M)*p from by ring]; exact fact_split p (2*M) hp0
  have eQ : Qseq (M*p) = p^M * Qseq M * QG p M := Q_split p M hp0
  have e3pow : (3:ℕ)^(M*p) = 3^M * 3^(M*(p-1)) := by
    rw [← pow_add]; congr 1
    conv_lhs => rw [show (p:ℕ) = (p-1)+1 from by omega]
    ring
  have hK : (3^(M*p) * (6*(M*p))!) * SL * ((3*M)! * (2*M)! * Qseq M)
      = (3^M * (6*M)!) * SR * ((3*(M*p))! * (2*(M*p))! * Qseq (M*p)) := by
    rw [e6, e3, e2, eQ, e3pow, hSL, hSR]
    ring
  have hKz : ((3^(M*p) * (6*(M*p))! : ℕ):ℤ) * (SL:ℤ) * (((3*M)! * (2*M)! * Qseq M : ℕ):ℤ)
      = ((3^M * (6*M)! : ℕ):ℤ) * (SR:ℤ) * (((3*(M*p))! * (2*(M*p))! * Qseq (M*p) : ℕ):ℤ) := by
    exact_mod_cast hK
  rw [← hAi, ← hBi] at hKz
  have hDN0 : (((3*(M*p))! * (2*(M*p))! * Qseq (M*p) : ℕ):ℤ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) (Qseq_ne' _)
  have hDM0 : (((3*M)! * (2*M)! * Qseq M : ℕ):ℤ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) (Qseq_ne' _)
  have hABSL : A * (SL:ℤ) = B * (SR:ℤ) := by
    have hprod : (A * (SL:ℤ)) * ((((3*(M*p))! * (2*(M*p))! * Qseq (M*p) : ℕ):ℤ) * (((3*M)! * (2*M)! * Qseq M : ℕ):ℤ))
        = (B * (SR:ℤ)) * ((((3*(M*p))! * (2*(M*p))! * Qseq (M*p) : ℕ):ℤ) * (((3*M)! * (2*M)! * Qseq M : ℕ):ℤ)) := by
      linear_combination hKz
    exact mul_right_cancel₀ (mul_ne_zero hDN0 hDM0) hprod
  -- congruences mod (p^r)^3
  have hgcong : ∀ c : ℕ, (Gcop p (c*M*p):ℤ) ≡ (Gcop p (p^r):ℤ)^(c*n) [ZMOD ((p^r:ℕ):ℤ)^3] := by
    intro c; rw [hcoef c]; exact core_G p r hp hp5 hr (c*n)
  have hQGeq : QG p M = BG3 p r n n := by
    unfold QG BG3; rw [← hNM]
  have hQG : (QG p M:ℤ)
      ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((3*e:ℕ):ℤ))^n [ZMOD ((p^r:ℕ):ℤ)^3] := by
    rw [hQGeq]; exact BG3_cong p r hp hp5 hr n n
  have hSLcong : (SL:ℤ) ≡ (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((3*e:ℕ):ℤ))^n
      * (Gcop p (p^r):ℤ)^(3*n) * (Gcop p (p^r):ℤ)^(2*n) [ZMOD ((p^r:ℕ):ℤ)^3] := by
    rw [hSL]; push_cast
    exact (hQG.mul (hgcong 3)).mul (hgcong 2)
  have hSRcong : (SR:ℤ) ≡ (3:ℤ)^(M*(p-1)) * (Gcop p (p^r):ℤ)^(6*n) [ZMOD ((p^r:ℕ):ℤ)^3] := by
    rw [hSR]; push_cast
    exact (Int.ModEq.refl _).mul (hgcong 6)
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
  have h3eU : (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((3*e:ℕ):ℤ))
      = 3^(((Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e)).card) * (Gcop p (p^r):ℤ) := by
    rw [hGU, Finset.prod_congr rfl (fun e _ => by push_cast; ring :
        ∀ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((3*e:ℕ):ℤ) = 3 * (e:ℤ)),
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
  have hEQ : (∏ e ∈ (Finset.Icc 1 (p^r-1)).filter (fun e => ¬ p ∣ e), ((3*e:ℕ):ℤ))^n
        * (Gcop p (p^r):ℤ)^(3*n) * (Gcop p (p^r):ℤ)^(2*n)
      = (3:ℤ)^(M*(p-1)) * (Gcop p (p^r):ℤ)^(6*n) := by
    rw [h3eU, mul_pow, ← pow_mul, hcardcard,
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
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_left (qg_coprime p M hp hp5) (gcop_coprime p (3*M*p) hp)) (gcop_coprime p (2*M*p) hp)
  have hcop : IsCoprime ((p:ℤ)^(3*r)) (SL:ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hcopSL).symm.pow_left
  exact hcop.dvd_of_dvd_mul_right hdvd2


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

lemma hPQ (n : ℕ) :
    (3:ℝ)^n * ∏ i ∈ Finset.range n, (1/3*(n:ℝ)+1+(i:ℝ)) = (Qseq n : ℝ) := by
  have hcard : (3:ℝ)^n = ∏ i ∈ Finset.range n, (3:ℝ) := by
    rw [Finset.prod_const, Finset.card_range]
  have hcast : (Qseq n : ℝ) = ∏ i ∈ Finset.range n, ((n:ℝ)+3+3*(i:ℝ)) := by
    rw [Qseq]; push_cast
    rw [show Finset.Icc 1 n = Finset.Ico 1 (n+1) from by
          ext x; simp [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff],
        Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.prod_congr rfl; intro i _; push_cast; ring
  rw [hcard, ← Finset.prod_mul_distrib, hcast]
  apply Finset.prod_congr rfl; intro i _; ring

lemma val_eq (n : ℕ) :
    (Real.Gamma (6 * (n:ℝ) + 1) * Real.Gamma (1 / 3 * (n:ℝ) + 1)) /
    (Real.Gamma (3 * (n:ℝ) + 1) * Real.Gamma (2 * (n:ℝ) + 1) * Real.Gamma (4 / 3 * (n:ℝ) + 1))
    = (aexact n : ℝ) := by
  have hx : (0:ℝ) < 1 / 3 * (n:ℝ) + 1 := by positivity
  have hG : (0:ℝ) < Real.Gamma (1 / 3 * (n:ℝ) + 1) := Real.Gamma_pos_of_pos hx
  have hf3 : (0:ℝ) < ((3*n)! : ℝ) := by exact_mod_cast (3*n).factorial_pos
  have hf2 : (0:ℝ) < ((2*n)! : ℝ) := by exact_mod_cast (2*n).factorial_pos
  have hPpos : (0:ℝ) < ∏ i ∈ Finset.range n, (1/3*(n:ℝ)+1+(i:ℝ)) :=
    Finset.prod_pos (fun i _ => by positivity)
  have hshift : Real.Gamma (4 / 3 * (n:ℝ) + 1)
      = Real.Gamma (1/3*(n:ℝ)+1) * ∏ i ∈ Finset.range n, (1/3*(n:ℝ)+1+(i:ℝ)) := by
    have h := gamma_shift (1/3*(n:ℝ)+1) hx n
    rw [show (1/3*(n:ℝ)+1)+(n:ℝ) = 4/3*(n:ℝ)+1 by ring] at h
    exact h
  have haex : (aexact n : ℝ) = ↑(3^n*(6*n)!) / ↑((3*n)!*(2*n)!*Qseq n) := by
    rw [eq_div_iff (by exact_mod_cast (mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _)
        (Nat.factorial_ne_zero _)) (Qseq_ne n)))]
    have hspec := congrArg (fun t : ℕ => (t : ℝ)) (aexact_spec n)
    push_cast
    push_cast at hspec
    linear_combination hspec
  rw [show (6:ℝ)*(n:ℝ)+1 = ((6*n:ℕ):ℝ)+1 by push_cast; ring,
      show (3:ℝ)*(n:ℝ)+1 = ((3*n:ℕ):ℝ)+1 by push_cast; ring,
      show (2:ℝ)*(n:ℝ)+1 = ((2*n:ℕ):ℝ)+1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      hshift, haex]
  rw [div_eq_div_iff
      (mul_ne_zero (mul_ne_zero hf3.ne' hf2.ne') (mul_ne_zero hG.ne' hPpos.ne'))
      (by exact_mod_cast (mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _)
        (Nat.factorial_ne_zero _)) (Qseq_ne n)))]
  push_cast
  linear_combination (-(((6*n)! : ℝ) * ((3*n)! : ℝ) * ((2*n)! : ℝ)
    * Real.Gamma (1 / 3 * (n:ℝ) + 1))) * hPQ n

lemma a_eq (n : ℕ) : a n = aexact n := by
  show (round _).toNat = aexact n
  rw [val_eq n, round_natCast, Int.toNat_natCast]


/--
Conjecture: the supercongruences $a(n p^r) \equiv a(n p^{r-1}) \pmod{p^{3r}}$
hold for all primes $p \ge 5$ and all positive integers $n$ and $r$.
-/
theorem oeis_364172_conjecture_0 (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
  (hn : 0 < n) (hr : 0 < r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  rw [a_eq, a_eq, Nat.modEq_iff_dvd, dvd_sub_comm]
  push_cast
  exact core172 p hp h_prime_ge_five n r hn hr

#print axioms oeis_364172_conjecture_0
