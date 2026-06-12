/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports
import Mathlib.Algebra.IsPrimePow

/-!
# Conjecture relating two characterizations of a set of integers.

Informal Statement:
For an integer $k ≥ 2$, the following are equivalent:

1. The greatest common divisor of the binomial coefficients
    $\binom{2k}{k}, \binom{3k}{k}, \dots, \binom{(k+1)k}{k} = 1$.

2. Writing prime factorization of k as
    $k = \prod p_i^{e_i}$, and let
    $P = \max_i p_i^{e_i}$,
    one has $k / P > P$.

This conjecture asserts that the sequence defined by 1. is obtained by
taking 1 off each number in the sequence defined by 2.

*Reference:*
- [A80170](https://oeis.org/A80170)
- [A51283](https://oeis.org/A51283)
-/

-- The supporting lemmas below are proof infrastructure rather than catalogued
-- problem statements, so the category/AMS attribute linters are disabled here.
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

namespace OeisA80170

/--
The gcd of the binomial coefficients
$\binom{2k}{k}, \binom{3k}{k}, \dots, \binom{(k+1)k}{k} = 1$.
-/
def GCDCondition (k : ℕ) : Prop :=
  (Finset.range k).gcd (fun i => Nat.choose ((i + 2) * k) k) = 1

/--
Let P be the largest prime power dividing `k`.
Then $k / P > P$.
-/
def PrimePowerCondition (k : ℕ) : Prop :=
  let P := ((Nat.divisors k).filter IsPrimePow).max.getD 0
  k / P > P

/- ## Supporting theory for the proof -/

/- ## Supporting definitions -/

/-- The binomial GCD
`D k = gcd_{2 ≤ q ≤ k+1} C(qk, k)`. -/
def D (k : ℕ) : ℕ :=
  (Finset.Icc 2 (k + 1)).gcd fun q => Nat.choose (q * k) k

/-- The largest exact prime-power component (Section 1):
`ppart n = max { p^a : p^a ∥ n }` for `n > 1`, where `p^a ∥ n` means
`p^a ∣ n ∧ ¬ p^(a+1) ∣ n`.  For each prime `p ∣ n`, the exact component is
`p ^ (n.factorization p)`, so the maximum is the `Finset.sup` over
`n.primeFactors`.  (For `n ≤ 1` this yields the junk value `0`; `ppart`
is only meaningful for `n > 1`.) -/
def ppart (n : ℕ) : ℕ :=
  n.primeFactors.sup fun p => p ^ n.factorization p

/-- The digit box `𝒟_c` of Section 4: for a prime `p`, `L ≥ 1`, `P = p^L`
and `0 ≤ c < P`, the set of `y < P` such that every base-`p` digit of `y`
is at most the corresponding digit of `c`.  The `i`-th base-`p` digit of
`y` is `y / p^i % p`; since `y < p^L`, all digits with index `≥ L` vanish,
so quantifying over `i < L` is equivalent to quantifying over all `i`. -/
def digitBox (p L c : ℕ) : Finset ℕ :=
  (Finset.range (p ^ L)).filter fun y => ∀ i < L, y / p ^ i % p ≤ c / p ^ i % p

/- ## Two standard algebraic tools (Section 2) -/

section NewtonInterpolation

open Polynomial Finset

/-- `Ring.choose` over `ℚ` is the evaluation of the descending Pochhammer
polynomial divided by `r!`. -/
private lemma ringChoose_eq_inv_factorial_mul_eval (t : ℚ) (r : ℕ) :
    Ring.choose t r = (r.factorial : ℚ)⁻¹ * (descPochhammer ℚ r).eval t := by
  rw [Ring.choose_eq_smul, smul_eq_mul, ← Polynomial.aeval_eq_smeval,
    Polynomial.aeval_def, ← Polynomial.eval_map, descPochhammer_map]

/-- **Lemma (Newton interpolation by forward differences)**.
"Let `f` be a polynomial of degree at most `d`, and define
`Δf(x) = f(x+1) − f(x)`.  For every integer `a` and every `x`,
`f(x) = ∑_{r=0}^{d} C(x−a, r) · Δ^r f(a)`."

Encoding: polynomials over `ℚ`; `Δ` is Mathlib's `fwdDiff (1 : ℚ)` applied
to the evaluation function of `f`; the generalized binomial coefficient
`C(x−a, r)` is `Ring.choose (x − a) r` in the binomial ring `ℚ`. -/
theorem newton_interpolation (f : Polynomial ℚ) (d : ℕ) (hf : f.natDegree ≤ d)
    (a : ℤ) (x : ℚ) :
    f.eval x =
      ∑ r ∈ Finset.range (d + 1),
        Ring.choose (x - (a : ℚ)) r *
          (fwdDiff (1 : ℚ))^[r] (fun y => f.eval y) (a : ℚ) := by
  -- The interpolating polynomial `g(X) = ∑ r, Δ^r f(a)/r! * (X-a)(X-a-1)⋯(X-a-r+1)`.
  set g : Polynomial ℚ :=
    ∑ r ∈ Finset.range (d + 1),
      Polynomial.C ((r.factorial : ℚ)⁻¹ *
          (fwdDiff (1 : ℚ))^[r] (fun y => f.eval y) (a : ℚ)) *
        (descPochhammer ℚ r).comp (Polynomial.X - Polynomial.C (a : ℚ)) with hg
  -- `g` evaluates to the Newton sum.
  have heval : ∀ y : ℚ, g.eval y =
      ∑ r ∈ Finset.range (d + 1),
        Ring.choose (y - (a : ℚ)) r *
          (fwdDiff (1 : ℚ))^[r] (fun y => f.eval y) (a : ℚ) := by
    intro y
    rw [hg, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      ringChoose_eq_inv_factorial_mul_eval]
    ring
  -- `g` has degree at most `d`.
  have hdeg : g.natDegree ≤ d := by
    rw [hg]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r hr => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.natDegree_comp, descPochhammer_natDegree,
      Polynomial.natDegree_X_sub_C, mul_one]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  -- `f` and `g` agree at the `d+1` nodes `a, a+1, …, a+d`.
  have hnode : ∀ j : ℕ, j ≤ d →
      g.eval ((a : ℚ) + (j : ℚ)) = f.eval ((a : ℚ) + (j : ℚ)) := by
    intro j hj
    rw [heval]
    have hcast : (a : ℚ) + (j : ℚ) - (a : ℚ) = ((j : ℕ) : ℚ) := by ring
    rw [hcast]
    simp only [Ring.choose_natCast]
    have key := shift_eq_sum_fwdDiff_iter (1 : ℚ) (fun y => f.eval y) j (a : ℚ)
    simp only [nsmul_eq_mul, mul_one] at key
    rw [key]
    have hsub : Finset.range (j + 1) ⊆ Finset.range (d + 1) := by
      intro r hr
      rw [Finset.mem_range] at hr ⊢
      omega
    refine (Finset.sum_subset hsub ?_).symm
    intro r _ hr
    rw [Finset.mem_range, not_lt] at hr
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  -- Two polynomials of degree ≤ d agreeing at d+1 points are equal.
  have hzero : f - g = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (f - g)
      (f := fun i : Fin (d + 1) => (a : ℚ) + ((i : ℕ) : ℚ))
    · intro i j hij
      simp only [add_right_inj, Nat.cast_inj] at hij
      exact Fin.ext hij
    · intro i
      rw [Polynomial.eval_sub, sub_eq_zero]
      exact (hnode (i : ℕ) (Nat.lt_succ_iff.mp i.isLt)).symm
    · have h1 := Polynomial.natDegree_sub_le f g
      have h2 : (f - g).natDegree ≤ d := h1.trans (max_le hf hdeg)
      rw [Fintype.card_fin]
      omega
  have hfg : f = g := sub_eq_zero.mp hzero
  conv_lhs => rw [hfg]
  exact heval x

end NewtonInterpolation

/-- Single-digit Lucas criterion: for `n < p`, the prime `p` does not divide
`C(n, k)` iff `k ≤ n`.  (If `k > n` then `C(n, k) = 0`; if `k ≤ n` then
`C(n, k) ∣`-related to `n!`, all of whose prime factors are `≤ n < p`.) -/
private lemma lucas_aux_digit {p : ℕ} (hp : p.Prime) {n k : ℕ} (hn : n < p) :
    ¬ p ∣ Nat.choose n k ↔ k ≤ n := by
  constructor
  · intro h
    by_contra hk
    push Not at hk
    rw [Nat.choose_eq_zero_of_lt hk] at h
    exact h (dvd_zero p)
  · intro hk hdvd
    have h1 : p ∣ Nat.factorial n := by
      rw [← Nat.choose_mul_factorial_mul_factorial hk]
      exact (hdvd.mul_right _).mul_right _
    exact absurd (hp.dvd_factorial.mp h1) (Nat.not_le.mpr hn)

/-- **Lemma (Lucas non-vanishing criterion)**.
"Let `p` be prime, and write `N = ∑ N_i p^i`, `K = ∑ K_i p^i` with
`0 ≤ N_i, K_i < p`.  Then `C(N, K) ≢ 0 (mod p)  ↔  K_i ≤ N_i` for every `i`."

Encoding: the `i`-th base-`p` digit of `N` is `N / p^i % p`. -/
theorem lucas_nonvanishing (p : ℕ) (hp : p.Prime) (N K : ℕ) :
    ¬ p ∣ Nat.choose N K ↔ ∀ i, K / p ^ i % p ≤ N / p ^ i % p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set a := N + K with ha
  have hN : N < p ^ a :=
    lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
      (Nat.pow_le_pow_right hp.one_lt.le (Nat.le_add_right _ _))
  have hK : K < p ^ a :=
    lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
      (Nat.pow_le_pow_right hp.one_lt.le (Nat.le_add_left _ _))
  have hmod := Choose.lucas_theorem_nat (p := p) (n := N) (k := K) hN hK
  rw [hmod.dvd_iff dvd_rfl, hp.prime.dvd_finset_prod_iff]
  push Not
  constructor
  · intro h i
    by_cases hi : i < a
    · exact (lucas_aux_digit hp (Nat.mod_lt _ hp.pos)).mp (h i (Finset.mem_range.mpr hi))
    · push Not at hi
      have hKi : K / p ^ i = 0 :=
        Nat.div_eq_of_lt (lt_of_lt_of_le hK (Nat.pow_le_pow_right hp.one_lt.le hi))
      simp [hKi]
  · intro h i _
    exact (lucas_aux_digit hp (Nat.mod_lt _ hp.pos)).mpr (h i)

/- ## Primes in the GCD (Section 3) -/

/-- `(−1)(−2)⋯(−r) = (−1)^r · r!`. -/
private lemma descPochhammer_eval_neg_one (r : ℕ) :
    (descPochhammer ℚ r).eval (-1) = (-1) ^ r * r.factorial := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_eval, ih, Nat.factorial_succ]
    push_cast
    ring

/-- `C(−1, r) = (−1)^r` in the binomial ring `ℚ`. -/
private lemma ringChoose_neg_one (r : ℕ) :
    Ring.choose (-1 : ℚ) r = (-1 : ℚ) ^ r := by
  rw [ringChoose_eq_inv_factorial_mul_eval, descPochhammer_eval_neg_one,
    mul_comm ((-1 : ℚ) ^ r) _, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr r.factorial_ne_zero), one_mul]

/-- **Lemma (Prime divisors of the GCD)**.
"Let `k ≥ 1` and `D(k) = gcd_{2 ≤ q ≤ k+1} C(qk, k)`.
If a prime `p` divides `D(k)`, then `p ∣ k+1`." -/
theorem prime_dvd_succ_of_dvd_D (k p : ℕ) (hk : 1 ≤ k)
    (h : p ∣ D k) : p ∣ k + 1 := by
  -- The polynomial `F(x) = C(kx, k)` over `ℚ`.
  set F : Polynomial ℚ := Polynomial.C ((k.factorial : ℚ)⁻¹) *
      (descPochhammer ℚ k).comp (Polynomial.C (k : ℚ) * Polynomial.X) with hF
  -- `F` interpolates the binomial values at the naturals.
  have hFeval : ∀ q : ℕ, F.eval (q : ℚ) = (Nat.choose (q * k) k : ℚ) := by
    intro q
    rw [hF, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      ← ringChoose_eq_inv_factorial_mul_eval,
      show (k : ℚ) * (q : ℚ) = ((q * k : ℕ) : ℚ) by push_cast; ring,
      Ring.choose_natCast]
  -- `F` has degree at most `k`.
  have hdeg : F.natDegree ≤ k := by
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine Polynomial.natDegree_comp_le.trans ?_
    rw [descPochhammer_natDegree]
    calc k * (Polynomial.C (k : ℚ) * Polynomial.X).natDegree
        ≤ k * 1 := Nat.mul_le_mul_left k
          ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
      _ = k := mul_one k
  -- `F(0) = C(0, k) = 0` since `k ≥ 1`.
  have hF0 : F.eval (0 : ℚ) = 0 := by
    simpa [Nat.choose_eq_zero_of_lt hk] using hFeval 0
  -- Newton interpolation at `x = 0`, `a = 1`.
  have hnewton := newton_interpolation F k hdeg 1 0
  simp only [Int.cast_one, zero_sub] at hnewton
  -- Expand the iterated forward differences at `1`.
  have hfd : ∀ r : ℕ, (fwdDiff (1 : ℚ))^[r] (fun y => F.eval y) (1 : ℚ) =
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ (r - j) * (r.choose j : ℚ) * (Nat.choose ((1 + j) * k) k : ℚ) := by
    intro r
    rw [fwdDiff_iter_eq_sum_shift]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (1 : ℚ) + j • (1 : ℚ) = ((1 + j : ℕ) : ℚ) := by
      rw [nsmul_eq_mul, mul_one]
      push_cast
      ring
    simp only [h1, hFeval (1 + j), zsmul_eq_mul]
    push_cast
    ring
  -- The master identity over `ℚ`.
  have hmaster : (0 : ℚ) = ∑ r ∈ Finset.range (k + 1), (-1 : ℚ) ^ r *
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ (r - j) * (r.choose j : ℚ) * (Nat.choose ((1 + j) * k) k : ℚ) := by
    rw [← hF0, hnewton]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ringChoose_neg_one, hfd r]
  -- The same identity as an integer identity.
  have hTzero : (∑ r ∈ Finset.range (k + 1), (-1 : ℤ) ^ r *
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℤ) ^ (r - j) * (r.choose j : ℤ) * (Nat.choose ((1 + j) * k) k : ℤ)) = 0 := by
    have hQ : ((∑ r ∈ Finset.range (k + 1), (-1 : ℤ) ^ r *
        ∑ j ∈ Finset.range (r + 1),
          (-1 : ℤ) ^ (r - j) * (r.choose j : ℤ) *
            (Nat.choose ((1 + j) * k) k : ℤ) : ℤ) : ℚ) = 0 := by
      push_cast
      exact hmaster.symm
    exact_mod_cast hQ
  -- Map the integer identity into `ZMod p`.
  have hsumZ : (∑ r ∈ Finset.range (k + 1), (-1 : ZMod p) ^ r *
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ZMod p) ^ (r - j) * (r.choose j : ZMod p) *
          (Nat.choose ((1 + j) * k) k : ZMod p)) = 0 := by
    have h0 : ((∑ r ∈ Finset.range (k + 1), (-1 : ℤ) ^ r *
        ∑ j ∈ Finset.range (r + 1),
          (-1 : ℤ) ^ (r - j) * (r.choose j : ℤ) *
            (Nat.choose ((1 + j) * k) k : ℤ) : ℤ) : ZMod p) = 0 := by
      rw [hTzero]
      exact Int.cast_zero
    push_cast at h0
    exact h0
  -- Modulo `p`, only the `j = 0` terms survive, each contributing `1`.
  have houter : ∀ r ∈ Finset.range (k + 1),
      (-1 : ZMod p) ^ r * (∑ j ∈ Finset.range (r + 1),
        (-1 : ZMod p) ^ (r - j) * (r.choose j : ZMod p) *
          (Nat.choose ((1 + j) * k) k : ZMod p)) = 1 := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hinner : (∑ j ∈ Finset.range (r + 1),
        (-1 : ZMod p) ^ (r - j) * (r.choose j : ZMod p) *
          (Nat.choose ((1 + j) * k) k : ZMod p)) = (-1 : ZMod p) ^ r := by
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos r))]
      · simp
      · intro j hj hj0
        rw [Finset.mem_range] at hj
        have hdvd : p ∣ Nat.choose ((1 + j) * k) k :=
          h.trans (Finset.gcd_dvd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
        rw [(ZMod.natCast_eq_zero_iff _ _).mpr hdvd, mul_zero]
    rw [hinner, ← mul_pow, neg_mul_neg, one_mul, one_pow]
  -- Conclude: `0 = ∑_{r ≤ k} 1 = k + 1` in `ZMod p`.
  have hfinal : ((k + 1 : ℕ) : ZMod p) = 0 := by
    have hsum1 : (∑ _r ∈ Finset.range (k + 1), (1 : ZMod p)) = ((k + 1 : ℕ) : ZMod p) := by
      simp
    rw [← hsum1, ← Finset.sum_congr rfl houter]
    exact hsumZ
  exact (ZMod.natCast_eq_zero_iff _ _).mp hfinal

/- ## Digit boxes (Section 4) -/

/-- Membership characterization of the digit box. -/
lemma mem_digitBox {p L c y : ℕ} :
    y ∈ digitBox p L c ↔ y < p ^ L ∧ ∀ i < L, y / p ^ i % p ≤ c / p ^ i % p := by
  simp [digitBox]

/-- `c` itself lies in its digit box `𝒟_c` whenever `c < p^L`. -/
lemma self_mem_digitBox {p L c : ℕ} (hc : c < p ^ L) : c ∈ digitBox p L c :=
  mem_digitBox.mpr ⟨hc, fun _ _ => le_rfl⟩

/-- For `i < L`, the `i`-th base-`p` digit of `y % p^L` equals that of `y`. -/
lemma digit_mod_pow (p L i y : ℕ) (h : i < L) :
    y % p ^ L / p ^ i % p = y / p ^ i % p := by
  rw [← Nat.mod_mul_right_div_self y (p ^ i) p,
      ← Nat.mod_mul_right_div_self (y % p ^ L) (p ^ i) p,
      ← pow_succ, Nat.mod_mod_of_dvd y (pow_dvd_pow p h)]

/-- `0` lies in every digit box. -/
lemma zero_mem_digitBox (p L c : ℕ) (hp : 0 < p) : 0 ∈ digitBox p L c := by
  rw [mem_digitBox]
  exact ⟨pow_pos hp L, fun i _ => by simp⟩

/-- Block decomposition: membership in a digit box of `L+1` digits splits
into a top-digit comparison and membership of the remainder in the digit
box of the low `L` digits. -/
lemma mem_digitBox_succ {p : ℕ} (hp : 0 < p) (L c y : ℕ) (hc : c < p ^ (L + 1)) :
    y ∈ digitBox p (L + 1) c ↔
      y / p ^ L ≤ c / p ^ L ∧ y % p ^ L ∈ digitBox p L (c % p ^ L) := by
  have hH0 : 0 < p ^ L := pow_pos hp L
  have hcp : c / p ^ L < p := by
    rw [Nat.div_lt_iff_lt_mul hH0]
    calc c < p ^ (L + 1) := hc
      _ = p * p ^ L := by ring
  constructor
  · intro hy
    rw [mem_digitBox] at hy
    obtain ⟨hylt, hd⟩ := hy
    have hyp : y / p ^ L < p := by
      rw [Nat.div_lt_iff_lt_mul hH0]
      calc y < p ^ (L + 1) := hylt
        _ = p * p ^ L := by ring
    have htop := hd L (Nat.lt_succ_self L)
    rw [Nat.mod_eq_of_lt hyp, Nat.mod_eq_of_lt hcp] at htop
    refine ⟨htop, ?_⟩
    rw [mem_digitBox]
    refine ⟨Nat.mod_lt y hH0, fun i hi => ?_⟩
    rw [digit_mod_pow p L i y hi, digit_mod_pow p L i c hi]
    exact hd i (by omega)
  · rintro ⟨htop, hmem⟩
    rw [mem_digitBox] at hmem ⊢
    obtain ⟨hmlt, hmd⟩ := hmem
    have hyp : y / p ^ L < p := lt_of_le_of_lt htop hcp
    constructor
    · rw [show p ^ (L + 1) = p * p ^ L by ring, ← Nat.div_lt_iff_lt_mul hH0]
      exact hyp
    · intro i hi
      rcases Nat.lt_or_ge i L with hiL | hiL
      · rw [← digit_mod_pow p L i y hiL, ← digit_mod_pow p L i c hiL]
        exact hmd i hiL
      · have hieq : i = L := by omega
        subst hieq
        rw [Nat.mod_eq_of_lt hyp, Nat.mod_eq_of_lt hcp]
        exact htop

/-- Digit domination implies numeric domination: every element of the
digit box `𝒟_c` is at most `c`. -/
lemma le_of_mem_digitBox (p : ℕ) (hp : 0 < p) :
    ∀ L c y, y ∈ digitBox p L c → y ≤ c := by
  intro L
  induction L with
  | zero =>
    intro c y hy
    have h := (mem_digitBox.1 hy).1
    simp only [pow_zero] at h
    omega
  | succ L ih =>
    intro c y hy
    rcases Nat.lt_or_ge c (p ^ (L + 1)) with hc | hc
    · rw [mem_digitBox_succ hp L c y hc] at hy
      obtain ⟨htop, hmod⟩ := hy
      have h1 : y % p ^ L ≤ c % p ^ L := ih (c % p ^ L) (y % p ^ L) hmod
      calc y = p ^ L * (y / p ^ L) + y % p ^ L := (Nat.div_add_mod y (p ^ L)).symm
        _ ≤ p ^ L * (c / p ^ L) + c % p ^ L :=
            Nat.add_le_add (Nat.mul_le_mul_left _ htop) h1
        _ = c := Nat.div_add_mod c (p ^ L)
    · have h := (mem_digitBox.1 hy).1
      omega

/-- Core of the gap bound, with `p^L / p` replaced by `p^(L-1)`. -/
lemma gap_bound_aux (p : ℕ) (hp : 0 < p) :
    ∀ L, 1 ≤ L → ∀ c, c < p ^ L → ∀ z ∈ digitBox p L c, z < c →
      ∃ w ∈ digitBox p L c, z < w ∧ w ≤ z + p ^ (L - 1) := by
  intro L
  induction L with
  | zero => intro h; exact absurd h (by omega)
  | succ L ih =>
    intro _ c hc z hz hzc
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · -- base case `L + 1 = 1`: the box is `{0, 1, …, c}`, successor is `z + 1`
      have hc1 : c < p := by simpa using hc
      refine ⟨z + 1, ?_, Nat.lt_succ_self z, by simp⟩
      rw [mem_digitBox]
      refine ⟨by simpa using (by omega : z + 1 < p), fun i hi => ?_⟩
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [pow_zero, Nat.div_one]
      rw [Nat.mod_eq_of_lt (by omega : z + 1 < p), Nat.mod_eq_of_lt hc1]
      omega
    · -- inductive step: decompose into blocks of size `H = p ^ L`
      have hH0 : 0 < p ^ L := pow_pos hp L
      rw [mem_digitBox_succ hp L c z hc] at hz
      obtain ⟨htop, hmod⟩ := hz
      have hzc' : z % p ^ L ≤ c % p ^ L :=
        le_of_mem_digitBox p hp L (c % p ^ L) (z % p ^ L) hmod
      rcases Nat.lt_or_ge (z % p ^ L) (c % p ^ L) with hlt | hge
      · -- `z` is not last in its block: use the inductive hypothesis
        obtain ⟨w', hw', hw'1, hw'2⟩ :=
          ih hL (c % p ^ L) (Nat.mod_lt c hH0) (z % p ^ L) hmod hlt
        have hw'H : w' < p ^ L := (mem_digitBox.1 hw').1
        have hdiv : (p ^ L * (z / p ^ L) + w') / p ^ L = z / p ^ L := by
          rw [Nat.mul_add_div hH0, Nat.div_eq_of_lt hw'H, Nat.add_zero]
        have hmd : (p ^ L * (z / p ^ L) + w') % p ^ L = w' := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hw'H]
        refine ⟨p ^ L * (z / p ^ L) + w', ?_, ?_, ?_⟩
        · rw [mem_digitBox_succ hp L c _ hc, hdiv, hmd]
          exact ⟨htop, hw'⟩
        · conv_lhs => rw [← Nat.div_add_mod z (p ^ L)]
          exact Nat.add_lt_add_left hw'1 _
        · have h1 : p ^ (L - 1) ≤ p ^ L := Nat.pow_le_pow_right hp (by omega)
          have h2 : p ^ L * (z / p ^ L) + z % p ^ L = z := Nat.div_add_mod z (p ^ L)
          calc p ^ L * (z / p ^ L) + w'
              ≤ p ^ L * (z / p ^ L) + (z % p ^ L + p ^ (L - 1)) :=
                Nat.add_le_add_left hw'2 _
            _ = z + p ^ (L - 1) := by rw [← Nat.add_assoc, h2]
            _ ≤ z + p ^ (L + 1 - 1) := by simpa using Nat.add_le_add_left h1 z
      · -- `z` is last in its block: jump to the start of the next block
        have heq : z % p ^ L = c % p ^ L := le_antisymm hzc' hge
        have hac : z / p ^ L < c / p ^ L := by
          by_contra hcon
          have hcon : c / p ^ L ≤ z / p ^ L := Nat.le_of_not_lt hcon
          have hle : c ≤ z := by
            calc c = p ^ L * (c / p ^ L) + c % p ^ L := (Nat.div_add_mod c (p ^ L)).symm
              _ ≤ p ^ L * (z / p ^ L) + z % p ^ L :=
                  Nat.add_le_add (Nat.mul_le_mul_left _ hcon) (le_of_eq heq.symm)
              _ = z := Nat.div_add_mod z (p ^ L)
          omega
        refine ⟨p ^ L * (z / p ^ L + 1), ?_, ?_, ?_⟩
        · rw [mem_digitBox_succ hp L c _ hc]
          constructor
          · rw [Nat.mul_div_cancel_left _ hH0]
            exact hac
          · rw [Nat.mul_mod_right]
            exact zero_mem_digitBox p L (c % p ^ L) hp
        · conv_lhs => rw [← Nat.div_add_mod z (p ^ L)]
          calc p ^ L * (z / p ^ L) + z % p ^ L
              < p ^ L * (z / p ^ L) + p ^ L := Nat.add_lt_add_left (Nat.mod_lt z hH0) _
            _ = p ^ L * (z / p ^ L + 1) := by ring
        · have h2 : p ^ L * (z / p ^ L) + z % p ^ L = z := Nat.div_add_mod z (p ^ L)
          calc p ^ L * (z / p ^ L + 1) = p ^ L * (z / p ^ L) + p ^ L := by ring
            _ ≤ (p ^ L * (z / p ^ L) + z % p ^ L) + p ^ L :=
                Nat.add_le_add_right (Nat.le_add_right _ _) _
            _ = z + p ^ L := by rw [h2]
            _ ≤ z + p ^ (L + 1 - 1) := by simp

/-- **Lemma (Gap bound)**.
"Let `P = p^L` and `0 ≤ c < P`.  If the elements of `𝒟_c` are listed in
increasing order, every gap between two consecutive elements is at most
`P/p`."

Encoding: every element of the box other than the largest (which is `c`)
has a strictly larger element of the box within distance `P/p`.  Since
`0` is the smallest element and `c` the largest, this captures exactly
"all consecutive gaps are ≤ P/p". -/
theorem gap_bound (p L c : ℕ) (hp : p.Prime) (hL : 1 ≤ L) (hc : c < p ^ L) :
    ∀ z ∈ digitBox p L c, z < c →
      ∃ w ∈ digitBox p L c, z < w ∧ w ≤ z + p ^ L / p := by
  have hp0 : 0 < p := hp.pos
  have hdiv : p ^ L / p = p ^ (L - 1) := by
    have h := Nat.pow_div hL hp0
    rwa [pow_one] at h
  rw [hdiv]
  exact gap_bound_aux p hp0 L hL c hc

/-- **Lemma (No nonzero translation)**.
"Let `P = p^L` and `0 ≤ c < P − P/p`.  Suppose `0 ≤ S ≤ c` and
`[z+S]_P ∈ {0, 1, …, c}` for every `z ∈ 𝒟_c`.  Then `S = 0`."

Note: `P − P/p` is exact in `ℕ` (`P/p = p^(L−1)` divides `P`). -/
theorem no_nonzero_translation (p L c S : ℕ) (hp : p.Prime) (hL : 1 ≤ L)
    (hc : c < p ^ L - p ^ L / p) (hS : S ≤ c)
    (h : ∀ z ∈ digitBox p L c, (z + S) % p ^ L ≤ c) :
    S = 0 := by
  by_contra hS0
  have hS0 : 0 < S := Nat.pos_of_ne_zero hS0
  have hdivP : p ^ L / p ≤ p ^ L := Nat.div_le_self _ _
  -- `omega` cannot interpret division by a variable; make `P/p` opaque.
  generalize hQ : p ^ L / p = Q at hc hdivP
  have hcP : c < p ^ L := by omega
  rcases Nat.lt_or_ge S (p ^ L - c) with hcase | hcase
  · -- Case `S < P − c`: translate `z = c` itself; no wraparound, so
    -- `(c + S) % P = c + S > c`, contradiction.
    have hmem := self_mem_digitBox hcP
    have hle := h c hmem
    rw [Nat.mod_eq_of_lt (by omega : c + S < p ^ L)] at hle
    omega
  · -- Case `S ≥ P − c`: take `z*` the largest box element with `z* ≤ c − S`.
    set T : Finset ℕ := (digitBox p L c).filter (· ≤ c - S) with hT
    have hTne : T.Nonempty :=
      ⟨0, Finset.mem_filter.mpr ⟨zero_mem_digitBox p L c hp.pos, Nat.zero_le _⟩⟩
    set z := T.max' hTne with hz
    have hzT : z ∈ T := T.max'_mem hTne
    have hz_mem : z ∈ digitBox p L c := (Finset.mem_filter.mp hzT).1
    have hz_le : z ≤ c - S := (Finset.mem_filter.mp hzT).2
    have hzc : z < c := by omega
    -- Gap bound: a strictly larger box element `w` within distance `P/p`.
    obtain ⟨w, hw_mem, hzw, hwle⟩ := gap_bound p L c hp hL hcP z hz_mem hzc
    rw [hQ] at hwle
    -- Maximality of `z*` forces `w > c − S`.
    have hw_gt : c - S < w := by
      by_contra hcon
      push Not at hcon
      have hwT : w ∈ T := Finset.mem_filter.mpr ⟨hw_mem, hcon⟩
      have := Finset.le_max' T w hwT
      omega
    -- Then `c < w + S < P`, so `(w + S) % P = w + S > c`, contradiction.
    have hle := h w hw_mem
    rw [Nat.mod_eq_of_lt (by omega : w + S < p ^ L)] at hle
    omega

/- ### Digit/divisibility helpers -/

/-- `p^v ∣ y` iff the lowest `v` base-`p` digits of `y` vanish. -/
lemma pow_dvd_iff_digits_zero {p : ℕ} (hp : 0 < p) (v y : ℕ) :
    p ^ v ∣ y ↔ ∀ i < v, y / p ^ i % p = 0 := by
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := h
    have hsplit : p ^ v = p ^ i * p ^ (v - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, mul_assoc, Nat.mul_div_cancel_left _ (pow_pos hp i)]
    have hdvd : p ∣ p ^ (v - i) * k :=
      Dvd.dvd.mul_right (dvd_pow_self p (by omega : v - i ≠ 0)) k
    omega
  · intro h
    have hmem : y % p ^ v ∈ digitBox p v 0 := by
      rw [mem_digitBox]
      refine ⟨Nat.mod_lt _ (pow_pos hp v), fun i hi => ?_⟩
      rw [digit_mod_pow p v i y hi, h i hi]
      simp
    have hle : y % p ^ v ≤ 0 := le_of_mem_digitBox p hp v 0 _ hmem
    exact Nat.dvd_of_mod_eq_zero (Nat.le_zero.mp hle)

/-- The digit box with `c = 0` is `{0}`. -/
lemma digitBox_c_zero (p L : ℕ) (hp : 0 < p) : digitBox p L 0 = {0} := by
  ext y
  rw [Finset.mem_singleton]
  constructor
  · intro hy
    have := le_of_mem_digitBox p hp L 0 y hy
    omega
  · rintro rfl
    exact zero_mem_digitBox p L 0 hp

/-- The one-digit box is an initial segment. -/
lemma digitBox_one {p c : ℕ} (hc : c < p) : digitBox p 1 c = Finset.Iic c := by
  ext y
  rw [mem_digitBox, Finset.mem_Iic]
  constructor
  · rintro ⟨hy, hd⟩
    have h0 := hd 0 Nat.one_pos
    rw [pow_one] at hy
    simpa [Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hc] using h0
  · intro hy
    have hyp : y < p := by omega
    refine ⟨by simpa [pow_one] using hyp, fun i hi => ?_⟩
    have hi0 : i = 0 := by omega
    subst hi0
    simpa [Nat.mod_eq_of_lt hyp, Nat.mod_eq_of_lt hc] using hy

/-- Low-digit split of the digit box: strip off the lowest digit. -/
lemma mem_digitBox_low {p : ℕ} (hp : 0 < p) (L c y : ℕ) :
    y ∈ digitBox p (L + 1) c ↔ y % p ≤ c % p ∧ y / p ∈ digitBox p L (c / p) := by
  rw [mem_digitBox, mem_digitBox]
  have hdiv : ∀ x i : ℕ, x / p ^ (i + 1) = x / p / p ^ i := by
    intro x i
    rw [Nat.div_div_eq_div_mul, ← pow_succ']
  have hlt : y < p ^ (L + 1) ↔ y / p < p ^ L := by
    rw [Nat.div_lt_iff_lt_mul hp, ← pow_succ]
  constructor
  · rintro ⟨hy, hd⟩
    refine ⟨by simpa using hd 0 (by omega), hlt.mp hy, fun i hi => ?_⟩
    rw [← hdiv, ← hdiv]
    exact hd (i + 1) (by omega)
  · rintro ⟨h0, hy, hd⟩
    refine ⟨hlt.mpr hy, fun i hi => ?_⟩
    cases i with
    | zero => simpa using h0
    | succ i =>
      rw [hdiv, hdiv]
      exact hd i (by omega)

/-- Splitting a `mod p*P'` into low digit plus `p` times a `mod P'`. -/
lemma low_high_mod {p P' : ℕ} (_hp : 0 < p) (hP' : 0 < P') (r m : ℕ) (hr : r < p) :
    (r + p * m) % (p * P') = r + p * (m % P') := by
  conv_lhs => rw [← Nat.div_add_mod m P']
  rw [show r + p * (P' * (m / P') + m % P') =
        r + p * (m % P') + p * P' * (m / P') by ring,
      Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have h1 : m % P' < P' := Nat.mod_lt _ hP'
  calc r + p * (m % P') < p + p * (m % P') := by omega
    _ = p * (m % P' + 1) := by ring
    _ ≤ p * P' := Nat.mul_le_mul_left p (by omega)

/- ### Forward direction -/

/-- Forward direction of the stabilizer theorem: if `s ≡ 1` modulo
`p^(L - ord_p c)`, then multiplication by `s` fixes every element of the
digit box modulo `p^L`. -/
lemma stabilizer_forward (p L c s : ℕ) (hp : p.Prime) (hc0 : 0 < c)
    (hcP : c < p ^ L) (hmod : s ≡ 1 [MOD p ^ (L - c.factorization p)]) :
    ∀ y ∈ digitBox p L c, s * y % p ^ L = y := by
  have hp0 := hp.pos
  have hp1 := hp.one_lt
  have hvL : c.factorization p < L := by
    have h1 : p ^ c.factorization p ≤ c := Nat.ordProj_le p hc0.ne'
    have h2 : p ^ c.factorization p < p ^ L := lt_of_le_of_lt h1 hcP
    exact (Nat.pow_lt_pow_iff_right hp1).mp h2
  have hm1 : 1 < p ^ (L - c.factorization p) := Nat.one_lt_pow (by omega) hp1
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · exfalso
      have h0 : 0 % p ^ (L - c.factorization p) = 1 % p ^ (L - c.factorization p) := hmod
      rw [Nat.zero_mod, Nat.mod_eq_of_lt hm1] at h0
      omega
    · exact h
  have hdvd_s : p ^ (L - c.factorization p) ∣ s - 1 :=
    (Nat.modEq_iff_dvd' hs1).mp hmod.symm
  intro y hy
  have hcd : ∀ i < c.factorization p, c / p ^ i % p = 0 :=
    (pow_dvd_iff_digits_zero hp0 _ c).mp (Nat.ordProj_dvd c p)
  have hyd : ∀ i < c.factorization p, y / p ^ i % p = 0 := by
    intro i hi
    have h := (mem_digitBox.mp hy).2 i (by omega)
    rw [hcd i hi] at h
    omega
  have hdvd_y : p ^ c.factorization p ∣ y :=
    (pow_dvd_iff_digits_zero hp0 _ y).mpr hyd
  have hPL : p ^ L ∣ (s - 1) * y := by
    have h := mul_dvd_mul hdvd_s hdvd_y
    rwa [← pow_add, Nat.sub_add_cancel hvL.le] at h
  obtain ⟨k, hk⟩ := hPL
  have hsy : s * y = p ^ L * k + y := by
    have hexp : (s - 1) * y + y = s * y := by
      have h := (Nat.sub_add_cancel hs1)
      calc (s - 1) * y + y = ((s - 1) + 1) * y := by ring
        _ = s * y := by rw [h]
    omega
  rw [hsy, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (le_of_mem_digitBox p hp0 L c y hy) hcP)

/- ### Converse, base case `L = 1` (sum argument) -/

/-- Base case of the converse: if multiplication by `s` maps `{1, …, c}`
into itself modulo a prime `p` with `c + 1 < p`, then `s ≡ 1 [MOD p]`. -/
lemma stabilizer_converse_base (p c s : ℕ) (hp : p.Prime) (hc0 : 0 < c)
    (hcp : c + 1 < p) (hs : Nat.Coprime s p)
    (h : ∀ y ∈ Finset.Icc 1 c, 1 ≤ s * y % p ∧ s * y % p ≤ c) :
    s ≡ 1 [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `y ↦ s * y % p` is injective on `{1, …, c}`.
  have hinj : ∀ x ∈ Finset.Icc 1 c, ∀ y ∈ Finset.Icc 1 c,
      s * x % p = s * y % p → x = y := by
    intro x hx y hy hxy
    rw [Finset.mem_Icc] at hx hy
    have hmod : x ≡ y [MOD p] := Nat.ModEq.cancel_left_of_coprime hs.symm hxy
    have heq : x % p = y % p := hmod
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
  -- Its image is contained in `{1, …, c}`, hence equals it.
  have hsub : (Finset.Icc 1 c).image (fun y => s * y % p) ⊆ Finset.Icc 1 c := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1, h2⟩ := h y hy
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hcard : ((Finset.Icc 1 c).image (fun y => s * y % p)).card
      = (Finset.Icc 1 c).card :=
    Finset.card_image_of_injOn fun x hx y hy hxy => hinj x hx y hy hxy
  have himg : (Finset.Icc 1 c).image (fun y => s * y % p) = Finset.Icc 1 c :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  -- Hence the two sums agree in `ℕ`.
  have hsum : ∑ y ∈ Finset.Icc 1 c, (s * y % p) = ∑ y ∈ Finset.Icc 1 c, y := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (fun x hx y hy hxy => hinj x hx y hy hxy)]
  -- Gauss sum: `(∑_{1}^{c} y) * 2 = (c+1) * c`.
  have hr : Finset.range (c + 1) = insert 0 (Finset.Icc 1 c) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0notin : (0 : ℕ) ∉ Finset.Icc 1 c := by simp
  have hN2 : (∑ y ∈ Finset.Icc 1 c, y) * 2 = (c + 1) * c := by
    have hg := Finset.sum_range_id_mul_two (c + 1)
    rw [hr, Finset.sum_insert h0notin] at hg
    simpa using hg
  -- Transfer to `ZMod p`: `(s - 1) * T = 0` with `T` the Gauss sum.
  have hZ : ((s : ZMod p) - 1) * ((∑ y ∈ Finset.Icc 1 c, y : ℕ) : ZMod p) = 0 := by
    have e1 : ((∑ y ∈ Finset.Icc 1 c, (s * y % p) : ℕ) : ZMod p)
        = (s : ZMod p) * ((∑ y ∈ Finset.Icc 1 c, y : ℕ) : ZMod p) := by
      rw [Nat.cast_sum, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [ZMod.natCast_mod, Nat.cast_mul]
    have e2 : ((∑ y ∈ Finset.Icc 1 c, (s * y % p) : ℕ) : ZMod p)
        = ((∑ y ∈ Finset.Icc 1 c, y : ℕ) : ZMod p) := by rw [hsum]
    rw [sub_mul, one_mul, ← e1, e2, sub_self]
  -- The Gauss sum is a unit: `p ∤ c` and `p ∤ c + 1`.
  have hTne : ((∑ y ∈ Finset.Icc 1 c, y : ℕ) : ZMod p) ≠ 0 := by
    intro hT0
    have h2 : (((∑ y ∈ Finset.Icc 1 c, y) * 2 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_mul, hT0, zero_mul]
    rw [hN2] at h2
    have hdvd : p ∣ (c + 1) * c := (ZMod.natCast_eq_zero_iff _ _).mp h2
    rcases hp.dvd_mul.mp hdvd with hd | hd
    · have := Nat.le_of_dvd (by omega) hd
      omega
    · have := Nat.le_of_dvd hc0 hd
      omega
  have hs1 : (s : ZMod p) - 1 = 0 := by
    rcases mul_eq_zero.mp hZ with h' | h'
    · exact h'
    · exact absurd h' hTne
  have hcast : (s : ZMod p) = ((1 : ℕ) : ZMod p) := by
    rw [Nat.cast_one]
    exact sub_eq_zero.mp hs1
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast

/- ### Converse direction: helpers -/

/-- Descent of the stabilizer hypothesis: the hypothesis at level `L + 1`
for `c` (restricted to the multiples of `p` in the box) yields the analogous
hypothesis at level `L` for `c / p`. -/
lemma box_hyp_div {p : ℕ} (hp : 0 < p) (L c s : ℕ)
    (hbox : ∀ y ∈ digitBox p (L + 1) c, y ≠ 0 →
      1 ≤ s * y % p ^ (L + 1) ∧ s * y % p ^ (L + 1) ≤ c) :
    ∀ z ∈ digitBox p L (c / p), z ≠ 0 →
      1 ≤ s * z % p ^ L ∧ s * z % p ^ L ≤ c / p := by
  intro z hz hz0
  have hy : p * z ∈ digitBox p (L + 1) c := by
    rw [mem_digitBox_low hp]
    constructor
    · simp [Nat.mul_mod_right]
    · rwa [Nat.mul_div_cancel_left z hp]
  have hy0 : p * z ≠ 0 := Nat.mul_ne_zero hp.ne' hz0
  obtain ⟨h1, h2⟩ := hbox _ hy hy0
  have hmod : s * (p * z) % p ^ (L + 1) = p * (s * z % p ^ L) := by
    rw [pow_succ' p L, show s * (p * z) = p * (s * z) by ring, Nat.mul_mod_mul_left]
  rw [hmod] at h1 h2
  constructor
  · rcases Nat.eq_zero_or_pos (s * z % p ^ L) with h0 | h0
    · rw [h0, Nat.mul_zero] at h1
      omega
    · exact h0
  · refine (Nat.le_div_iff_mul_le hp).mpr ?_
    rwa [mul_comm _ p]

/-- `ord_p (p * C) = ord_p C + 1` for a prime `p` and `C ≠ 0`. -/
lemma factorization_p_mul {p : ℕ} (hp : p.Prime) {C : ℕ} (hC : C ≠ 0) :
    (p * C).factorization p = C.factorization p + 1 := by
  rw [Nat.factorization_mul hp.pos.ne' hC, Finsupp.add_apply, hp.factorization_self]
  omega

/- ### Converse direction: strong induction on the number of digits -/

/-- Converse direction of the stabilizer theorem, for `s` already reduced
modulo `p^L`: strong induction on `L`. -/
lemma stabilizer_converse (p : ℕ) (hp : p.Prime) :
    ∀ L, 1 ≤ L → ∀ c s, 0 < c → c < p ^ L - p ^ L / p → Nat.Coprime s p →
      s < p ^ L →
      (∀ y ∈ digitBox p L c, y ≠ 0 → 1 ≤ s * y % p ^ L ∧ s * y % p ^ L ≤ c) →
      s ≡ 1 [MOD p ^ (L - c.factorization p)] := by
  have hp0 := hp.pos
  intro L
  induction L using Nat.strong_induction_on with
  | _ L IH =>
  intro hL c s hc0 hc hs hsP hbox
  obtain _ | N := L
  · exact absurd hL (by omega)
  rcases Nat.eq_zero_or_pos N with rfl | hN1
  · -- Base case `L = 1`: the sum argument.
    simp only [Nat.zero_add] at hc hbox ⊢
    rw [pow_one, Nat.div_self hp0] at hc
    -- `hc : c < p - 1`
    have hford : c.factorization p = 0 := Nat.factorization_eq_zero_of_lt (by omega)
    rw [hford, Nat.sub_zero, pow_one]
    apply stabilizer_converse_base p c s hp hc0 (by omega) hs
    intro y hy
    rw [Finset.mem_Icc] at hy
    have hybox : y ∈ digitBox p 1 c := by
      rw [digitBox_one (show c < p by omega), Finset.mem_Iic]
      exact hy.2
    have h := hbox y hybox (by omega)
    rwa [pow_one] at h
  -- Inductive step: `L = N + 1` with `N ≥ 1`.  Put `P' = p^N`, `P = p·P'`.
  have hP'pos : 0 < p ^ N := pow_pos hp0 N
  have hpdvd : p ∣ p ^ N := dvd_pow_self p hN1.ne'
  have hB : p ^ (N + 1) = p * p ^ N := pow_succ' p N
  have hBp : p ^ (N + 1) / p = p ^ N := by
    rw [hB, Nat.mul_div_cancel_left _ hp0]
  have hA : p * (p ^ N / p) = p ^ N := Nat.mul_div_cancel' hpdvd
  have hppN : p ≤ p ^ N := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ N := Nat.pow_le_pow_right hp0 hN1
  have hcdm : p * (c / p) + c % p = c := Nat.div_add_mod c p
  have hcm : c % p < p := Nat.mod_lt _ hp0
  -- The digit bound passes to `C = c / p`.
  have hCb : c / p < p ^ N - p ^ N / p := by
    have hmul : p * (c / p) < p * (p ^ N - p ^ N / p) := by
      calc p * (c / p) ≤ c := Nat.le.intro hcdm
        _ < p ^ (N + 1) - p ^ (N + 1) / p := hc
        _ = p * (p ^ N - p ^ N / p) := by rw [Nat.mul_sub, hA, ← hB, hBp]
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hCP' : c / p < p ^ N := lt_of_lt_of_le hCb (Nat.sub_le _ _)
  -- Descended box hypothesis, and the inductive congruence for `s`.
  have hdesc := box_hyp_div hp0 N c s hbox
  have hkey : 0 < c / p → s ≡ 1 [MOD p ^ (N - (c / p).factorization p)] := by
    intro hC0
    have hs' : Nat.Coprime (s % p ^ N) p := by
      have h1 : ¬p ∣ s := (Nat.Prime.coprime_iff_not_dvd hp).mp hs.symm
      have h2 : ¬p ∣ s % p ^ N := fun hd => h1 ((Nat.dvd_mod_iff hpdvd).mp hd)
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr h2).symm
    have hs'P : s % p ^ N < p ^ N := Nat.mod_lt _ hP'pos
    have hbox' : ∀ z ∈ digitBox p N (c / p), z ≠ 0 →
        1 ≤ s % p ^ N * z % p ^ N ∧ s % p ^ N * z % p ^ N ≤ c / p := by
      intro z hz hz0
      rw [Nat.mod_mul_mod]
      exact hdesc z hz hz0
    have hIH := IH N (Nat.lt_succ_self N) hN1 (c / p) (s % p ^ N)
      hC0 hCb hs' hs'P hbox'
    exact (Nat.ModEq.of_dvd (pow_dvd_pow p (Nat.sub_le _ _))
      (Nat.mod_modEq s (p ^ N)).symm).trans hIH
  rcases Nat.eq_zero_or_pos (c % p) with hc0p | hc0p
  · -- Subcase `c ≡ 0 (mod p)`: pass directly to the inductive congruence.
    have hC0 : 0 < c / p :=
      Nat.div_pos (Nat.le_of_dvd hc0 (Nat.dvd_of_mod_eq_zero hc0p)) hp0
    have hceq : p * (c / p) = c := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc0p)
    have hford : c.factorization p = (c / p).factorization p + 1 := by
      conv_lhs => rw [← hceq]
      exact factorization_p_mul hp hC0.ne'
    have hgoal := hkey hC0
    have hexp : N + 1 - c.factorization p = N - (c / p).factorization p := by omega
    rwa [hexp]
  · -- Subcase `c ≢ 0 (mod p)`: here `ord_p c = 0`, and we show `s = 1`.
    have hford : c.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      have := Nat.dvd_iff_mod_eq_zero.mp hdvd
      omega
    rw [hford, Nat.sub_zero]
    suffices hs1 : s = 1 by subst hs1; rfl
    -- (i) `s` fixes every element of the lower box `𝒟_C` modulo `p^N`.
    have hsz : ∀ z ∈ digitBox p N (c / p), s * z % p ^ N = z := by
      rcases Nat.eq_zero_or_pos (c / p) with hC0 | hC0
      · intro z hz
        rw [hC0, digitBox_c_zero p N hp0, Finset.mem_singleton] at hz
        subst hz
        rw [Nat.mul_zero, Nat.zero_mod]
      · exact stabilizer_forward p N (c / p) s hp hC0 hCP' (hkey hC0)
    -- Decompose `s = p·S + s₀` with `1 ≤ s₀ < p` and `S < p^N`.
    have hs0m : 0 < s % p := by
      rcases Nat.eq_zero_or_pos (s % p) with h0 | h0
      · exact absurd (Nat.dvd_of_mod_eq_zero h0)
          ((Nat.Prime.coprime_iff_not_dvd hp).mp hs.symm)
      · exact h0
    have hSm : s / p < p ^ N := by
      rw [Nat.div_lt_iff_lt_mul hp0]
      calc s < p ^ (N + 1) := hsP
        _ = p ^ N * p := pow_succ p N
    obtain ⟨S, s₀, rfl, hs0lt, hs0pos, hSlt⟩ :
        ∃ S s₀, s = p * S + s₀ ∧ s₀ < p ∧ 0 < s₀ ∧ S < p ^ N :=
      ⟨s / p, s % p, (Nat.div_add_mod s p).symm, Nat.mod_lt _ hp0, hs0m, hSm⟩
    -- (ii) The translation `R_a = (e_a + S·a) mod p^N` vanishes for
    -- every `a ∈ [1, c₀]`, by the no-nonzero-translation lemma.
    have hRa : ∀ a, 1 ≤ a → a ≤ c % p → p ^ N ∣ s₀ * a / p + S * a := by
      intro a ha1 hac
      have halt : a < p := lt_of_le_of_lt hac hcm
      have herd : p * (s₀ * a / p) + s₀ * a % p = s₀ * a := Nat.div_add_mod _ p
      have hrlt : s₀ * a % p < p := Nat.mod_lt _ hp0
      set R := (s₀ * a / p + S * a) % p ^ N with hR
      have hRlt : R < p ^ N := Nat.mod_lt _ hP'pos
      have hmain : ∀ z ∈ digitBox p N (c / p), (z + R) % p ^ N ≤ c / p := by
        intro z hz
        have hyc : a + p * z ∈ digitBox p (N + 1) c := by
          rw [mem_digitBox_low hp0]
          constructor
          · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt halt]
            exact hac
          · rwa [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt halt, Nat.zero_add]
        have hy0 : a + p * z ≠ 0 := (Nat.add_pos_left (by omega) _).ne'
        obtain ⟨-, h2⟩ := hbox _ hyc hy0
        have hsy : (p * S + s₀) * (a + p * z)
            = s₀ * a % p + p * (s₀ * a / p + S * a + (p * S + s₀) * z) := by
          calc (p * S + s₀) * (a + p * z)
              = s₀ * a + p * (S * a + (p * S + s₀) * z) := by ring
            _ = (p * (s₀ * a / p) + s₀ * a % p)
                + p * (S * a + (p * S + s₀) * z) := by rw [herd]
            _ = s₀ * a % p + p * (s₀ * a / p + S * a + (p * S + s₀) * z) := by
                ring
        rw [hsy, hB, low_high_mod hp0 hP'pos _ _ hrlt] at h2
        have hinner : (s₀ * a / p + S * a + (p * S + s₀) * z) % p ^ N
            = (z + R) % p ^ N := by
          rw [Nat.add_mod (s₀ * a / p + S * a) ((p * S + s₀) * z), hsz z hz,
            ← hR, Nat.add_comm R z]
        rw [hinner] at h2
        -- `r + p·((z+R) mod p^N) ≤ c` forces `(z+R) mod p^N ≤ C`.
        have hple : p * ((z + R) % p ^ N) < p * (c / p + 1) := by
          calc p * ((z + R) % p ^ N) ≤ c := le_trans (Nat.le_add_left _ _) h2
            _ < p * (c / p + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hple)
      have hR0 : R ≤ c / p := by
        have h := hmain 0 (zero_mem_digitBox p N (c / p) hp0)
        rwa [Nat.zero_add, Nat.mod_eq_of_lt hRlt] at h
      have hRzero : R = 0 :=
        no_nonzero_translation p N (c / p) R hp hN1 hCb hR0 hmain
      rw [hR] at hRzero
      exact Nat.dvd_of_mod_eq_zero hRzero
    -- (iii) `a = 1` gives `S = 0`; then no low digit ever carries.
    have hS0 : S = 0 := by
      have h1 := hRa 1 le_rfl hc0p
      rw [Nat.mul_one, Nat.mul_one, Nat.div_eq_of_lt hs0lt, Nat.zero_add] at h1
      exact Nat.eq_zero_of_dvd_of_lt h1 hSlt
    subst hS0
    have hcar : ∀ a, 1 ≤ a → a ≤ c % p → s₀ * a < p := by
      intro a ha1 hac
      have halt : a < p := lt_of_le_of_lt hac hcm
      have h := hRa a ha1 hac
      rw [Nat.zero_mul, Nat.add_zero] at h
      have hdlt : s₀ * a / p < p ^ N := by
        have h1 : s₀ * a / p < p := by
          apply Nat.div_lt_of_lt_mul
          calc s₀ * a < p * a := mul_lt_mul_of_pos_right hs0lt (by omega)
            _ < p * p := mul_lt_mul_of_pos_left halt hp0
        exact lt_of_lt_of_le h1 hppN
      have h0 : s₀ * a / p = 0 := Nat.eq_zero_of_dvd_of_lt h hdlt
      have hd := Nat.div_add_mod (s₀ * a) p
      rw [h0, Nat.mul_zero, Nat.zero_add] at hd
      rw [← hd]
      exact Nat.mod_lt _ hp0
    -- (iv) Evaluate the hypothesis at `y = c` to force `s₀ = 1`.
    have hsc : s₀ * (c % p) < p := hcar (c % p) hc0p le_rfl
    have hccP : c < p ^ (N + 1) := lt_of_lt_of_le hc (Nat.sub_le _ _)
    obtain ⟨-, h2⟩ := hbox c (self_mem_digitBox hccP) hc0.ne'
    have hsC : (p * 0 + s₀) * (c / p) % p ^ N = c / p :=
      hsz (c / p) (self_mem_digitBox hCP')
    have hcalc : (p * 0 + s₀) * c
        = s₀ * (c % p) + p * ((p * 0 + s₀) * (c / p)) := by
      calc (p * 0 + s₀) * c = s₀ * c := by ring
        _ = s₀ * (p * (c / p) + c % p) := by rw [hcdm]
        _ = s₀ * (c % p) + p * ((p * 0 + s₀) * (c / p)) := by ring
    rw [hcalc, hB, low_high_mod hp0 hP'pos _ _ hsc, hsC] at h2
    -- `h2 : s₀·c₀ + p·C ≤ c = p·C + c₀`, hence `s₀·c₀ ≤ c₀`, hence `s₀ = 1`.
    have hfin : s₀ * (c % p) ≤ c % p := by omega
    have hle1 : s₀ ≤ 1 := by
      have h1 : s₀ * (c % p) ≤ 1 * (c % p) := by rwa [Nat.one_mul]
      exact Nat.le_of_mul_le_mul_right h1 hc0p
    omega

/-- **Theorem (Digit-box stabilizer)**.
"Let `P = p^L` and `0 < c < P − P/p`.  Let `s` be coprime to `p`.  Then
`[sy]_P ∈ {1, …, c}` for every `y ∈ 𝒟_c \ {0}`
if and only if `s ≡ 1 (mod p^(L − ord_p(c)))`."

Encoding: `ord_p(c) = c.factorization p` (well-defined since `c > 0`). -/
theorem digitBox_stabilizer (p L c s : ℕ) (hp : p.Prime) (hL : 1 ≤ L)
    (hc0 : 0 < c) (hc : c < p ^ L - p ^ L / p) (hs : Nat.Coprime s p) :
    (∀ y ∈ digitBox p L c, y ≠ 0 →
        1 ≤ s * y % p ^ L ∧ s * y % p ^ L ≤ c) ↔
      s ≡ 1 [MOD p ^ (L - c.factorization p)] := by
  have hp0 := hp.pos
  have hcP : c < p ^ L := lt_of_lt_of_le hc (Nat.sub_le _ _)
  constructor
  · -- Reduce `s` modulo `p^L`, then apply the inductive converse.
    intro hbox
    have hpdvd : p ∣ p ^ L := dvd_pow_self p (by omega : L ≠ 0)
    have hs' : Nat.Coprime (s % p ^ L) p := by
      have h1 : ¬p ∣ s := (Nat.Prime.coprime_iff_not_dvd hp).mp hs.symm
      have h2 : ¬p ∣ s % p ^ L := fun hd => h1 ((Nat.dvd_mod_iff hpdvd).mp hd)
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr h2).symm
    have hs'lt : s % p ^ L < p ^ L := Nat.mod_lt _ (pow_pos hp0 L)
    have hbox' : ∀ y ∈ digitBox p L c, y ≠ 0 →
        1 ≤ s % p ^ L * y % p ^ L ∧ s % p ^ L * y % p ^ L ≤ c := by
      intro y hy hy0
      rw [Nat.mod_mul_mod]
      exact hbox y hy hy0
    have h1 := stabilizer_converse p hp L hL c (s % p ^ L) hc0 hc hs' hs'lt hbox'
    have h2 : s ≡ s % p ^ L [MOD p ^ (L - c.factorization p)] :=
      Nat.ModEq.of_dvd (pow_dvd_pow p (Nat.sub_le _ _)) (Nat.mod_modEq s _).symm
    exact h2.trans h1
  · -- Forward direction: multiplication by `s` fixes the box pointwise.
    intro hmod y hy hy0
    have heq := stabilizer_forward p L c s hp hc0 hcP hmod y hy
    rw [heq]
    exact ⟨Nat.one_le_iff_ne_zero.mpr hy0, le_of_mem_digitBox p hp0 L c y hy⟩


/- ## The zero-run lemma (Section 5) -/

/-- Peel the lowest base-`p` digit off `m % p^(j+1)`. -/
lemma mod_pow_succ {p : ℕ} (hp : 0 < p) (j m : ℕ) :
    m % p ^ (j + 1) = m % p + p * (m / p % p ^ j) := by
  have hP : 0 < p ^ j := pow_pos hp j
  conv_lhs => rw [← Nat.mod_add_div m p]
  rw [pow_succ' p j]
  exact low_high_mod hp hP (m % p) (m / p) (Nat.mod_lt _ hp)

/-- For `m, r < p^L`, membership of `r` in the digit box of `c = p^L - 1 - m`
is equivalent to the base-`p` addition `m + r` being carry-free. -/
lemma noCarry_iff_mem_box {p : ℕ} (hp2 : 2 ≤ p) :
    ∀ L m r, m < p ^ L → r < p ^ L →
      (r ∈ digitBox p L (p ^ L - 1 - m) ↔ ∀ i, m % p ^ i + r % p ^ i < p ^ i) := by
  have hp0 : 0 < p := by omega
  intro L
  induction L with
  | zero =>
    intro m r hm hr
    simp only [pow_zero] at hm hr
    have hm0 : m = 0 := by omega
    have hr0 : r = 0 := by omega
    subst hm0; subst hr0
    constructor
    · intro _ i
      simpa using pow_pos hp0 i
    · intro _
      have he : p ^ 0 - 1 - 0 = 0 := by norm_num
      rw [he]
      exact zero_mem_digitBox p 0 0 hp0
  | succ L IH =>
    intro m r hm hr
    have hP : 0 < p ^ L := pow_pos hp0 L
    have hPP : p ^ (L + 1) = p * p ^ L := pow_succ' p L
    have hmp : m / p < p ^ L := by
      rw [Nat.div_lt_iff_lt_mul hp0]
      calc m < p ^ (L + 1) := hm
        _ = p ^ L * p := pow_succ p L
    have hrp : r / p < p ^ L := by
      rw [Nat.div_lt_iff_lt_mul hp0]
      calc r < p ^ (L + 1) := hr
        _ = p ^ L * p := pow_succ p L
    have hmodm : m % p < p := Nat.mod_lt _ hp0
    -- digit decomposition of `c = p^(L+1) - 1 - m`
    have hkeyc : p ^ (L + 1) - 1 - m = (p - 1 - m % p) + p * (p ^ L - 1 - m / p) := by
      have e1 : p * (p ^ L - 1 - m / p) = p * p ^ L - p - p * (m / p) := by
        rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_one]
      have e2 : p * (m / p) + m % p = m := Nat.div_add_mod m p
      have e3 : p * (m / p) + p ≤ p * p ^ L := by
        have h4 := Nat.mul_le_mul_left p (show m / p + 1 ≤ p ^ L from hmp)
        rw [Nat.mul_add, Nat.mul_one] at h4
        exact h4
      rw [e1]
      omega
    have hcmod : (p ^ (L + 1) - 1 - m) % p = p - 1 - m % p := by
      rw [hkeyc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hcdiv : (p ^ (L + 1) - 1 - m) / p = p ^ L - 1 - m / p := by
      rw [hkeyc, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    rw [mem_digitBox_low hp0, hcmod, hcdiv, IH (m / p) (r / p) hmp hrp]
    constructor
    · rintro ⟨h1, h2⟩ i
      cases i with
      | zero => simp only [pow_zero, Nat.mod_one]; omega
      | succ j =>
        rw [mod_pow_succ hp0 j m, mod_pow_succ hp0 j r, pow_succ' p j]
        have hXY := h2 j
        have hmul : p * (m / p % p ^ j) + p * (r / p % p ^ j) + p ≤ p * p ^ j := by
          have h4 := Nat.mul_le_mul_left p
            (show m / p % p ^ j + (r / p % p ^ j) + 1 ≤ p ^ j from hXY)
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at h4
          omega
        omega
    · intro hcar
      constructor
      · have h1 := hcar 1
        rw [pow_one] at h1
        omega
      · intro j
        have hj := hcar (j + 1)
        rw [mod_pow_succ hp0 j m, mod_pow_succ hp0 j r, pow_succ' p j] at hj
        by_contra hcon
        push Not at hcon
        have h4 := Nat.mul_le_mul_left p hcon
        rw [Nat.mul_add] at h4
        omega

/-- Kummer-style criterion: `p ∤ C(m+x, m)` iff the base-`p` addition of `m`
and `x` is carry-free (all partial mod-sums stay below `p^i`). -/
lemma not_dvd_choose_iff_no_carry {p : ℕ} (hp : p.Prime) (m x : ℕ) :
    ¬ p ∣ Nat.choose (m + x) m ↔ ∀ i, m % p ^ i + x % p ^ i < p ^ i := by
  have hpos : 0 < Nat.choose (m + x) m := Nat.choose_pos (Nat.le_add_right m x)
  have hb : Nat.log p (x + m) < m + x + 1 := by
    apply Nat.log_lt_of_lt_pow' (by omega)
    calc x + m < 2 ^ (x + m) := Nat.lt_two_pow_self
      _ ≤ 2 ^ (m + x + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ p ^ (m + x + 1) := Nat.pow_le_pow_left hp.two_le _
  have hfac := Nat.factorization_choose' hp hb
  have hdvd : p ∣ Nat.choose (m + x) m ↔ ∃ i, p ^ i ≤ m % p ^ i + x % p ^ i := by
    rw [hp.dvd_iff_one_le_factorization hpos.ne',
      show m + x = x + m from Nat.add_comm m x, hfac]
    constructor
    · intro hcard
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
      rw [Finset.mem_filter] at hi
      exact ⟨i, hi.2⟩
    · rintro ⟨i, hi⟩
      apply Finset.card_pos.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, hi⟩⟩
      · rcases Nat.eq_zero_or_pos i with rfl | h
        · simp only [pow_zero] at hi; omega
        · exact h
      · have h1 : i < 2 ^ i := Nat.lt_two_pow_self
        have h2 : 2 ^ i ≤ p ^ i := Nat.pow_le_pow_left hp.two_le i
        have h3 : m % p ^ i ≤ m := Nat.mod_le m _
        have h4 : x % p ^ i ≤ x := Nat.mod_le x _
        omega
  rw [hdvd]
  simp only [not_exists, not_le]

/-- Splitting a residue mod `P * Q` into a high block and a residue mod `P`. -/
lemma mod_mul_decomp (P Q x : ℕ) :
    x % (P * Q) = P * (x / P % Q) + x % P := by
  conv_lhs => rw [← Nat.div_add_mod (x % (P * Q)) P]
  rw [Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd x (dvd_mul_right P Q)]

/-- The key equivalence of Part 1: `p ∤ C(m+x, m)` iff the residue of `x`
mod `p^L` lies in the digit box of `c = p^L - 1 - m`. -/
lemma not_dvd_choose_iff_mem_box {p : ℕ} (hp : p.Prime) (L m x : ℕ)
    (hm : m < p ^ L) :
    ¬ p ∣ Nat.choose (m + x) m ↔ x % p ^ L ∈ digitBox p L (p ^ L - 1 - m) := by
  have hp0 := hp.pos
  have hP : 0 < p ^ L := pow_pos hp0 L
  have hr : x % p ^ L < p ^ L := Nat.mod_lt x hP
  rw [not_dvd_choose_iff_no_carry hp, noCarry_iff_mem_box hp.two_le L m (x % p ^ L) hm hr]
  constructor
  · intro hcar i
    rcases le_or_gt i L with hiL | hiL
    · rw [Nat.mod_mod_of_dvd x (pow_dvd_pow p hiL)]
      exact hcar i
    · have hPi : p ^ L ≤ p ^ i := Nat.pow_le_pow_right hp0 hiL.le
      have h1 : m % p ^ i = m := Nat.mod_eq_of_lt (lt_of_lt_of_le hm hPi)
      have h2 : x % p ^ L % p ^ i = x % p ^ L := Nat.mod_eq_of_lt (lt_of_lt_of_le hr hPi)
      have h3 := hcar L
      rw [Nat.mod_eq_of_lt hm] at h3
      rw [h1, h2]
      omega
  · intro hbox i
    rcases le_or_gt i L with hiL | hiL
    · have h := hbox i
      rwa [Nat.mod_mod_of_dvd x (pow_dvd_pow p hiL)] at h
    · have hQ : 0 < p ^ (i - L) := pow_pos hp0 _
      have hpi : p ^ i = p ^ L * p ^ (i - L) := by
        rw [← pow_add]
        congr 1
        omega
      have hdec : x % p ^ i = p ^ L * (x / p ^ L % p ^ (i - L)) + x % p ^ L := by
        rw [hpi]
        exact mod_mul_decomp _ _ _
      have hW : x / p ^ L % p ^ (i - L) < p ^ (i - L) := Nat.mod_lt _ hQ
      have hbL := hbox L
      rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hm] at hbL
      have hmul : p ^ L * (x / p ^ L % p ^ (i - L)) + p ^ L ≤ p ^ L * p ^ (i - L) := by
        have h4 := Nat.mul_le_mul_left (p ^ L)
          (show x / p ^ L % p ^ (i - L) + 1 ≤ p ^ (i - L) from hW)
        rw [Nat.mul_add, Nat.mul_one] at h4
        exact h4
      have hPle : p ^ L ≤ p ^ i := Nat.pow_le_pow_right hp0 (by omega)
      have h1 : m % p ^ i = m := Nat.mod_eq_of_lt (lt_of_lt_of_le hm hPle)
      rw [h1, hdec, hpi]
      omega

/-- **Lemma (Zero-run lemma)**.
"Let `p` be prime, let `m ≥ 1`, and let `M` be coprime to `p`.  Assume
`p ∤ m+1`.  Let `P = p^L` be the least power of `p` satisfying `m < P`.
If `C(m + tM, m) ≡ 0 (mod p)` for `t = 1, …, m`, then `M ≡ −1 (mod P)`."

Encoding: minimality of `P = p^L` is expressed by `p^(L−1) ≤ m < p^L`
(note `m ≥ 1` then forces `L ≥ 1`); the conclusion `M ≡ −1 (mod P)` is
stated in `ZMod (p^L)`. -/
theorem zero_run (p m M L : ℕ) (hp : p.Prime) (hm : 1 ≤ m)
    (hM : Nat.Coprime M p) (hm1 : ¬ p ∣ m + 1)
    (hLm : p ^ (L - 1) ≤ m) (hmL : m < p ^ L)
    (h : ∀ t ∈ Finset.Icc 1 m, p ∣ Nat.choose (m + t * M) m) :
    (M : ZMod (p ^ L)) = -1 := by
  have hp0 := hp.pos
  have hL : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · rw [pow_zero] at hmL; omega
    · exact hL
  have hPpos : 0 < p ^ L := pow_pos hp0 L
  have hP1 : 1 < p ^ L := Nat.one_lt_pow (by omega) hp.one_lt
  haveI : NeZero (p ^ L) := ⟨hPpos.ne'⟩
  have hpdvdP : p ∣ p ^ L := dvd_pow_self p (by omega)
  set c : ℕ := p ^ L - 1 - m with hc_def
  have hcm : c + (m + 1) = p ^ L := by omega
  have hpc : ¬ p ∣ c := by
    intro hdvd
    apply hm1
    have h1 : p ∣ c + (m + 1) := by rw [hcm]; exact hpdvdP
    exact (Nat.dvd_add_right hdvd).mp h1
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exact absurd (by rw [h0]; exact dvd_zero p : p ∣ c) hpc
    · exact h0
  have hcP : c < p ^ L := by omega
  have hcfact : c.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpc
  have hPp : p ^ L / p = p ^ (L - 1) := by
    have h1 := Nat.pow_div hL hp0
    rwa [pow_one] at h1
  have hcband : c < p ^ L - p ^ L / p := by
    rw [hPp]
    have h1 : 0 < p ^ (L - 1) := pow_pos hp0 _
    omega
  -- Part 1: the box hypothesis from Lucas/Kummer.
  have hbox : ∀ t ∈ Finset.Icc 1 m, (t * M) % p ^ L ∉ digitBox p L c := by
    intro t ht hmem
    rw [hc_def] at hmem
    exact ((not_dvd_choose_iff_mem_box hp L m (t * M) hmL).mpr hmem) (h t ht)
  -- Part 2: the inverse of M and the stabilizer.
  have hMP : Nat.Coprime M (p ^ L) := hM.pow_right L
  set u : (ZMod (p ^ L))ˣ := ZMod.unitOfCoprime M hMP with hu_def
  have hu_coe : ((u : (ZMod (p ^ L))ˣ) : ZMod (p ^ L)) = (M : ZMod (p ^ L)) :=
    ZMod.coe_unitOfCoprime M hMP
  set U : ZMod (p ^ L) := ((u⁻¹ : (ZMod (p ^ L))ˣ) : ZMod (p ^ L)) with hU_def
  have hUM : U * (M : ZMod (p ^ L)) = 1 := by
    rw [hU_def, ← hu_coe]
    exact u.inv_mul
  -- The key map: for nonzero `y` in the box, `(U * y).val` lies in `[m+1, P-1]`.
  have hkey : ∀ y : ℕ, y ∈ digitBox p L c → y ≠ 0 →
      m + 1 ≤ (U * (y : ZMod (p ^ L))).val ∧
        (U * (y : ZMod (p ^ L))).val ≤ p ^ L - 1 := by
    intro y hy hy0
    have hyc : y ≤ c := le_of_mem_digitBox p hp0 L c y hy
    have hyP : y < p ^ L := by omega
    set t : ℕ := (U * (y : ZMod (p ^ L))).val with ht_def
    have htP : t < p ^ L := ZMod.val_lt _
    have ht0 : t ≠ 0 := by
      intro h0
      have hz : U * (y : ZMod (p ^ L)) = 0 := (ZMod.val_eq_zero _).mp h0
      have hy' : (y : ZMod (p ^ L)) = 0 := by
        have h1 : (M : ZMod (p ^ L)) * (U * (y : ZMod (p ^ L))) = (y : ZMod (p ^ L)) := by
          rw [← mul_assoc, mul_comm (M : ZMod (p ^ L)) U, hUM, one_mul]
        rw [hz, mul_zero] at h1
        exact h1.symm
      have h2 : p ^ L ∣ y := (ZMod.natCast_eq_zero_iff y (p ^ L)).mp hy'
      have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hy0) h2
      omega
    have htm : t ∉ Finset.Icc 1 m := by
      intro htIcc
      refine hbox t htIcc ?_
      have h1 : ((t : ℕ) : ZMod (p ^ L)) = U * (y : ZMod (p ^ L)) := by
        rw [ht_def]
        exact ZMod.natCast_zmod_val _
      have hcast : ((t * M : ℕ) : ZMod (p ^ L)) = (y : ZMod (p ^ L)) := by
        push_cast
        rw [h1, mul_right_comm, hUM, one_mul]
      have hmod : (t * M) % p ^ L = y % p ^ L :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
      rw [hmod, Nat.mod_eq_of_lt hyP]
      exact hy
    simp only [Finset.mem_Icc, not_and, not_le] at htm
    have ht1 : m + 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · exact absurd h0 ht0
      · exact htm h0
    exact ⟨ht1, by omega⟩
  -- `1` lies in the box since `p ∤ c`.
  have h1box : (1 : ℕ) ∈ digitBox p L c := by
    rw [mem_digitBox]
    refine ⟨hP1, fun i hi => ?_⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [pow_zero, Nat.div_one]
      have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
      have h2 : c % p ≠ 0 := fun h0 => hpc (Nat.dvd_of_mod_eq_zero h0)
      omega
    · have hpi : 1 < p ^ i := Nat.one_lt_pow hi0.ne' hp.one_lt
      rw [Nat.div_eq_of_lt hpi]
      simp
  -- Hence `U.val ∈ [m+1, P-1]`; set `s := P - U.val ∈ [1, c]`.
  have hUv := hkey 1 h1box one_ne_zero
  rw [Nat.cast_one, mul_one] at hUv
  have hUvP : U.val < p ^ L := ZMod.val_lt U
  set s : ℕ := p ^ L - U.val with hs_def
  have hs1 : 1 ≤ s := by omega
  have hsc : s ≤ c := by omega
  have hs_cast : (s : ZMod (p ^ L)) = -U := by
    rw [hs_def, Nat.cast_sub hUvP.le, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
  -- `s` is coprime to `p`.
  have hUM_nat : U.val * M ≡ 1 [MOD p ^ L] := by
    have hcast : ((U.val * M : ℕ) : ZMod (p ^ L)) = ((1 : ℕ) : ZMod (p ^ L)) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, hUM, Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hps : ¬ p ∣ s := by
    intro hdvd
    have hdU : p ∣ U.val := by
      have heq : U.val = p ^ L - s := by omega
      rw [heq]
      exact Nat.dvd_sub hpdvdP hdvd
    have h1 : U.val * M ≡ 1 [MOD p] := Nat.ModEq.of_dvd hpdvdP hUM_nat
    have h2 : U.val * M % p = 1 % p := h1
    obtain ⟨k, hk⟩ := hdU.mul_right M
    rw [hk, Nat.mul_mod_right, Nat.mod_eq_of_lt hp.one_lt] at h2
    omega
  have hsp : Nat.Coprime s p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hps).symm
  -- The stabilizer hypothesis for `s`.
  have hstab : ∀ y ∈ digitBox p L c, y ≠ 0 →
      1 ≤ s * y % p ^ L ∧ s * y % p ^ L ≤ c := by
    intro y hy hy0
    obtain ⟨ht1, ht2⟩ := hkey y hy hy0
    set z : ZMod (p ^ L) := U * (y : ZMod (p ^ L)) with hz_def
    have hz0 : z ≠ 0 := by
      intro h0
      have hv : z.val = 0 := by rw [h0]; exact ZMod.val_zero
      omega
    have hcast : ((s * y : ℕ) : ZMod (p ^ L)) = -z := by
      rw [Nat.cast_mul, hs_cast, hz_def]
      ring
    have hval : s * y % p ^ L = (-z).val := by
      rw [← ZMod.val_natCast, hcast]
    rw [hval, ZMod.neg_val, if_neg hz0]
    omega
  -- Apply the stabilizer theorem: `s ≡ 1 (mod p^L)`, hence `s = 1`.
  have hsmod : s ≡ 1 [MOD p ^ (L - c.factorization p)] :=
    (digitBox_stabilizer p L c s hp hL hc0 hcband hsp).mp hstab
  rw [hcfact, Nat.sub_zero] at hsmod
  have hs_eq : s = 1 := by
    have h1 : s % p ^ L = 1 % p ^ L := hsmod
    rwa [Nat.mod_eq_of_lt (by omega : s < p ^ L), Nat.mod_eq_of_lt hP1] at h1
  -- Conclude: `U = -1`, hence `M ≡ -1`.
  have hU_eq : U = -1 := by
    have h1 := hs_cast
    rw [hs_eq, Nat.cast_one] at h1
    exact neg_eq_iff_eq_neg.mp h1.symm
  rw [hU_eq, neg_one_mul] at hUM
  exact neg_eq_iff_eq_neg.mp hUM

/- ## The primary criterion (Section 6) -/

/- ### Digit helpers for `p^a - 1` -/

/-- `(p^a − 1) / p^i = p^(a−i) − 1` for `i ≤ a`. -/
lemma pow_sub_one_div_pow {p : ℕ} (hp : 1 ≤ p) {a i : ℕ} (hi : i ≤ a) :
    (p ^ a - 1) / p ^ i = p ^ (a - i) - 1 := by
  have hpi : 0 < p ^ i := pow_pos hp i
  have hX : 0 < p ^ (a - i) := pow_pos hp _
  have hpa : p ^ a = p ^ i * p ^ (a - i) := by
    rw [← pow_add]
    congr 1
    omega
  have hms : p ^ i * p ^ (a - i) = p ^ i * (p ^ (a - i) - 1) + p ^ i := by
    have h1 : p ^ (a - i) - 1 + 1 = p ^ (a - i) := by omega
    calc p ^ i * p ^ (a - i) = p ^ i * (p ^ (a - i) - 1 + 1) := by rw [h1]
      _ = p ^ i * (p ^ (a - i) - 1) + p ^ i := by ring
  have heq : p ^ a - 1 = p ^ i * (p ^ (a - i) - 1) + (p ^ i - 1) := by omega
  rw [heq, Nat.mul_add_div hpi, Nat.div_eq_of_lt (by omega), Nat.add_zero]

/-- `(p^j − 1) % p = p − 1` for `j ≥ 1`. -/
lemma pow_sub_one_mod {p : ℕ} (hp : 2 ≤ p) {j : ℕ} (hj : 1 ≤ j) :
    (p ^ j - 1) % p = p - 1 := by
  have hpj : p ^ j = p * p ^ (j - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hX : 0 < p ^ (j - 1) := pow_pos (by omega) _
  have hms : p * p ^ (j - 1) = p * (p ^ (j - 1) - 1) + p := by
    have h1 : p ^ (j - 1) - 1 + 1 = p ^ (j - 1) := by omega
    calc p * p ^ (j - 1) = p * (p ^ (j - 1) - 1 + 1) := by rw [h1]
      _ = p * (p ^ (j - 1) - 1) + p := by ring
  have heq : p ^ j - 1 = p * (p ^ (j - 1) - 1) + (p - 1) := by omega
  rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- All base-`p` digits of `p^a − 1` below position `a` equal `p − 1`. -/
lemma digit_pow_sub_one {p : ℕ} (hp : 2 ≤ p) {a i : ℕ} (hi : i < a) :
    (p ^ a - 1) / p ^ i % p = p - 1 := by
  rw [pow_sub_one_div_pow (by omega) hi.le]
  exact pow_sub_one_mod hp (by omega)

/-- If all digits of `x` below `a` are `p − 1`, then `x % p^a = p^a − 1`. -/
lemma mod_pow_eq_of_digits {p : ℕ} (hp : p.Prime) (a x : ℕ)
    (h : ∀ i < a, x / p ^ i % p = p - 1) : x % p ^ a = p ^ a - 1 := by
  have hP : 0 < p ^ a := pow_pos hp.pos a
  have hmem : p ^ a - 1 ∈ digitBox p a (x % p ^ a) := by
    rw [mem_digitBox]
    refine ⟨by omega, fun i hi => ?_⟩
    have h1 : (p ^ a - 1) / p ^ i % p = p - 1 := digit_pow_sub_one hp.two_le hi
    have h2 : x % p ^ a / p ^ i % p = p - 1 := by
      rw [digit_mod_pow p a i x hi]
      exact h i hi
    omega
  have hle := le_of_mem_digitBox p hp.pos a (x % p ^ a) (p ^ a - 1) hmem
  have hlt : x % p ^ a < p ^ a := Nat.mod_lt _ hP
  omega

/-- Conversely, if `x % p^a = p^a − 1` then all digits of `x` below `a`
are `p − 1`. -/
lemma digits_of_mod_pow {p : ℕ} (hp : 2 ≤ p) (a x : ℕ)
    (hx : x % p ^ a = p ^ a - 1) :
    ∀ i < a, x / p ^ i % p = p - 1 := by
  intro i hi
  rw [← digit_mod_pow p a i x hi, hx]
  exact digit_pow_sub_one hp hi

/- ### Iterated Lucas congruence when the low digits all agree at `p − 1` -/

/-- If all digits of `N` and `K` below `a` equal `p − 1`, then
`C(N, K) ≡ C(N / p^a, K / p^a) (mod p)`. -/
lemma choose_modEq_of_low_digits {p : ℕ} (hp : p.Prime) (a N K : ℕ)
    (hN : ∀ i < a, N / p ^ i % p = p - 1) (hK : ∀ i < a, K / p ^ i % p = p - 1) :
    Nat.choose N K ≡ Nat.choose (N / p ^ a) (K / p ^ a) [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : Nat.choose N K ≡ Nat.choose (N / p ^ a) (K / p ^ a) *
      ∏ i ∈ Finset.range a, Nat.choose (N / p ^ i % p) (K / p ^ i % p) [MOD p] := by
    rw [← Int.natCast_modEq_iff]
    exact_mod_cast Choose.choose_modEq_choose_mul_prod_range_choose
      (p := p) (n := N) (k := K) a
  have hprod : ∏ i ∈ Finset.range a, Nat.choose (N / p ^ i % p) (K / p ^ i % p) = 1 :=
    Finset.prod_eq_one fun i hi => by
      rw [hN i (Finset.mem_range.mp hi), hK i (Finset.mem_range.mp hi), Nat.choose_self]
  rwa [hprod, Nat.mul_one] at h

/- ### Residue arithmetic -/

/-- If `K ≡ −1 (mod A)` (via `K + 1 = A·b`) and `q·K ≡ −1 (mod A)`,
then `q ≡ 1 (mod A)`. -/
lemma mod_eq_one_of_mul_mod_eq {A b q K : ℕ} (hA : 2 ≤ A) (hK : K + 1 = A * b)
    (h : q * K % A = A - 1) : q % A = 1 := by
  have hKz : (K : ZMod A) = -1 := by
    have h0 : ((K + 1 : ℕ) : ZMod A) = 0 := by
      rw [hK, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hA1 : ((A - 1 : ℕ) : ZMod A) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ A), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have h1 : ((q * K % A : ℕ) : ZMod A) = ((q * K : ℕ) : ZMod A) :=
    ZMod.natCast_mod _ _
  rw [h, Nat.cast_mul, hKz, hA1] at h1
  have h2 : (q : ZMod A) * (-1) = -1 := h1.symm
  rw [mul_neg_one] at h2
  have h3 : (q : ZMod A) = 1 := neg_inj.mp h2
  have h4 : q ≡ 1 [MOD A] := by
    have h5 : ((q : ℕ) : ZMod A) = ((1 : ℕ) : ZMod A) := by
      rw [h3, Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h5
  have h6 : q % A = 1 % A := h4
  rwa [Nat.mod_eq_of_lt (by omega : 1 < A)] at h6

/- ### The shift congruence `C((1+At)·K, K) ≡ C((b−1)+tK, b−1) (mod p)` -/

/-- For `K + 1 = p^a · b` and any `t`, removing the common lowest `a`
digits (all `p − 1`) of `(1 + p^a t)·K` and `K` reduces the binomial
coefficient to `C((b−1) + tK, b−1)` modulo `p`. -/
lemma choose_shift_congr {p : ℕ} (hp : p.Prime) (a b t K : ℕ) (hb : 1 ≤ b)
    (hK : K + 1 = p ^ a * b) :
    Nat.choose ((1 + p ^ a * t) * K) K ≡
      Nat.choose ((b - 1) + t * K) (b - 1) [MOD p] := by
  have hP : 0 < p ^ a := pow_pos hp.pos a
  have hmul : p ^ a * b = p ^ a * (b - 1) + p ^ a := by
    have h1 : b - 1 + 1 = b := by omega
    calc p ^ a * b = p ^ a * (b - 1 + 1) := by rw [h1]
      _ = p ^ a * (b - 1) + p ^ a := by ring
  have hKeq : K = p ^ a * (b - 1) + (p ^ a - 1) := by omega
  have hKmod : K % p ^ a = p ^ a - 1 := by
    rw [hKeq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hKdiv : K / p ^ a = b - 1 := by
    rw [hKeq, Nat.mul_add_div hP, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have h1 : (1 + p ^ a * t) * K = K + p ^ a * (t * K) := by ring
  have h2 : p ^ a * ((b - 1) + t * K) = p ^ a * (b - 1) + p ^ a * (t * K) := by
    ring
  have hqKeq : (1 + p ^ a * t) * K = p ^ a * ((b - 1) + t * K) + (p ^ a - 1) := by
    omega
  have hqKmod : (1 + p ^ a * t) * K % p ^ a = p ^ a - 1 := by
    rw [hqKeq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hqKdiv : (1 + p ^ a * t) * K / p ^ a = (b - 1) + t * K := by
    rw [hqKeq, Nat.mul_add_div hP, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have h := choose_modEq_of_low_digits hp a ((1 + p ^ a * t) * K) K
    (digits_of_mod_pow hp.two_le a _ hqKmod) (digits_of_mod_pow hp.two_le a _ hKmod)
  rwa [hqKdiv, hKdiv] at h

/-- **Lemma (Primary criterion)**.
"Let `n ≥ 2`, let `p^a ∥ n`, and write `A = p^a`, `n = Ab`, `p ∤ b`.  Put
`G_n = gcd_{2 ≤ q ≤ n} C(q(n−1), n−1)`.  Then `p ∣ G_n  ↔  b ≤ A`."

Encoding: `a = n.factorization p` (so `p^a ∥ n` automatically), with the
hypothesis `a ≥ 1` expressing `p ∣ n`; and `G_n = D (n−1)` since with
`k = n−1` the range `2 ≤ q ≤ k+1` is exactly `2 ≤ q ≤ n`. -/
theorem primary_criterion (n p b : ℕ) (hn : 2 ≤ n) (hp : p.Prime)
    (ha : 1 ≤ n.factorization p) (hb : n = p ^ n.factorization p * b)
    (hpb : ¬ p ∣ b) :
    p ∣ D (n - 1) ↔ b ≤ p ^ n.factorization p := by
  have hp2 := hp.two_le
  set a := n.factorization p with ha_def
  have hA2 : 2 ≤ p ^ a := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | h
    · rw [Nat.mul_zero] at hb; omega
    · exact h
  have hK : (n - 1) + 1 = p ^ a * b := by omega
  have hD : D (n - 1) = (Finset.Icc 2 n).gcd fun q => Nat.choose (q * (n - 1)) (n - 1) := by
    have h1 : n - 1 + 1 = n := by omega
    simp only [D]
    rw [h1]
  have hP : 0 < p ^ a := pow_pos hp.pos a
  have hmul : p ^ a * b = p ^ a * (b - 1) + p ^ a := by
    have h1 : b - 1 + 1 = b := by omega
    calc p ^ a * b = p ^ a * (b - 1 + 1) := by rw [h1]
      _ = p ^ a * (b - 1) + p ^ a := by ring
  have hKeq : n - 1 = p ^ a * (b - 1) + (p ^ a - 1) := by omega
  have hKmod : (n - 1) % p ^ a = p ^ a - 1 := by
    rw [hKeq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hKdig : ∀ i < a, (n - 1) / p ^ i % p = p - 1 :=
    digits_of_mod_pow hp2 a (n - 1) hKmod
  constructor
  · -- forward direction: `p ∣ D(n−1)` forces `b ≤ p^a` via the zero-run lemma
    intro hdvdD
    rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · omega
    have hchoose : ∀ t ∈ Finset.Icc 1 (b - 1),
        p ∣ Nat.choose ((b - 1) + t * (n - 1)) (b - 1) := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      have hqmem : 1 + p ^ a * t ∈ Finset.Icc 2 n := by
        rw [Finset.mem_Icc]
        have h1 : 1 * 1 ≤ p ^ a * t := Nat.mul_le_mul (by omega) ht.1
        have h2 : p ^ a * t ≤ p ^ a * (b - 1) := Nat.mul_le_mul_left _ ht.2
        omega
      have hgcd : p ∣ Nat.choose ((1 + p ^ a * t) * (n - 1)) (n - 1) := by
        refine hdvdD.trans ?_
        rw [hD]
        exact Finset.gcd_dvd hqmem
      exact ((choose_shift_congr hp a b t (n - 1) hb1 hK).dvd_iff dvd_rfl).mp hgcd
    have hpK : ¬ p ∣ (n - 1) := by
      intro hdK
      have hdA : p ∣ p ^ a := dvd_pow_self p (by omega)
      have hdAb : p ∣ (n - 1) + 1 := by
        rw [hK]
        exact hdA.mul_right b
      have hd1 : p ∣ 1 := (Nat.dvd_add_right hdK).mp hdAb
      have := Nat.le_of_dvd one_pos hd1
      omega
    have hcop : Nat.Coprime (n - 1) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpK).symm
    have hm1 : ¬ p ∣ (b - 1) + 1 := by
      have h1 : b - 1 + 1 = b := by omega
      rwa [h1]
    have hm0 : b - 1 ≠ 0 := by omega
    have hzr := zero_run p (b - 1) (n - 1) (Nat.log p (b - 1) + 1) hp (by omega)
      hcop hm1
      (by simpa using Nat.pow_log_le_self p hm0)
      (Nat.lt_pow_succ_log_self hp.one_lt _)
      hchoose
    have hdvd1 : p ^ (Nat.log p (b - 1) + 1) ∣ (n - 1) + 1 := by
      have h0 : (((n - 1) + 1 : ℕ) : ZMod (p ^ (Nat.log p (b - 1) + 1))) = 0 := by
        rw [Nat.cast_add, Nat.cast_one, hzr, neg_add_cancel]
      exact (ZMod.natCast_eq_zero_iff _ _).mp h0
    rw [hK] at hdvd1
    have hcopb : Nat.Coprime (p ^ (Nat.log p (b - 1) + 1)) b :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb)
    have hdvdA : p ^ (Nat.log p (b - 1) + 1) ∣ p ^ a :=
      hcopb.dvd_of_dvd_mul_right hdvd1
    have hle := Nat.le_of_dvd (by omega) hdvdA
    have hltb : b - 1 < p ^ (Nat.log p (b - 1) + 1) :=
      Nat.lt_pow_succ_log_self hp.one_lt _
    omega
  · -- backward direction: `b ≤ p^a` makes every `C(q(n−1), n−1)` divisible by `p`
    intro hbA
    rw [hD]
    apply Finset.dvd_gcd
    intro q hq
    rw [Finset.mem_Icc] at hq
    show p ∣ Nat.choose (q * (n - 1)) (n - 1)
    by_contra hndvd
    have hdig := (lucas_nonvanishing p hp (q * (n - 1)) (n - 1)).mp hndvd
    have hqdig : ∀ i < a, q * (n - 1) / p ^ i % p = p - 1 := by
      intro i hi
      have h1 := hdig i
      rw [hKdig i hi] at h1
      have h2 : q * (n - 1) / p ^ i % p < p := Nat.mod_lt _ hp.pos
      omega
    have hqKmodA : q * (n - 1) % p ^ a = p ^ a - 1 :=
      mod_pow_eq_of_digits hp a _ hqdig
    have hq1 : q % p ^ a = 1 := mod_eq_one_of_mul_mod_eq hA2 hK hqKmodA
    have hdm := Nat.div_add_mod q (p ^ a)
    have ht1 : 1 ≤ q / p ^ a := by
      rcases Nat.eq_zero_or_pos (q / p ^ a) with h0 | h
      · rw [h0, Nat.mul_zero] at hdm; omega
      · exact h
    have htb : q / p ^ a ≤ b - 1 := by
      by_contra hcon
      push Not at hcon
      have h1 : p ^ a * b ≤ p ^ a * (q / p ^ a) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hqe : q = 1 + p ^ a * (q / p ^ a) := by omega
    have hcongr := choose_shift_congr hp a b (q / p ^ a) (n - 1) hb1 hK
    have hndvd2 : ¬ p ∣ Nat.choose ((b - 1) + (q / p ^ a) * (n - 1)) (b - 1) := by
      intro hdd
      apply hndvd
      rw [hqe]
      exact (hcongr.dvd_iff dvd_rfl).mpr hdd
    have hdig2 := (lucas_nonvanishing p hp ((b - 1) + (q / p ^ a) * (n - 1)) (b - 1)).mp hndvd2
    have hmem : b - 1 ∈ digitBox p a (((b - 1) + (q / p ^ a) * (n - 1)) % p ^ a) := by
      rw [mem_digitBox]
      refine ⟨by omega, fun i hi => ?_⟩
      rw [digit_mod_pow p a i _ hi]
      exact hdig2 i
    have hle := le_of_mem_digitBox p hp.pos a _ _ hmem
    have hcomp : ((b - 1) + (q / p ^ a) * (n - 1)) % p ^ a = b - 1 - q / p ^ a := by
      have h2 : (q / p ^ a) * ((n - 1) + 1) = (q / p ^ a) * (n - 1) + (q / p ^ a) := by
        ring
      rw [hK] at h2
      have h3 : (q / p ^ a) * (p ^ a * b) = p ^ a * ((q / p ^ a) * b) := by ring
      have h1 : (b - 1) + (q / p ^ a) * (n - 1) =
          (b - 1 - q / p ^ a) + p ^ a * ((q / p ^ a) * b) := by omega
      rw [h1, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hcomp] at hle
    omega

/- ## Main theorem -/

/-- For `n ≥ 2`, `ppart n` is realized as the exact component
`p₀ ^ n.factorization p₀` of some prime factor `p₀` of `n`. -/
private lemma exists_ppart_eq (n : ℕ) (hn : 2 ≤ n) :
    ∃ p ∈ n.primeFactors, ppart n = p ^ n.factorization p := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨p₀, hp₀, hsup⟩ :=
    Finset.exists_mem_eq_sup n.primeFactors hne (fun p => p ^ n.factorization p)
  exact ⟨p₀, hp₀, hsup⟩

/-- **Theorem (A080170)**.
"Let `k ≥ 2` and put `n = k+1`.  Then
`gcd_{2 ≤ q ≤ k+1} C(qk, k) = 1  ↔  n / ppart(n) > ppart(n)`."

Note: `ppart n ∣ n` for `n ≥ 2`, so the natural-number division `n / ppart n`
is exact, matching the `n / P` of `PrimePowerCondition`. -/
theorem a080170 (k : ℕ) (hk : 2 ≤ k) :
    D k = 1 ↔ (k + 1) / ppart (k + 1) > ppart (k + 1) := by
  set n := k + 1 with hn_def
  have hn : 2 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hkn : n - 1 = k := by omega
  -- the prime factor realizing `ppart n`
  obtain ⟨p₀, hp₀mem, hP⟩ := exists_ppart_eq n hn
  obtain ⟨hp₀, hp₀dvd, -⟩ := Nat.mem_primeFactors.mp hp₀mem
  have ha₀ : 1 ≤ n.factorization p₀ :=
    (Nat.Prime.dvd_iff_one_le_factorization hp₀ hn0).mp hp₀dvd
  constructor
  · -- `D k = 1 → n / P > P`
    intro hD
    by_contra hcon
    push Not at hcon
    -- `hcon : n / ppart n ≤ ppart n`; apply the primary criterion at `p₀`
    have hb : n = p₀ ^ n.factorization p₀ * (n / p₀ ^ n.factorization p₀) :=
      (Nat.ordProj_mul_ordCompl_eq_self n p₀).symm
    have hpb : ¬ p₀ ∣ n / p₀ ^ n.factorization p₀ := Nat.not_dvd_ordCompl hp₀ hn0
    have hcrit := primary_criterion n p₀ (n / p₀ ^ n.factorization p₀) hn hp₀ ha₀ hb hpb
    rw [hkn] at hcrit
    have hble : n / p₀ ^ n.factorization p₀ ≤ p₀ ^ n.factorization p₀ := by
      rw [← hP]
      exact hcon
    have hdvd : p₀ ∣ D k := hcrit.mpr hble
    rw [hD] at hdvd
    have := Nat.le_of_dvd one_pos hdvd
    have := hp₀.two_le
    omega
  · -- `n / P > P → D k = 1`
    intro hPP
    by_contra hD
    obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd hD
    have hpn : p ∣ n := prime_dvd_succ_of_dvd_D k p (by omega) hpD
    have ha : 1 ≤ n.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hp hn0).mp hpn
    have hb : n = p ^ n.factorization p * (n / p ^ n.factorization p) :=
      (Nat.ordProj_mul_ordCompl_eq_self n p).symm
    have hpb : ¬ p ∣ n / p ^ n.factorization p := Nat.not_dvd_ordCompl hp hn0
    have hcrit := primary_criterion n p (n / p ^ n.factorization p) hn hp ha hb hpb
    rw [hkn] at hcrit
    have hble : n / p ^ n.factorization p ≤ p ^ n.factorization p := hcrit.mp hpD
    -- `p ^ a ≤ ppart n`, hence `n / ppart n ≤ n / p ^ a ≤ p ^ a ≤ ppart n`
    have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩
    have hle : p ^ n.factorization p ≤ ppart n :=
      Finset.le_sup (f := fun q => q ^ n.factorization q) hpmem
    have hApos : 0 < p ^ n.factorization p := pow_pos hp.pos _
    have hdivle : n / ppart n ≤ n / p ^ n.factorization p :=
      Nat.div_le_div_left hle hApos
    have hfinal : n / ppart n ≤ ppart n := hdivle.trans (hble.trans hle)
    exact absurd hPP (Nat.not_lt.mpr hfinal)

/-- **Bridge lemma.**  The index sets `{i + 2 : i < k}` of `GCDCondition`
and `Icc 2 (k+1)` of `D` coincide, so the two GCDs agree and
`GCDCondition k` is exactly `D k = 1`. -/
theorem gcdCondition_iff_D_eq_one (k : ℕ) :
    GCDCondition k ↔ D k = 1 := by
  have himg : (Finset.range k).image (· + 2) = Finset.Icc 2 (k + 1) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ha, rfl⟩; omega
    · intro hx; exact ⟨x - 2, by omega, by omega⟩
  have h : (Finset.range k).gcd (fun i => Nat.choose ((i + 2) * k) k) = D k := by
    unfold D
    rw [← himg, Finset.gcd_image]
    rfl
  unfold GCDCondition
  rw [h]

/-- For each prime factor `p` of `n ≠ 0`, the exact component
`p ^ n.factorization p` is a prime-power divisor of `n`. -/
private lemma ordProj_mem_filter {n p : ℕ} (hn0 : n ≠ 0) (hp : p ∈ n.primeFactors) :
    p ^ n.factorization p ∈ (Nat.divisors n).filter IsPrimePow := by
  obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
  rw [Finset.mem_filter, Nat.mem_divisors]
  refine ⟨⟨Nat.ordProj_dvd n p, hn0⟩, ?_⟩
  have h1 : 1 ≤ n.factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization hpp hn0).mp hpd
  exact ⟨p, n.factorization p, hpp.prime, h1, rfl⟩

/-- Every prime-power divisor of `n ≠ 0` is at most `ppart n`. -/
private lemma le_ppart_of_mem_filter {n q : ℕ} (hn0 : n ≠ 0)
    (hq : q ∈ (Nat.divisors n).filter IsPrimePow) : q ≤ ppart n := by
  rw [Finset.mem_filter, Nat.mem_divisors] at hq
  obtain ⟨⟨hqd, -⟩, p, j, hpp, hj, rfl⟩ := hq
  have hpp' : p.Prime := hpp.nat_prime
  have hpmem : p ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hpp', (dvd_pow_self p hj.ne').trans hqd, hn0⟩
  have hjle : j ≤ n.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hpp' hn0).mp hqd
  calc p ^ j ≤ p ^ n.factorization p :=
        Nat.pow_le_pow_right hpp'.one_lt.le hjle
    _ ≤ ppart n :=
        Finset.le_sup (f := fun p => p ^ n.factorization p) hpmem

/-- **Helper.**  For `n ≥ 2`, the largest prime-power divisor of `n` is its
largest exact prime-power component: every prime-power divisor `p^j ∣ n`
satisfies `p^j ≤ p ^ (n.factorization p) ≤ ppart n`, and `ppart n` itself
is a prime-power divisor of `n`. -/
theorem max_primePow_divisor_eq_ppart (n : ℕ) (hn : 2 ≤ n) :
    ((Nat.divisors n).filter IsPrimePow).max.getD 0 = ppart n := by
  have hn0 : n ≠ 0 := by omega
  -- a prime factor realizing the sup defining `ppart n`
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨p₀, hp₀, hsup⟩ :=
    Finset.exists_mem_eq_sup n.primeFactors hne (fun p => p ^ n.factorization p)
  have hmemP : ppart n ∈ (Nat.divisors n).filter IsPrimePow := by
    rw [ppart, hsup]
    exact ordProj_mem_filter hn0 hp₀
  have hmax : ((Nat.divisors n).filter IsPrimePow).max = (ppart n : WithBot ℕ) := by
    refine le_antisymm (Finset.max_le fun a ha => ?_) (Finset.le_max hmemP)
    exact WithBot.coe_le_coe.mpr (le_ppart_of_mem_filter hn0 ha)
  rw [hmax]
  rfl

/-- **Bridge lemma.**  The largest prime-power divisor of `n` (the `P` of
`PrimePowerCondition`) equals the largest exact prime-power component
`ppart n`, so `PrimePowerCondition n` is exactly `n / ppart n > ppart n`. -/
theorem primePowerCondition_iff_ppart (n : ℕ) (hn : 2 ≤ n) :
    PrimePowerCondition n ↔ n / ppart n > ppart n := by
  unfold PrimePowerCondition
  rw [max_primePow_divisor_eq_ppart n hn]

/--
Conjecture: The gcd condition is equivalent to the prime power condition.
This is now a theorem: a complete proof is given below.
-/
@[category research solved, AMS 11]
theorem gcdCondition_iff_primePowerCondition (k : ℕ) (hk : 2 ≤ k) :
    GCDCondition k ↔ PrimePowerCondition (k + 1) := by
  rw [gcdCondition_iff_D_eq_one k, a080170 k hk,
    primePowerCondition_iff_ppart (k + 1) (by omega)]

end OeisA80170
