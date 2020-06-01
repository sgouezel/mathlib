/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.mean_value
import data.nat.parity
import analysis.special_functions.pow

/-!
# Collection of convex functions

In this file we prove that the following functions are convex:

* `convex_on_exp` : the exponential function is convex on $(-∞, +∞)$;
* `convex_on_pow_of_even` : given an even natural number $n$, the function $f(x)=x^n$
  is convex on $(-∞, +∞)$;
* `convex_on_pow` : for a natural $n$, the function $f(x)=x^n$ is convex on $[0, +∞)$;
* `convex_on_fpow` : for an integer $m$, the function $f(x)=x^m$ is convex on $(0, +∞)$.
* `convex_on_rpow : ∀ p : ℝ, 1 ≤ p → convex_on (Ici 0) (λ x, x ^ p)`
-/

open real set

/-- `exp` is convex on the whole real line -/
lemma convex_on_exp : convex_on univ exp :=
convex_on_univ_of_deriv2_nonneg differentiable_exp (by simp)
  (assume x, (iter_deriv_exp 2).symm ▸ le_of_lt (exp_pos x))

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even -/
lemma convex_on_pow_of_even {n : ℕ} (hn : n.even) : convex_on set.univ (λ x, x^n) :=
begin
  apply convex_on_univ_of_deriv2_nonneg differentiable_pow,
  { simp only [deriv_pow', differentiable.mul, differentiable_const, differentiable_pow] },
  { intro x,
    rcases hn.sub (nat.even_bit0 1) with ⟨k, hk⟩,
    simp only [iter_deriv_pow, finset.prod_range_succ, finset.prod_range_zero, nat.sub_zero,
      mul_one, hk, pow_mul', pow_two],
    exact mul_nonneg (nat.cast_nonneg _) (mul_self_nonneg _) }
end

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n` -/
lemma convex_on_pow (n : ℕ) : convex_on (Ici 0) (λ x, x^n) :=
begin
  apply convex_on_of_deriv2_nonneg (convex_Ici _) (continuous_pow n).continuous_on;
    simp only [interior_Ici, differentiable_on_pow, deriv_pow',
      differentiable_on_const, differentiable_on.mul, iter_deriv_pow],
  intros x hx,
  exact mul_nonneg (nat.cast_nonneg _) (pow_nonneg (le_of_lt hx) _)
end

lemma finset.prod_nonneg_of_card_nonpos_even
  {α β : Type*} [linear_ordered_comm_ring β]
  {f : α → β} [decidable_pred (λ x, f x ≤ 0)]
  {s : finset α} (h0 : (s.filter (λ x, f x ≤ 0)).card.even) :
  0 ≤ s.prod f :=
calc 0 ≤ s.prod (λ x, (if f x ≤ 0 then (-1:β) else 1) * f x) :
  finset.prod_nonneg (λ x _, by
    { split_ifs with hx hx, by simp [hx], simp at hx ⊢, exact le_of_lt hx })
... = _ : by rw [finset.prod_mul_distrib, finset.prod_ite, finset.prod_const_one,
  mul_one, finset.prod_const, neg_one_pow_eq_pow_mod_two, nat.even_iff.1 h0, pow_zero, one_mul]

lemma int_prod_range_nonneg (m : ℤ) (n : ℕ) (hn : n.even) :
  0 ≤ (finset.range n).prod (λ k, m - k) :=
begin
  cases (le_or_lt ↑n m) with hnm hmn,
  { exact finset.prod_nonneg (λ k hk, sub_nonneg.2 (le_trans
      (int.coe_nat_le.2 $ le_of_lt $ finset.mem_range.1 hk) hnm)) },
  cases le_or_lt 0 m with hm hm,
  { lift m to ℕ using hm,
    exact le_of_eq (eq.symm $ finset.prod_eq_zero
      (finset.mem_range.2 $ int.coe_nat_lt.1 hmn) (sub_self _)) },
  clear hmn,
  apply finset.prod_nonneg_of_card_nonpos_even,
  convert hn,
  convert finset.card_range n,
  ext k,
  simp only [finset.mem_filter, finset.mem_range],
  refine ⟨and.left, λ hk, ⟨hk, sub_nonpos.2 $ le_trans (le_of_lt hm) _⟩⟩,
  exact int.coe_nat_nonneg k
end

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` -/
lemma convex_on_fpow (m : ℤ) : convex_on (Ioi 0) (λ x, x^m) :=
begin
  apply convex_on_of_deriv2_nonneg (convex_Ioi 0); try { rw [interior_Ioi] },
  { exact (differentiable_on_fpow $ lt_irrefl _).continuous_on },
  { exact differentiable_on_fpow (lt_irrefl _) },
  { have : eq_on (deriv (λx:ℝ, x^m)) (λx, ↑m * x^(m-1)) (Ioi 0),
      from λ x hx, deriv_fpow (ne_of_gt hx),
    refine (differentiable_on_congr this).2 _,
    exact (differentiable_on_fpow (lt_irrefl _)).const_mul _ },
  { intros x hx,
    simp only [iter_deriv_fpow (ne_of_gt hx)],
    refine mul_nonneg (int.cast_nonneg.2 _) (fpow_nonneg_of_nonneg (le_of_lt hx) _),
    exact int_prod_range_nonneg _ _ (nat.even_bit0 1) }
end

lemma convex_on_rpow {p : ℝ} (hp : 1 ≤ p) : convex_on (Ici 0) (λ x, x^p) :=
begin
  have A : deriv (λ (x : ℝ), x ^ p) = λ x, p * x^(p-1), by { ext x, simp [hp] },
  apply convex_on_of_deriv2_nonneg (convex_Ici 0),
  { apply (continuous_rpow_of_pos (λ _, lt_of_lt_of_le zero_lt_one hp)
      continuous_id continuous_const).continuous_on },
  { apply differentiable.differentiable_on, simp [hp] },
  { rw A,
    assume x hx,
    replace hx : x ≠ 0, by { simp at hx, exact ne_of_gt hx },
    simp [differentiable_at.differentiable_within_at, hx] },
  { assume x hx,
    replace hx : 0 < x, by simpa using hx,
    suffices : 0 ≤ p * ((p - 1) * x ^ (p - 1 - 1)), by simpa [ne_of_gt hx, A],
    apply mul_nonneg (le_trans zero_le_one hp),
    exact mul_nonneg (sub_nonneg_of_le hp) (rpow_nonneg_of_nonneg (le_of_lt hx) _) }
end

open_locale big_operators

namespace real

structure is_conjugate_exponent (p q : ℝ) : Prop :=
(one_lt : 1 < p)
(inv_add_inv_conj : 1/p + 1/q = 1)

lemma is_conjugate_exponent_iff {p q : ℝ} :
  p.is_conjugate_exponent q ↔ q = 1/(1-1/p) :=
calc
1/p + 1/q = 1 ↔ 1/q = 1-1/p : eq_sub_iff_add_eq'.symm
... ↔ q = 1/(1-1/p) : by { simp only [one_div_eq_inv], rw inv_eq_iff, exact eq_comm }

namespace is_conjugate_exponent

variables {p q : ℝ} (h : p.is_conjugate_exponent q)
include h

protected lemma eq : q = 1/(1-1/p) :=
is_conjugate_exponent_iff.1 h

protected lemma symm : q.is_conjugate_exponent p :=
by rwa [is_conjugate_exponent, add_comm]

lemma one_lt (hp : 1 < p) : 1 < q :=
begin
  rw [h.eq, ← inv_eq_one_div],
  refine one_lt_inv (by simp [inv_lt_one hp]) _,
  have : 0 < p⁻¹, { apply inv_pos.2, linarith },
  rw [← inv_eq_one_div],
  linarith
end

lemma conj_add_one_sub_conj_mul_of_one_lt (hp : 1 < p) : q + (1 - q) * p = 0 :=
begin
  rw h.eq,
  field_simp [ne_of_gt (lt_trans zero_lt_one hp), sub_ne_zero_of_ne (ne_of_gt hp)],
  ring
end

end is_conjugate_exponent


theorem finset.sum_le_sum_rpow_inv_rpow_mul_sum_rpow_inv_rpow
  {α : Type*} (s : finset α) (f g : α → ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x)
  (p q : ℝ) (hp : 1 < p) (hpq : p.is_conjugate_exponent q) :
  (∑ i in s, f i * g i) ≤ (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) :=
begin
  have hq : 1 < q := hpq.one_lt hp,
  have Q : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq),
  by_cases H : ∀ (i : α), i ∈ s → g i = 0,
  { -- assume first that all `g i` vanish. Then the result is trivial.
    have A : (∑ i in s, f i * g i) = (∑ i in s, f i * 0),
    { apply finset.sum_congr rfl (λ x hx, _), simp [H x hx] },
    have B : (∑ i in s, (g i)^q) = (∑ i in s, 0),
    { apply finset.sum_congr rfl (λ x hx, _),
      simp [H x hx, zero_rpow Q] },
    simp [A, B, zero_rpow (inv_ne_zero Q)] },
  { -- assume now that some `g i` is nonzero.
    set S := (∑ i in s, (g i)^q) with hS,
    have S_ne : S ≠ 0,
    { assume Z,
      have : ∀ (i : α), i ∈ s → 0 ≤ (g i)^q,
        by { assume i hi, exact rpow_nonneg_of_nonneg (hg i hi) _ },
      rw finset.sum_eq_zero_iff_of_nonneg this at Z,
      apply H,
      assume i hi,
      simpa [rpow_eq_zero_iff_of_nonneg (hg i hi), Q] using Z i hi },
    have S_pos : 0 < S,
    { have : 0 ≤ S := finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg (hg i hi) _),
      exact lt_of_le_of_ne this (ne.symm S_ne) },
    set a := λ i, (g i)^q / S with ha,
    have : (∑ i in s, a i * (f i * (g i)^(1-q))) ^ p ≤ (∑ i in s, a i * (f i * (g i)^(1-q))^p),
    { apply (convex_on_rpow (le_of_lt hp)).map_sum_le,
      { assume i hi, exact div_nonneg (rpow_nonneg_of_nonneg (hg i hi) _) S_pos },
      { rw [ha, ← finset.sum_div, hS, div_self S_ne] },
      { assume i hi, exact mul_nonneg (hf i hi) (rpow_nonneg_of_nonneg (hg i hi) _) } },
    have : (∑ i in s, a i * (f i * (g i)^(1-q))^p) ≤ (∑ i in s, (f i)^p / S),
    { apply finset.sum_le_sum (λ i hi, _),
      calc a i * (f i * g i ^ (1 - q)) ^ p
          = a i * ((f i) ^ p * (g i)^ ((1-q) * p)) :
        by rw [mul_rpow (hf i hi) (rpow_nonneg_of_nonneg (hg i hi) _), ← rpow_mul (hg i hi)]
      ... = ((f i)^p / S) * ((g i)^q * (g i)^((1-q)*p)) : by { simp [ha], ring }
      ... ≤ (f i ^ p / S) * 1 : begin
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (rpow_nonneg_of_nonneg (hf i hi) _) S_pos),
        rcases le_iff_eq_or_lt.1 (hg i hi) with H|pos,
        { simp [zero_rpow Q, ← H, zero_le_one] },
        { rw [← rpow_add _ _ pos, hpq.conj_add_one_sub_conj_mul_of_one_lt hp, rpow_zero] }
      end
      ... = f i ^p / S : by simp },


  }
end
