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

noncomputable def conjugate_exponent (p : ℝ) : ℝ := p/(p-1)

lemma is_conjugate_exponent.ne_zero {p q : ℝ} (h : p.is_conjugate_exponent q) :
  p ≠ 0 :=
ne_of_gt (lt_trans zero_lt_one h.one_lt)

lemma is_conjugate_exponent.sub_one_ne_zero {p q : ℝ}
  (h : p.is_conjugate_exponent q) : p - 1 ≠ 0 :=
sub_ne_zero_of_ne (ne_of_gt h.one_lt)

lemma is_conjugate_exponent_iff {p q : ℝ} (h : 1 < p) :
  p.is_conjugate_exponent q ↔ q = p/(p-1) :=
begin
  have A : 1/p + 1/q = 1 ↔ q = 1/(1-1/p) := calc
    1/p + 1/q = 1 ↔ 1/q = 1-1/p : eq_sub_iff_add_eq'.symm
    ... ↔ q = 1/(1-1/p) : by { simp only [one_div_eq_inv], rw inv_eq_iff, exact eq_comm },
  split,
  { assume H,
    rw A.1 H.inv_add_inv_conj,
    field_simp [H.ne_zero] },
  { assume H,
    refine ⟨h, _⟩,
    rw H,
    field_simp [ne_of_gt (lt_trans zero_lt_one h)] }
end

lemma is_conjugate_exponent_conjugate_exponent {p : ℝ} (h : 1 < p) :
  p.is_conjugate_exponent (conjugate_exponent p) :=
(is_conjugate_exponent_iff h).2 rfl

namespace is_conjugate_exponent

variables {p q : ℝ} (h : p.is_conjugate_exponent q)
include h

lemma conj_eq : q = p/(p-1) :=
(is_conjugate_exponent_iff h.one_lt).1 h

protected lemma symm : q.is_conjugate_exponent p :=
{ one_lt :=
    by { rw [h.conj_eq], exact one_lt_div_of_lt _ (sub_pos_of_lt h.one_lt) (sub_one_lt p) },
  inv_add_inv_conj := by simpa [add_comm] using h.inv_add_inv_conj }

end is_conjugate_exponent

end real

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with nonnegative functions. -/
theorem finset.sum_le_sum_rpow_rpow_inv_mul_sum_rpow_rpow_inv
  {α : Type*} (s : finset α) (f g : α → ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x)
  (p q : ℝ) (hpq : p.is_conjugate_exponent q) :
  (∑ i in s, f i * g i) ≤ (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) :=
begin
  by_cases H : ∀ (i : α), i ∈ s → g i = 0,
  { -- assume first that all `g i` vanish. Then the result is trivial.
    have A : (∑ i in s, f i * g i) = (∑ i in s, f i * 0),
    { apply finset.sum_congr rfl (λ x hx, _), simp [H x hx] },
    have B : (∑ i in s, (g i)^q) = (∑ i in s, 0),
    { apply finset.sum_congr rfl (λ x hx, _),
      simp [H x hx, zero_rpow hpq.symm.ne_zero] },
    simp [A, B, zero_rpow (inv_ne_zero hpq.symm.ne_zero)] },
  { /- Assume now that some `g i` is nonzero, so that the sum `S = ∑ i in s, (g i)^q` is nonzero.
    We will apply the convexity of the function `x ↦ x^p` to a suitable sum to get the result:
    write `a i = (g i)^q / S` (these coefficients add up to `1`). Then, by convexity,
    `(∑ a i * (f i * (g i)^(1-q))) ^ p ≤ (∑ a i * (f i * (g i)^(1-q)) ^ p)`. This is the desired
    inequality, up to trivial massaging, as the sum on the left is `(∑ f i * g i / S) ^ p` and the
    sum on the right is `(∑ (f i) ^ p) / S`. -/
    set S := (∑ i in s, (g i)^q) with hS,
    have S_ne : S ≠ 0,
    { assume Z,
      have : ∀ (i : α), i ∈ s → 0 ≤ (g i)^q,
        by { assume i hi, exact rpow_nonneg_of_nonneg (hg i hi) _ },
      rw finset.sum_eq_zero_iff_of_nonneg this at Z,
      apply H,
      assume i hi,
      simpa [rpow_eq_zero_iff_of_nonneg (hg i hi), hpq.symm.ne_zero] using Z i hi },
    have S_pos : 0 < S,
    { have : 0 ≤ S := finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg (hg i hi) _),
      exact lt_of_le_of_ne this (ne.symm S_ne) },
    set a := λ i, (g i)^q / S with ha,
    have fgS_nonneg : 0 ≤ ∑ (x : α) in s, f x * g x / S :=
      finset.sum_nonneg (λ i hi, div_nonneg (mul_nonneg (hf i hi) (hg i hi)) S_pos),
    -- formulate the main convexity inequality, in a suitable form
    have main : (∑ i in s, f i * g i/S) ^ p ≤ (∑ i in s, (f i)^p) / S := calc
      (∑ i in s, f i * g i/S) ^ p
          ≤ (∑ i in s, a i * (f i * (g i)^(1-q))) ^ p :
      begin
        apply rpow_le_rpow fgS_nonneg _ (le_of_lt (lt_trans zero_lt_one hpq.one_lt)),
        apply finset.sum_le_sum (λ i hi, _),
        rcases le_iff_eq_or_lt.1 (hg i hi) with H|pos,
        { simp [ha, ← H], simp [← H, zero_rpow hpq.symm.ne_zero] },
        { have : g i = (g i)^q * (g i)^(1-q), by simp [← rpow_add _ _ pos],
          conv_lhs { rw this },
          apply le_of_eq,
          simp [ha],
          ring }
      end
      ... ≤ (∑ i in s, a i * (f i * (g i)^(1-q))^p) :
      begin
        -- this is where something happens, i.e., we use convexity.
        apply (convex_on_rpow (le_of_lt hpq.one_lt)).map_sum_le,
        { assume i hi, exact div_nonneg (rpow_nonneg_of_nonneg (hg i hi) _) S_pos },
        { rw [ha, ← finset.sum_div, hS, div_self S_ne] },
        { assume i hi, exact mul_nonneg (hf i hi) (rpow_nonneg_of_nonneg (hg i hi) _) }
      end
      ... ≤ (∑ i in s, (f i)^p / S) :
      begin
        apply finset.sum_le_sum (λ i hi, _),
        calc a i * (f i * g i ^ (1 - q)) ^ p
            = a i * ((f i) ^ p * (g i)^ ((1-q) * p)) :
          by rw [mul_rpow (hf i hi) (rpow_nonneg_of_nonneg (hg i hi) _), ← rpow_mul (hg i hi)]
        ... = ((f i)^p / S) * ((g i)^q * (g i)^((1-q)*p)) : by { simp [ha], ring }
        ... ≤ (f i ^ p / S) * 1 :
        begin
          apply mul_le_mul_of_nonneg_left _ (div_nonneg (rpow_nonneg_of_nonneg (hf i hi) _) S_pos),
          rcases le_iff_eq_or_lt.1 (hg i hi) with H|pos,
          { simp [zero_rpow hpq.symm.ne_zero, ← H, zero_le_one] },
          { have : q + (1 - q) * p = 0, by { field_simp [hpq.conj_eq, hpq.sub_one_ne_zero], ring },
            rw [← rpow_add _ _ pos, this, rpow_zero] }
        end
        ... = f i ^p / S : by simp
      end
      ... = (∑ i in s, (f i)^p) / S : by rw finset.sum_div,
      -- Now that we have proved the main inequality, deduce the result by putting the `S` factors
      -- in the right place.
      calc
      (∑ i in s, f i * g i)
      = S * ((∑ i in s, f i * g i/S) ^ p) ^ (1/p) :
      begin
        have : p * p⁻¹ = 1 := div_self hpq.ne_zero,
        simp only [← rpow_mul fgS_nonneg, this, one_div_eq_inv, rpow_one],
        rw [← finset.sum_div, mul_div_cancel' _ S_ne]
      end
      ... ≤ S * ((∑ i in s, (f i)^p) / S) ^ (1/p) :
      begin
        apply mul_le_mul_of_nonneg_left _ (le_of_lt S_pos),
        exact rpow_le_rpow (rpow_nonneg_of_nonneg fgS_nonneg _) main
          (div_nonneg zero_le_one (lt_trans zero_lt_one hpq.one_lt)),
      end
      ... = (∑ i in s, (f i)^p) ^ (1/p) * S ^ (1-1/p) :
      begin
        have : 0 ≤ ∑ (i : α) in s, f i ^ p :=
          finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg (hf i hi) _),
        simp only [sub_eq_add_neg, rpow_add _ _ S_pos, div_eq_inv_mul, mul_one, rpow_one],
        rw [mul_rpow (inv_nonneg.2 (le_of_lt S_pos)) this, ← rpow_neg_one, ← rpow_mul (le_of_lt S_pos)],
        simp only [neg_mul_eq_neg_mul_symm, one_mul],
        ring
      end
      ... = (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) : begin
        have : 1 - 1/p = 1/q := sub_eq_of_eq_add' (eq.symm hpq.inv_add_inv_conj),
        rw this,
      end },
end
