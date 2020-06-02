/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.convex.specific_functions

/-!
# `L^p` distance on finite products of metric spaces

Given finitely many metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a real parameter `p ∈ [1, ∞)`, that also induce
the product topology. We define them in this file.
-/

open real set
open_locale big_operators

namespace real

/-- Two real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
structure is_conjugate_exponent (p q : ℝ) : Prop :=
(one_lt : 1 < p)
(inv_add_inv_conj : 1/p + 1/q = 1)

/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `1/p + 1/q = 1`. -/
noncomputable def conjugate_exponent (p : ℝ) : ℝ := p/(p-1)

/- Register several non-vanishing results following from the fact that `p` has a conjugate exponent
`q`: many computations using these exponents require clearing out denominators, which can be done
with `field_simp` given a proof that these denominators are non-zero, so we record the most usual
ones. -/
lemma is_conjugate_exponent.ne_zero {p q : ℝ} (h : p.is_conjugate_exponent q) :
  p ≠ 0 :=
ne_of_gt (lt_trans zero_lt_one h.one_lt)

lemma is_conjugate_exponent.sub_one_ne_zero {p q : ℝ}
  (h : p.is_conjugate_exponent q) : p - 1 ≠ 0 :=
sub_ne_zero_of_ne (ne_of_gt h.one_lt)

lemma is_conjugate_exponent.one_div_ne_zero {p q : ℝ} (h : p.is_conjugate_exponent q) :
  1/p ≠ 0 :=
λ H, by simpa [h.ne_zero] using H

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

namespace finset
/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with nonnegative functions. -/
theorem sum_rpow_holder_of_nonneg
  {α : Type*} {s : finset α} {f g : α → ℝ} {p q : ℝ}
  (hpq : p.is_conjugate_exponent q) (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x) :
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
          = (∑ i in s, a i * (f i * (g i)^(1-q))) ^ p :
      begin
        congr' 1,
        apply finset.sum_congr rfl (λ i hi, _),
        have : q + (1-q) ≠ 0, by simp,
        have : g i = (g i)^q * (g i)^(1-q), by simp [← rpow_add' (hg i hi) this],
        conv_lhs { rw this },
        simp [ha],
        ring
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
          have : q + (1 - q) * p = 0, by { field_simp [hpq.conj_eq, hpq.sub_one_ne_zero], ring },
          have : 1 = (g i) ^ (q + (1 - q) * p), by simp [this],
          conv_rhs { rw this },
          exact le_rpow_add (hg i hi) _ _,
        end
        ... = f i ^p / S : by rw [mul_one]
      end
      ... = (∑ i in s, (f i)^p) / S : by rw finset.sum_div,
    -- Now that we have proved the main inequality, deduce the result by putting the `S` factors
    -- in the right place.
    calc (∑ i in s, f i * g i)
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
        simp only [sub_eq_add_neg, rpow_add S_pos, div_eq_inv_mul, mul_one, rpow_one],
        rw [mul_rpow (inv_nonneg.2 (le_of_lt S_pos)) this, ← rpow_neg_one,
            ← rpow_mul (le_of_lt S_pos)],
        simp only [neg_mul_eq_neg_mul_symm, one_mul],
        ring
      end
      ... = (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) :
        by rw sub_eq_of_eq_add' (eq.symm hpq.inv_add_inv_conj) }
end

/-- Minkowski inequality: the `L^p` norm satisfies the triangular inequality, i.e.,
`||f+g||_p ≤ ||f||_p + ||g||_p`. Version for sums over finite sets, with nonnegative functions. -/
theorem sum_rpow_minkowski_of_nonneg
  {α : Type*} {s : finset α} {f g : α → ℝ} {p : ℝ}
  (hp : 1 ≤ p) (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x) :
  (∑ i in s, (f i + g i) ^ p)^(1/p) ≤ (∑ i in s, (f i)^p) ^ (1/p) + (∑ i in s, (g i)^p) ^ (1/p) :=
begin
  -- The result is trivial when `p = 1`, so we can assume `1 < p`.
  rcases le_iff_eq_or_lt.1 hp with H|lt_p, { simp [← H, finset.sum_add_distrib] },
  let q := p.conjugate_exponent,
  have hpq : p.is_conjugate_exponent q := real.is_conjugate_exponent_conjugate_exponent lt_p,
  /- The trick is to start from the sum `S = ∑ i in s, (f i + g i) ^ p`, decompose the power as
  `f i * (f i + g i) ^ (p-1) + g i * (f i + g i) ^ (p-1)`, and apply Hölder inequality with the
  exponents `p` and `q` to each of the two resulting sums. As `(p-1) q = p`, this gives a bound
  involving the same sum `S`, but at the power `1/q`. Massaging this inequality gives the
  desired boud. -/
  set S := ∑ i in s, (f i + g i) ^ p with hS,
  have : 0 ≤ S :=
    finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg (add_nonneg (hf i hi) (hg i hi)) _),
  rcases le_iff_eq_or_lt.1 this with H|S_pos,
  { /- The cancellation argument in the above sketch does not work when `S = 0`, so we first deal
    with this (trivial) case directly. -/
    simp only [← H, zero_rpow hpq.one_div_ne_zero],
    apply add_nonneg;
    refine rpow_nonneg_of_nonneg (finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg _ _)) _,
    { exact hf i hi },
    { exact hg i hi } },
  { -- Assume now `0 < S`. We will flesh out the details of the above sketch.
    have S_eq : (∑ i in s, ((f i + g i)^(p-1))^q) = S,
    { apply finset.sum_congr rfl (λ i hi, _),
      rw ← rpow_mul (add_nonneg (hf i hi) (hg i hi)),
      congr' 1,
      field_simp [q, real.conjugate_exponent, hpq.sub_one_ne_zero],
      ring },
    have main : S^(1/p) * S^(1/q) ≤
         ((∑ i in s, (f i)^p) ^ (1/p) + (∑ i in s, (g i)^p) ^ (1/p)) * S ^ (1/q) := calc
      S^(1/p) * S^(1/q) = S :
        by rw [← rpow_add S_pos, hpq.inv_add_inv_conj, rpow_one]
      ... = (∑ i in s, f i * (f i + g i) ^ (p-1)) + (∑ i in s, g i * (f i + g i) ^ (p-1)) :
      begin
        have A : p = 1 + (p-1) := eq_add_of_sub_eq' rfl,
        have B : 1 + (p-1) ≠ 0, by { rw ← A, exact hpq.ne_zero },
        rw [← finset.sum_add_distrib, hS],
        apply finset.sum_congr rfl (λ i hi, _),
        conv_lhs { rw A },
        rw [← add_mul, rpow_add' (add_nonneg (hf i hi) (hg i hi)) B, rpow_one]
      end
      ... ≤ (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, ((f i + g i)^(p-1))^q)^(1/q) +
            (∑ i in s, (g i)^p) ^ (1/p) * (∑ i in s, ((f i + g i)^(p-1))^q)^(1/q) :
      begin
        have A : ∀ i, i ∈ s → 0 ≤ (f i + g i)^(p-1) :=
          λ i hi, rpow_nonneg_of_nonneg (add_nonneg (hf i hi) (hg i hi)) _,
        apply add_le_add;
        apply finset.sum_rpow_holder_of_nonneg hpq (λ i hi, _) A,
        { exact hf i hi },
        { exact hg i hi }
      end
      ... = ((∑ i in s, (f i)^p) ^ (1/p) + (∑ i in s, (g i)^p) ^ (1/p)) * S ^ (1/q) :
        by rw [S_eq, add_mul],
    exact (mul_le_mul_right (rpow_pos_of_pos S_pos _)).mp main },
end

end finset
