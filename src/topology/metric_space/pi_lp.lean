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
open_locale big_operators uniformity topological_space

noncomputable theory

variable {ι : Type*}

namespace real

/-- Two real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
structure is_conjugate_exponent (p q : ℝ) : Prop :=
(one_lt : 1 < p)
(inv_add_inv_conj : 1/p + 1/q = 1)

/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `1/p + 1/q = 1`. -/
def conjugate_exponent (p : ℝ) : ℝ := p/(p-1)

/- Register several non-vanishing results following from the fact that `p` has a conjugate exponent
`q`: many computations using these exponents require clearing out denominators, which can be done
with `field_simp` given a proof that these denominators are non-zero, so we record the most usual
ones. -/
lemma is_conjugate_exponent.pos {p q : ℝ} (h : p.is_conjugate_exponent q) :
  0 < p :=
lt_trans zero_lt_one h.one_lt

lemma is_conjugate_exponent.ne_zero {p q : ℝ} (h : p.is_conjugate_exponent q) :
  p ≠ 0 :=
ne_of_gt h.pos

lemma is_conjugate_exponent.sub_one_ne_zero {p q : ℝ}
  (h : p.is_conjugate_exponent q) : p - 1 ≠ 0 :=
sub_ne_zero_of_ne (ne_of_gt h.one_lt)

lemma is_conjugate_exponent.one_div_pos {p q : ℝ} (h : p.is_conjugate_exponent q) :
  0 < 1/p :=
one_div_pos_of_pos h.pos

lemma is_conjugate_exponent.one_div_ne_zero {p q : ℝ} (h : p.is_conjugate_exponent q) :
  1/p ≠ 0 :=
ne_of_gt (h.one_div_pos)

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
theorem sum_rpow_holder_of_nonneg {s : finset ι} {f g : ι → ℝ} {p q : ℝ}
  (hpq : p.is_conjugate_exponent q) (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x) :
  (∑ i in s, f i * g i) ≤ (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) :=
begin
  by_cases H : ∀ (i : ι), i ∈ s → g i = 0,
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
      have : ∀ (i : ι), i ∈ s → 0 ≤ (g i)^q,
        by { assume i hi, exact rpow_nonneg_of_nonneg (hg i hi) _ },
      rw finset.sum_eq_zero_iff_of_nonneg this at Z,
      apply H,
      assume i hi,
      simpa [rpow_eq_zero_iff_of_nonneg (hg i hi), hpq.symm.ne_zero] using Z i hi },
    have S_pos : 0 < S,
    { have : 0 ≤ S := finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg (hg i hi) _),
      exact lt_of_le_of_ne this (ne.symm S_ne) },
    set a := λ i, (g i)^q / S with ha,
    have fgS_nonneg : 0 ≤ ∑ (x : ι) in s, f x * g x / S :=
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
        have : 0 ≤ ∑ (i : ι) in s, f i ^ p :=
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
theorem sum_rpow_minkowski_of_nonneg {s : finset ι} {f g : ι → ℝ} {p : ℝ}
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

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `nnreal`-valued functions. -/
theorem sum_rpow_holder_nnreal {s : finset ι} {f g : ι → nnreal} {p q : ℝ}
  (hpq : p.is_conjugate_exponent q) :
  (∑ i in s, f i * g i) ≤ (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) :=
begin
  rw ← nnreal.coe_le_coe,
  have hf : ∀ i ∈ s, 0 ≤ (f i : ℝ) := λ i hi, nnreal.coe_nonneg (f i),
  have hg : ∀ i ∈ s, 0 ≤ (g i : ℝ) := λ i hi, nnreal.coe_nonneg (g i),
  exact_mod_cast sum_rpow_holder_of_nonneg hpq hf hg
end

/-- Minkowski inequality: the `L^p` norm satisfies the triangular inequality, i.e.,
`||f+g||_p ≤ ||f||_p + ||g||_p`. Version for sums over finite sets, with `nnreal`-valued
functions. -/
theorem sum_rpow_minkowski_nnreal {s : finset ι} {f g : ι → nnreal} {p : ℝ} (hp : 1 ≤ p) :
  (∑ i in s, (f i + g i) ^ p)^(1/p) ≤ (∑ i in s, (f i)^p) ^ (1/p) + (∑ i in s, (g i)^p) ^ (1/p) :=
begin
  rw ← nnreal.coe_le_coe,
  have hf : ∀ i ∈ s, 0 ≤ (f i : ℝ) := λ i hi, nnreal.coe_nonneg (f i),
  have hg : ∀ i ∈ s, 0 ≤ (g i : ℝ) := λ i hi, nnreal.coe_nonneg (g i),
  exact_mod_cast sum_rpow_minkowski_of_nonneg hp hf hg
end

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ennreal`-valued functions. -/
theorem sum_rpow_holder_ennreal {s : finset ι} {f g : ι → ennreal} {p q : ℝ}
  (hpq : p.is_conjugate_exponent q) :
  (∑ i in s, f i * g i) ≤ (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) :=
begin
  by_cases H : (∑ i in s, (f i)^p) ^ (1/p) = 0 ∨ (∑ i in s, (g i)^q) ^ (1/q) = 0,
  { replace H : (∀ i ∈ s, f i = 0) ∨ (∀ i ∈ s, g i = 0),
      by simpa [ennreal.rpow_eq_zero_iff, hpq.pos, hpq.symm.pos, asymm hpq.pos, asymm hpq.symm.pos,
                sum_eq_zero_iff_of_nonneg] using H,
    have : ∀ i ∈ s, f i * g i = 0 := λ i hi, by cases H; simp [H i hi],
    have : (∑ i in s, f i * g i) = (∑ i in s, 0) := sum_congr rfl this,
    simp [this] },
  push_neg at H,
  by_cases H' : (∑ i in s, (f i)^p) ^ (1/p) = ⊤ ∨ (∑ i in s, (g i)^q) ^ (1/q) = ⊤,
  { cases H'; simp [H', -one_div_eq_inv, H] },
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ (∀ i ∈ s, g i ≠ ⊤),
    by simpa [ennreal.rpow_eq_top_iff, asymm hpq.pos, asymm hpq.symm.pos, hpq.pos, hpq.symm.pos,
              ennreal.sum_eq_top_iff, not_or_distrib] using H',
  have := ennreal.coe_le_coe.2 (@sum_rpow_holder_nnreal _ s (λ i, ennreal.to_nnreal (f i))
              (λ i, ennreal.to_nnreal (g i)) _ _ hpq),
  push_cast [← ennreal.coe_rpow_of_nonneg, le_of_lt (hpq.pos), le_of_lt (hpq.one_div_pos),
             le_of_lt (hpq.symm.pos), le_of_lt (hpq.symm.one_div_pos)] at this,
  convert this using 1,
  { apply finset.sum_congr rfl (λ i hi, _), simp [H'.1 i hi, H'.2 i hi] },
  { congr' 2;
    apply finset.sum_congr rfl (λ i hi, _);
    simp [H'.1 i hi, H'.2 i hi] }
end

/-- Minkowski inequality: the `L^p` norm satisfies the triangular inequality, i.e.,
`||f+g||_p ≤ ||f||_p + ||g||_p`. Version for sums over finite sets, with `ennreal`-valued
functions. -/
theorem sum_rpow_minkowski_ennreal {s : finset ι} {f g : ι → ennreal} {p : ℝ} (hp : 1 ≤ p) :
  (∑ i in s, (f i + g i) ^ p)^(1/p) ≤ (∑ i in s, (f i)^p) ^ (1/p) + (∑ i in s, (g i)^p) ^ (1/p) :=
begin
  by_cases H' : (∑ i in s, (f i)^p) ^ (1/p) = ⊤ ∨ (∑ i in s, (g i)^p) ^ (1/p) = ⊤,
  { cases H'; simp [H', -one_div_eq_inv] },
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ (∀ i ∈ s, g i ≠ ⊤),
    by simpa [ennreal.rpow_eq_top_iff, asymm pos, pos, ennreal.sum_eq_top_iff,
              not_or_distrib] using H',
  have := ennreal.coe_le_coe.2 (@sum_rpow_minkowski_nnreal _ s (λ i, ennreal.to_nnreal (f i))
              (λ i, ennreal.to_nnreal (g i)) _  hp),
  push_cast [← ennreal.coe_rpow_of_nonneg, le_of_lt (pos), le_of_lt (one_div_pos_of_pos pos)] at this,
  convert this using 2,
  { apply finset.sum_congr rfl (λ i hi, _), simp [H'.1 i hi, H'.2 i hi] },
  repeat { congr' 1;
    apply finset.sum_congr rfl (λ i hi, _);
    simp [H'.1 i hi, H'.2 i hi] }
end

end finset

/-- A copy of a Pi type, on which we will put the `L^p` distance. Since the Pi type itself is
already endowed with the `L^∞` distance, we need the type synonym to avoid confusing typeclass
resolution. Also, we let it depend on `p`, to get a whole family of type on which we can put
different distances, and we provide the assumption `hp` in the definition, to make it available
to typeclass resolution when it looks for a distance on `pi_lp p hp α`. -/
@[nolint unused_arguments]
def pi_lp {ι : Type*} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type*) : Type* := Π (i : ι), α i

instance {ι : Type*} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type*) [∀ i, inhabited (α i)] :
  inhabited (pi_lp p hp α) :=
⟨λ i, default (α i)⟩

/-- Canonical bijection between `pi_lp_equiv` and the original Pi type. We introduce it to be able
to compare the `L^p` and `L^∞` distances through it. -/
def pi_lp_equiv {ι : Type*} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type*) :
  pi_lp p hp α ≃ Π (i : ι), α i :=
{ to_fun := id,
  inv_fun := id,
  left_inv := λ x, rfl,
  right_inv := λ x, rfl }

namespace emetric_space

variables (p : ℝ) (hp : 1 ≤ p) (α : ι → Type*) [∀ i, emetric_space (α i)] [fintype ι]

open filter

/-- Endowing the space `pi_lp p hp α` with the `L^p` edistance. This definition is not satisfactory,
as it does not register the fact that the topology and the uniform structure coincide with the
product one. Therefore, we do not register it as an instance. Using this as a temporary emetric
space instance, we will show that the uniform structure is equal (but not defeq) to the product one,
and then register an instance in which we replace the uniform structure by the product one using
this emetric space and `emetric_space.replace_uniformity`. -/
def pi_lp_aux : emetric_space (pi_lp p hp α) :=
have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
{ edist := λ f g, (∑ (i : ι), (edist (f i) (g i)) ^ p) ^ (1/p),
  edist_self := λ f, by simp [edist, ennreal.zero_rpow_of_pos pos,
                     ennreal.zero_rpow_of_pos (inv_pos.2 pos)],
  edist_comm := λ f g, by simp [edist, edist_comm],
  edist_triangle := λ f g h, calc
    (∑ (i : ι), edist (f i) (h i) ^ p) ^ (1 / p) ≤
    (∑ (i : ι), (edist (f i) (g i) + edist (g i) (h i)) ^ p) ^ (1 / p) :
    begin
      apply ennreal.rpow_le_rpow _ (div_nonneg zero_le_one pos),
      refine finset.sum_le_sum (λ i hi, _),
      exact ennreal.rpow_le_rpow (edist_triangle _ _ _) (le_trans zero_le_one hp)
    end
    ... ≤
    (∑ (i : ι), edist (f i) (g i) ^ p) ^ (1 / p) + (∑ (i : ι), edist (g i) (h i) ^ p) ^ (1 / p) :
      finset.sum_rpow_minkowski_ennreal hp,
  eq_of_edist_eq_zero := λ f g hfg, begin
    simp [edist, ennreal.rpow_eq_zero_iff, pos, asymm pos, finset.sum_eq_zero_iff_of_nonneg] at hfg,
    exact funext hfg
  end }

local attribute [instance] emetric_space.pi_lp_aux

lemma lipschitz_with_pi_lp_equiv : lipschitz_with 1 (pi_lp_equiv p hp α) :=
begin
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  have cancel : p * (1/p) = 1 := mul_div_cancel' 1 (ne_of_gt pos),
  assume x y,
  simp only [edist, forall_prop_of_true, one_mul, finset.mem_univ, finset.sup_le_iff,
             ennreal.coe_one],
  assume i,
  calc edist (x i) (y i)
  = (edist (x i) (y i) ^ p) ^ (1/p) :
    by simp [← ennreal.rpow_mul, cancel, -one_div_eq_inv]
  ... ≤ (∑ (i : ι), edist (x i) (y i) ^ p) ^ (1 / p) :
  begin
    apply ennreal.rpow_le_rpow _ (div_nonneg zero_le_one pos),
    apply finset.single_le_sum (λ i hi, _) (finset.mem_univ i),
    exact bot_le
  end
end

lemma antilipschitz_with_pi_lp_equiv :
  antilipschitz_with ((fintype.card ι : nnreal) ^ (1/p)) (pi_lp_equiv p hp α) :=
begin
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  have cancel : p * (1/p) = 1 := mul_div_cancel' 1 (ne_of_gt pos),
  assume x y,
  simp [edist, -one_div_eq_inv],
  calc (∑ (i : ι), edist (x i) (y i) ^ p) ^ (1 / p) ≤
  (∑ (i : ι), edist (pi_lp_equiv p hp α x) (pi_lp_equiv p hp α y) ^ p) ^ (1 / p) :
  begin
    apply ennreal.rpow_le_rpow _ (div_nonneg zero_le_one pos),
    apply finset.sum_le_sum (λ i hi, _),
    apply ennreal.rpow_le_rpow _ (le_of_lt pos),
    exact finset.le_sup (finset.mem_univ i)
  end
  ... = (((fintype.card ι : nnreal)) ^ (1/p) : nnreal) *
    edist (pi_lp_equiv p hp α x) (pi_lp_equiv p hp α y) :
  begin
    simp only [nsmul_eq_mul, finset.card_univ, ennreal.rpow_one, finset.sum_const,
      ennreal.mul_rpow_of_nonneg _ _ (div_nonneg zero_le_one pos), ←ennreal.rpow_mul, cancel],
    have : (fintype.card ι : ennreal) = (fintype.card ι : nnreal) :=
      (ennreal.coe_nat (fintype.card ι)).symm,
    rw [this, ennreal.coe_rpow_of_nonneg _ (div_nonneg zero_le_one pos)]
  end
end

lemma pi_lp_aux_uniformity_eq :
  𝓤 (pi_lp p hp α) = @uniformity _ (Pi.uniform_space _) :=
begin
  have A : uniform_embedding (pi_lp_equiv p hp α) :=
    (antilipschitz_with_pi_lp_equiv p hp α).uniform_embedding
      (lipschitz_with_pi_lp_equiv p hp α).uniform_continuous,
  have : (λ (x : pi_lp p hp α × pi_lp p hp α),
    ((pi_lp_equiv p hp α) x.fst, (pi_lp_equiv p hp α) x.snd)) = id,
    by ext i; refl,
  rw [← A.comap_uniformity, this, comap_id],
end

end emetric_space

instance topological_space.pi_lp (p : ℝ) (hp : 1 ≤ p) (α : ι → Type*)
  [∀ i, topological_space (α i)] : topological_space (pi_lp p hp α) :=
Pi.topological_space

instance uniform_space.pi_lp (p : ℝ) (hp : 1 ≤ p) (α : ι → Type*)
  [∀ i, uniform_space (α i)] : uniform_space (pi_lp p hp α) :=
Pi.uniform_space _

instance emetric_space.pi_lp [fintype ι] (p : ℝ) (hp : 1 ≤ p) (α : ι → Type*)
  [∀ i, emetric_space (α i)] : emetric_space (pi_lp p hp α) :=
(emetric_space.pi_lp_aux p hp α).replace_uniformity
  (emetric_space.pi_lp_aux_uniformity_eq p hp α).symm

lemma emetric_space.pi_lp_edist [fintype ι] {p : ℝ} {hp : 1 ≤ p} {α : ι → Type*}
  [∀ i, emetric_space (α i)] (x y : pi_lp p hp α) :
  edist x y = (∑ (i : ι), (edist (x i) (y i)) ^ p) ^ (1/p) := rfl

instance metric_space.pi_lp [fintype ι] (p : ℝ) (hp : 1 ≤ p) (α : ι → Type*)
  [∀ i, metric_space (α i)] : metric_space (pi_lp p hp α) :=
begin
  /- we construct the instance from the emetric space instance to avoid checking again that the
  uniformity is the same as the product uniformity, but we register nevertheless a nice formula
  for the distance -/
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  refine emetric_space.to_metric_space_of_dist
    (λf g, (∑ (i : ι), (dist (f i) (g i)) ^ p) ^ (1/p)) _ _,
  { assume f g,
    simp [emetric_space.pi_lp_edist, ennreal.rpow_eq_top_iff, asymm pos, pos,
          ennreal.sum_eq_top_iff, edist_ne_top] },
  { assume f g,
    have A : ∀ (i : ι), i ∈ (finset.univ : finset ι) → edist (f i) (g i) ^ p < ⊤ :=
      λ i hi, by simp [lt_top_iff_ne_top, edist_ne_top, le_of_lt pos],
    simp [dist, -one_div_eq_inv, emetric_space.pi_lp_edist, ← ennreal.to_real_rpow,
          ennreal.to_real_sum A, dist_edist] }
end

lemma metric_space.pi_lp_dist [fintype ι] {p : ℝ} {hp : 1 ≤ p} {α : ι → Type*}
  [∀ i, metric_space (α i)] (x y : pi_lp p hp α) :
  dist x y = (∑ (i : ι), (dist (x i) (y i)) ^ p) ^ (1/p) := rfl
