/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import geometry.manifold.smooth_manifold_with_corners
import linear_algebra.finite_dimensional
import analysis.normed_space.real_inner_product

/-!
# Constructing examples of manifolds over ℝ

We introduce the necessary bits to be able to define manifolds modelled over `ℝ^n`, boundaryless
or with boundary or with corners. As a concrete example, we construct explicitly the manifold with
boundary structure on the real interval `[x, y]`.

More specifically, we introduce
* `model_with_corners ℝ (euclidean_space n) (euclidean_half_space n)` for the model space used
to define `n`-dimensional real manifolds with boundary
* `model_with_corners ℝ (euclidean_space n) (euclidean_quadrant n)` for the model space used
to define `n`-dimensional real manifolds with corners

## Implementation notes

The manifold structure on the interval `[x, y] = Icc x y` requires the assumption `x < y` as a
typeclass. We provide it as `[fact (x < y)]`.
-/

noncomputable theory
open set

/--
The half-space in `ℝ^n`, used to model manifolds with boundary. We only define it when
`1 ≤ n`, as the definition only makes sense in this case.
-/
def euclidean_half_space (n : ℕ) [has_zero (fin n)] : Type :=
{x : euclidean_space (fin n) // 0 ≤ x 0}

/--
The quadrant in `ℝ^n`, used to model manifolds with corners, made of all vectors with nonnegative
coordinates.
-/
def euclidean_quadrant (n : ℕ) : Type := {x : euclidean_space (fin n) // ∀i:fin n, 0 ≤ x i}

section
/- Register class instances for euclidean space and half-space and quadrant, that can not be noticed
without the following reducibility attribute (which is only set in this section). -/
local attribute [reducible] euclidean_half_space euclidean_quadrant
variable {n : ℕ}

instance [has_zero (fin n)] : topological_space (euclidean_half_space n) := by apply_instance
instance : topological_space (euclidean_quadrant n) := by apply_instance
instance [has_zero (fin n)] : inhabited (euclidean_half_space n) := ⟨⟨0, le_refl _⟩⟩
instance : inhabited (euclidean_quadrant n) := ⟨⟨0, λ i, le_refl _⟩⟩

lemma range_half_space (n : ℕ) [has_zero (fin n)] :
  range (λx : euclidean_half_space n, x.val) = {y | 0 ≤ y 0 } :=
by simp

lemma range_quadrant (n : ℕ) :
  range (λx : euclidean_quadrant n, x.val) = {y | ∀i:fin n, 0 ≤ y i } :=
by simp

end

/--
Definition of the model with corners `(euclidean_space (fin n), euclidean_half_space n)`, used as a
model for manifolds with boundary.
-/
def model_with_corners_euclidean_half_space (n : ℕ) [has_zero (fin n)] :
  model_with_corners ℝ (euclidean_space (fin n)) (euclidean_half_space n) :=
{ to_fun      := λx, x.val,
  inv_fun     := λx, ⟨λi, if h : i = 0 then max (x i) 0 else x i, by simp [le_refl]⟩,
  source      := univ,
  target      := range (λx : euclidean_half_space n, x.val),
  map_source' := λx hx, by simpa [-mem_range, mem_range_self] using x.property,
  map_target' := λx hx, mem_univ _,
  left_inv'   := λ⟨xval, xprop⟩ hx, begin
    rw subtype.mk_eq_mk,
    ext1 i,
    by_cases hi : i = 0,
    { rw hi, simp [hi, xprop] },
    { simp [hi] }
  end,
  right_inv'  := λx hx, begin
    simp [range_half_space] at hx,
    ext1 i,
    by_cases hi : i = 0,
    { rw hi, simp [hi, hx] },
    { simp [hi] }
  end,
  source_eq    := rfl,
  unique_diff' := begin
    /- To check that the half-space has the unique differentiability property, we use the criterion
    `unique_diff_on_convex`: it suffices to check that it is convex and with nonempty interior. -/
    rw range_half_space,
    apply unique_diff_on_convex,
    show convex {y : euclidean_space (fin n) | 0 ≤ y 0},
    { assume x y hx hy a b ha hb hab,
      simpa using add_le_add (mul_nonneg ha hx) (mul_nonneg hb hy) },
    show (interior {y : euclidean_space (fin n) | 0 ≤ y 0}).nonempty,
    { use (λi, 1),
      rw mem_interior,
      refine ⟨(pi (univ : set (fin n)) (λi, (Ioi 0 : set ℝ))), _,
        is_open_set_pi finite_univ (λa ha, is_open_Ioi), _⟩,
      { assume x hx,
        simp [pi] at hx,
        exact le_of_lt (hx 0) },
      { simp only [pi, forall_prop_of_true, mem_univ, mem_Ioi],
        assume i,
        exact zero_lt_one } }
  end,
  continuous_to_fun  := continuous_subtype_val,
  continuous_inv_fun := begin
    apply continuous_subtype_mk,
    apply continuous_pi,
    assume i,
    by_cases h : i = 0,
    { rw h,
      simp only [dif_pos],
      have : continuous (λx:ℝ, max x 0) := continuous_id.max continuous_const,
      exact this.comp (continuous_apply 0) },
    { simp [h],
      exact continuous_apply i }
  end }

/--
Definition of the model with corners `(euclidean_space (fin n), euclidean_quadrant n)`, used as a
model for manifolds with corners -/
def model_with_corners_euclidean_quadrant (n : ℕ) :
  model_with_corners ℝ (euclidean_space (fin n)) (euclidean_quadrant n) :=
{ to_fun      := λx, x.val,
  inv_fun     := λx, ⟨λi, max (x i) 0, λi, by simp [le_refl]⟩,
  source      := univ,
  target      := range (λx : euclidean_quadrant n, x.val),
  map_source' := λx hx, by simpa [-mem_range, mem_range_self] using x.property,
  map_target' := λx hx, mem_univ _,
  left_inv'   := λ⟨xval, xprop⟩ hx, begin
    rw subtype.mk_eq_mk,
    ext1 i,
    simp [xprop i]
  end,
  right_inv' := λx hx, begin
    rw range_quadrant at hx,
    ext1 i,
    simp [hx i]
  end,
  source_eq    := rfl,
  unique_diff' := begin
    /- To check that the quadrant has the unique differentiability property, we use the criterion
    `unique_diff_on_convex`: it suffices to check that it is convex and with nonempty interior. -/
    rw range_quadrant,
    apply unique_diff_on_convex,
    show convex {y : euclidean_space (fin n) | ∀ (i : fin n), 0 ≤ y i},
    { assume x y hx hy a b ha hb hab i,
      simpa using add_le_add (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i)) },
    show (interior {y : euclidean_space (fin n) | ∀ (i : fin n), 0 ≤ y i}).nonempty,
    { use (λi, 1),
      rw mem_interior,
      refine ⟨(pi (univ : set (fin n)) (λi, (Ioi 0 : set ℝ))), _,
        is_open_set_pi finite_univ (λa ha, is_open_Ioi), _⟩,
      { assume x hx i,
        simp [pi] at hx,
        exact le_of_lt (hx i) },
      { simp only [pi, forall_prop_of_true, mem_univ, mem_Ioi],
        assume i,
        exact zero_lt_one } }
  end,
  continuous_to_fun  := continuous_subtype_val,
  continuous_inv_fun := begin
    apply continuous_subtype_mk,
    apply continuous_pi,
    assume i,
    have : continuous (λx:ℝ, max x 0) := continuous.max continuous_id continuous_const,
    exact this.comp (continuous_apply i)
  end }

localized "notation `𝓡 `n := model_with_corners_self ℝ (euclidean_space (fin n))" in manifold
localized "notation `𝓡∂ `n := model_with_corners_euclidean_half_space n" in manifold


/--
The left chart for the topological space `[x, y]`, defined on `[x,y)` and sending `x` to `0` in
`euclidean_half_space 1`.
-/
def Icc_left_chart (x y : ℝ) [fact (x < y)] :
  local_homeomorph (Icc x y) (euclidean_half_space 1) :=
{ source      := {z : Icc x y | z.val < y},
  target      := {z : euclidean_half_space 1 | z.val 0 < y - x},
  to_fun      := λ(z : Icc x y), ⟨λi, z.val - x, sub_nonneg.mpr z.property.1⟩,
  inv_fun     := λz, ⟨min (z.val 0 + x) y, by simp [le_refl, z.property, le_of_lt ‹x < y›]⟩,
  map_source' := by simp,
  map_target' := by { simp, assume z hz, left, dsimp at hz, linarith },
  left_inv'   := by { rintros ⟨z, hz⟩ h'z, simp at hz h'z, simp [hz, h'z] },
  right_inv'  := begin
    rintros ⟨z, hz⟩ h'z,
    rw subtype.mk_eq_mk,
    funext,
    dsimp at hz h'z,
    have A : x + z 0 ≤ y, by linarith,
    rw subsingleton.elim i 0,
    simp [A, add_comm],
  end,
  open_source := begin
    have : is_open {z : ℝ | z < y} := is_open_Iio,
    exact continuous_subtype_val _ this
  end,
  open_target := begin
    have : is_open {z : ℝ | z < y - x} := is_open_Iio,
    have : is_open {z : euclidean_space (fin 1) | z 0 < y - x} :=
      @continuous_apply (fin 1) (λ _, ℝ) _ 0 _ this,
    exact continuous_subtype_val _ this
  end,
  continuous_to_fun := begin
    apply continuous.continuous_on,
    apply continuous_subtype_mk,
    have : continuous (λ (z : ℝ) (i : fin 1), z - x) :=
      continuous.sub (continuous_pi $ λi, continuous_id) continuous_const,
    exact this.comp continuous_subtype_val,
  end,
  continuous_inv_fun := begin
    apply continuous.continuous_on,
    apply continuous_subtype_mk,
    have A : continuous (λ z : ℝ, min (z + x) y) :=
      (continuous_id.add continuous_const).min continuous_const,
    have B : continuous (λz : euclidean_space (fin 1), z 0) := continuous_apply 0,
    exact (A.comp B).comp continuous_subtype_val
  end }

/--
The right chart for the topological space `[x, y]`, defined on `(x,y]` and sending `y` to `0` in
`euclidean_half_space 1`.
-/
def Icc_right_chart (x y : ℝ) [fact (x < y)] :
  local_homeomorph (Icc x y) (euclidean_half_space 1) :=
{ source      := {z : Icc x y | x < z.val},
  target      := {z : euclidean_half_space 1 | z.val 0 < y - x},
  to_fun      := λ(z : Icc x y), ⟨λi, y - z.val, sub_nonneg.mpr z.property.2⟩,
  inv_fun     := λz,
    ⟨max (y - z.val 0) x, by simp [le_refl, z.property, le_of_lt ‹x < y›, sub_eq_add_neg]⟩,
  map_source' := by simp,
  map_target' := by { simp, assume z hz, left, dsimp at hz, linarith },
  left_inv'   := by { rintros ⟨z, hz⟩ h'z, simp at hz h'z, simp [hz, h'z, sub_eq_add_neg] },
  right_inv'  := begin
    rintros ⟨z, hz⟩ h'z,
    rw subtype.mk_eq_mk,
    funext,
    dsimp at hz h'z,
    have A : x ≤ y - z 0, by linarith,
    rw subsingleton.elim i 0,
    simp [A, sub_sub_cancel],
  end,
  open_source := begin
    have : is_open {z : ℝ | x < z} := is_open_Ioi,
    exact continuous_subtype_val _ this
  end,
  open_target := begin
    have : is_open {z : ℝ | z < y - x} := is_open_Iio,
    have : is_open {z : euclidean_space (fin 1) | z 0 < y - x} :=
      @continuous_apply (fin 1) (λ _, ℝ) _ 0 _ this,
    exact continuous_subtype_val _ this
  end,
  continuous_to_fun := begin
    apply continuous.continuous_on,
    apply continuous_subtype_mk,
    have : continuous (λ (z : ℝ) (i : fin 1), y - z) :=
      continuous_const.sub (continuous_pi (λi, continuous_id)),
    exact this.comp continuous_subtype_val,
  end,
  continuous_inv_fun := begin
    apply continuous.continuous_on,
    apply continuous_subtype_mk,
    have A : continuous (λ z : ℝ, max (y - z) x) :=
      (continuous_const.sub continuous_id).max continuous_const,
    have B : continuous (λz : euclidean_space (fin 1), z 0) := continuous_apply 0,
    exact (A.comp B).comp continuous_subtype_val
  end }

/--
Manifold with boundary structure on `[x, y]`, using only two charts.
-/
instance Icc_manifold (x y : ℝ) [fact (x < y)] : manifold (euclidean_half_space 1) (Icc x y) :=
{ atlas := {Icc_left_chart x y, Icc_right_chart x y},
  chart_at := λz, if z.val < y then Icc_left_chart x y else Icc_right_chart x y,
  mem_chart_source := λz, begin
    by_cases h' : z.val < y,
    { simp only [h', if_true],
      exact h' },
    { simp only [h', if_false],
      apply lt_of_lt_of_le ‹x < y›,
      simpa using h' }
  end,
  chart_mem_atlas := λz, by { by_cases h' : z.val < y; simp [h'] } }

/--
The manifold structure on `[x, y]` is smooth.
-/
instance Icc_smooth_manifold (x y : ℝ) [fact (x < y)] :
  smooth_manifold_with_corners (𝓡∂ 1) (Icc x y) :=
begin
  have M : times_cont_diff_on ℝ ⊤ (λz : euclidean_space (fin 1), - z + (λi, y - x)) univ,
  { rw times_cont_diff_on_univ,
    exact times_cont_diff_id.neg.add times_cont_diff_const  },
  haveI : has_groupoid (Icc x y)
          (times_cont_diff_groupoid ⊤ (model_with_corners_euclidean_half_space 1)) :=
  begin
    apply has_groupoid_of_pregroupoid,
    assume e e' he he',
    simp [atlas] at he he',
    /- We need to check that any composition of two charts gives a `C^∞` function. Each chart can be
    either the left chart or the right chart, leaving 4 possibilities that we handle successively.
    -/
    rcases he with rfl | rfl; rcases he' with rfl | rfl,
    { -- `e = left chart`, `e' = left chart`
      refine ((mem_groupoid_of_pregroupoid _ _).mpr _).1,
      exact symm_trans_mem_times_cont_diff_groupoid _ _ _ },
    { -- `e = left chart`, `e' = right chart`
      apply M.congr_mono _ (subset_univ _),
      assume z hz,
      simp [-mem_range, range_half_space, model_with_corners_euclidean_half_space,
            local_equiv.trans_source, Icc_left_chart, Icc_right_chart] at hz,
      have A : 0 ≤ z 0 := hz.2,
      have B : z 0 + x ≤ y, by { have := hz.1.1.1, linarith },
      ext i,
      rw subsingleton.elim i 0,
      simp [model_with_corners_euclidean_half_space, Icc_left_chart, Icc_right_chart, A, B],
      ring },
    { -- `e = right chart`, `e' = left chart`
      apply M.congr_mono _ (subset_univ _),
      assume z hz,
      simp [-mem_range, range_half_space, model_with_corners_euclidean_half_space,
            local_equiv.trans_source, Icc_left_chart, Icc_right_chart] at hz,
      have A : 0 ≤ z 0 := hz.2,
      have B : x ≤ y - z 0, by { have := hz.1.1.1, dsimp at this, linarith },
      ext i,
      rw subsingleton.elim i 0,
      simp [model_with_corners_euclidean_half_space, Icc_left_chart, Icc_right_chart, A, B],
      ring },
    { -- `e = right chart`, `e' = right chart`
      refine ((mem_groupoid_of_pregroupoid _ _).mpr _).1,
      exact symm_trans_mem_times_cont_diff_groupoid _ _ _ }
  end,
  constructor
end
