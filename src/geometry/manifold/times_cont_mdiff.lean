/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import geometry.manifold.mfderiv

/-!
# Smooth functions between smooth manifolds

We define `Cⁿ` functions between smooth manifolds, as functions which are `Cⁿ` in charts, and prove
basic properties of these notions.

## Main definitions and statements

Let `M ` and `M'` be two smooth manifolds, with respect to model with corners `I` and `I'`. Let
`f : M → M'`.

* `times_cont_mdiff_on I I' n f s` states that the function `f` is `Cⁿ` on the set `s`
* `times_cont_mdiff I I' n f` states that the function `f` is `Cⁿ`.
* `times_cont_mdiff_on.comp` gives the invariance of the `Cⁿ` property under composition
* `times_cont_mdiff_on.times_cont_mdiff_on_bundle_mfderiv_within` states that the bundled derivative
  of a `Cⁿ` function is `Cᵐ` when `m < n`.

-/

open set

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [manifold H M] [smooth_manifold_with_corners I M]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [manifold H' M'] [smooth_manifold_with_corners I' M']
{f f₁ : M → M'} {s s₁ : set M} {x : M}
{m n : with_top ℕ}

/-- A function is `n` times continuously differentiable in a set of a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable on this set in the charts
around these points. -/
def times_cont_mdiff_on (n : with_top ℕ) (f : M → M') (s : set M) :=
continuous_on f s ∧
∀(x : M) (y : M'), times_cont_diff_on 𝕜 n ((ext_chart_at I' y) ∘ f ∘ (ext_chart_at I x).symm)
  ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' y).source))

/-- A function is `n` times continuously differentiable in a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable in the charts
around these points. -/
def times_cont_mdiff (n : with_top ℕ) (f : M → M') :=
continuous f ∧
∀(x : M) (y : M'), times_cont_diff_on 𝕜 n ((ext_chart_at I' y) ∘ f ∘ (ext_chart_at I x).symm)
  ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (f ⁻¹' (ext_chart_at I' y).source))

variables {I I'}

lemma times_cont_mdiff_on.of_le
 (hf : times_cont_mdiff_on I I' n f s) (le : m ≤ n) : times_cont_mdiff_on I I' m f s :=
⟨hf.1, λx y, (hf.2 x y).of_le le⟩

lemma times_cont_mdiff_on.of_succ {n : ℕ} (h : times_cont_mdiff_on I I' n.succ f s) :
  times_cont_mdiff_on I I' n f s :=
h.of_le (with_top.coe_le_coe.2 (nat.le_succ n))

lemma times_cont_mdiff_on.continuous_on (hf : times_cont_mdiff_on I I' n f s) :
  continuous_on f s :=
hf.1

lemma times_cont_mdiff_on.mdifferentiable_on (hf : times_cont_mdiff_on I I' n f s) (hn : 1 ≤ n) :
  mdifferentiable_on I I' f s :=
begin
  assume x hx,
  suffices h : mdifferentiable_within_at I I' f (s ∩ f ⁻¹' (ext_chart_at I' (f x)).source) x,
  { rwa mdifferentiable_within_at_inter' at h,
    apply (hf.1 x hx).preimage_mem_nhds_within,
    exact mem_nhds_sets (ext_chart_at_open_source I' (f x)) (mem_ext_chart_source I' (f x)) },
  rw mdifferentiable_within_at_iff,
  exact ⟨(hf.1 x hx).mono (inter_subset_left _ _),
    ((hf.2 x (f x)).differentiable_on hn) ((ext_chart_at I x) x)
    (by simp [local_equiv.map_source, hx])⟩
end

lemma times_cont_mdiff_on.mdifferentiable_within_at
  (hf : times_cont_mdiff_on I I' n f s) (hn : 1 ≤ n) (hx : x ∈ s) :
  mdifferentiable_within_at I I' f s x :=
hf.mdifferentiable_on hn x hx

lemma times_cont_mdiff_on_top :
  times_cont_mdiff_on I I' ⊤ f s ↔ (∀n:ℕ, times_cont_mdiff_on I I' n f s) :=
begin
  split,
  { assume h n,
    exact h.of_le le_top },
  { assume h,
    refine ⟨(h 1).1, λx hx, _⟩,
    rw times_cont_diff_on_top,
    assume n,
    exact (h n).2 x hx }
end

lemma times_cont_mdiff_on.congr_mono (hf : times_cont_mdiff_on I I' n f s)
  (h : ∀x ∈ s₁, f₁ x = f x) (h₁ : s₁ ⊆ s) :
  times_cont_mdiff_on I I' n f₁ s₁ :=
begin
  have : continuous_on f₁ s₁ := continuous_on.congr_mono (hf.1) h h₁,
  refine ⟨this, λx y, times_cont_diff_on.congr_mono (hf.2 x y) _ _⟩,
  { assume z hz,
    have : ((ext_chart_at I x).symm z) ∈ s₁, by { simp at hz, exact hz.2.1 },
    simp [written_in_ext_chart_at, h _ this] },
  { rintros p ⟨hp₁, hp₂, hp₃⟩,
    refine ⟨hp₁, h₁ hp₂, _⟩,
    simpa [h _ hp₂] using hp₃ }
end

lemma times_cont_mdiff_on.congr (hf : times_cont_mdiff_on I I' n f s)
  (h : ∀x ∈ s, f₁ x = f x) :
  times_cont_mdiff_on I I' n f₁ s :=
times_cont_mdiff_on.congr_mono hf h (subset.refl _)

lemma times_cont_mdiff_on.congr_mono' (hf : times_cont_mdiff_on I I' n f s)
  (h : ∀x ∈ s₁, f₁ x = f x) (h₁ : s₁ ⊆ s) (le : m ≤ n) :
  times_cont_mdiff_on I I' m f₁ s₁ :=
times_cont_mdiff_on.of_le (hf.congr_mono h h₁) le

lemma times_cont_mdiff_on.mono (h : times_cont_mdiff_on I I' n f s)
  (hst : s₁ ⊆ s) : times_cont_mdiff_on I I' n f s₁ :=
times_cont_mdiff_on.congr_mono h (λx hx, rfl) hst

lemma times_cont_mdiff_on_univ :
  times_cont_mdiff_on I I' n f univ ↔ times_cont_mdiff I I' n f :=
by simp [times_cont_mdiff_on, times_cont_mdiff, continuous_iff_continuous_on_univ]

/-- Being `C^n` is a local property. -/
lemma times_cont_mdiff_on_of_locally_times_cont_mdiff_on
  (h : ∀x∈s, ∃u, is_open u ∧ x ∈ u ∧ times_cont_mdiff_on I I' n f (s ∩ u)) :
  times_cont_mdiff_on I I' n f s :=
begin
  have cont : continuous_on f s,
  { refine continuous_on_of_locally_continuous_on (λx hx, _),
    rcases h x hx with ⟨u, u_open, xu, hu⟩,
    exact ⟨u, u_open, xu, hu.1⟩ },
  refine ⟨cont, λx y, times_cont_diff_on_of_locally_times_cont_diff_on (λz hz, _)⟩,
  rcases h ((ext_chart_at I x).symm z) hz.2.1 with ⟨u, u_open, zu, hu⟩,
  rcases continuous_on_iff'.1 cont (ext_chart_at I' y).source (ext_chart_at_open_source _ _)
    with ⟨o, o_open, ho⟩,
  rw inter_comm at ho,
  rw ho at  ⊢ hz,
  refine ⟨I.symm ⁻¹' ((chart_at H x).target ∩ ((chart_at H x).symm ⁻¹' (o ∩ u))) , _, _, _⟩,
  show is_open (I.symm ⁻¹' ((chart_at H x).target ∩ ((chart_at H x).symm ⁻¹' (o ∩ u)))),
  { apply I.continuous_inv_fun,
    apply (chart_at H x).continuous_inv_fun.preimage_open_of_open (chart_at H x).open_target,
    exact is_open_inter o_open u_open },
  show z ∈ I.symm ⁻¹' ((chart_at H x).target ∩ ((chart_at H x).symm ⁻¹' (o ∩ u))),
  { simp [ext_chart_at, local_equiv.trans_target, -mem_range] at hz zu,
    simp [hz, zu] },
  show times_cont_diff_on 𝕜 n ((ext_chart_at I' y) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (o ∩ s) ∩
       I.symm ⁻¹' ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' (o ∩ u))),
  { have : ((ext_chart_at I x).target ∩
           (ext_chart_at I x).symm ⁻¹' (s ∩ u ∩ o ∩ f ⁻¹' (ext_chart_at I' y).source)) =
       ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (o ∩ s) ∩
       I.symm ⁻¹' (((chart_at H x).to_local_equiv).target ∩ (chart_at H x).symm ⁻¹' (o ∩ u))),
    { rw ← ho,
      ext p,
      simp [ext_chart_at, local_equiv.trans_target, -mem_range],
      split;
      { assume hp, simp [hp] } },
    rw ← this,
    have : times_cont_mdiff_on I I' n f (s ∩ u ∩ o) := hu.mono (inter_subset_left _ _),
    exact this.2 x y }
end

section composition

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [manifold H'' M''] [smooth_manifold_with_corners I'' M'']

/-- The composition of `C^n` functions on domains is `C^n`. -/
lemma times_cont_mdiff_on.comp {n : with_top ℕ} {t : set M'} {g : M' → M''}
  (hg : times_cont_mdiff_on I' I'' n g t) (hf : times_cont_mdiff_on I I' n f s)
  (st : s ⊆ f ⁻¹' t) : times_cont_mdiff_on I I'' n (g ∘ f) s :=
begin
  have cont_gf : continuous_on (g ∘ f) s := continuous_on.comp hg.1 hf.1 st,
  refine ⟨cont_gf, λx y, _⟩,
  apply times_cont_diff_on_of_locally_times_cont_diff_on,
  assume z hz,
  let x' := (ext_chart_at I x).symm z,
  have x'_source : x' ∈ (ext_chart_at I x).source := (ext_chart_at I x).map_target hz.1,
  obtain ⟨o, o_open, zo, o_subset⟩ : ∃ o, is_open o ∧ z ∈ o ∧
    o ∩ (((ext_chart_at I x).symm ⁻¹' s ∩ range I)) ⊆
      (ext_chart_at I x).symm ⁻¹' (f ⁻¹' (ext_chart_at I' (f x')).source) :=
  begin
    have x'z : (ext_chart_at I x) x' = z, by simp [x', hz.1],
    have : continuous_within_at f s x' := hf.1 _ hz.2.1,
    have : f ⁻¹' (ext_chart_at I' (f x')).source ∈ nhds_within x' s :=
      this.preimage_mem_nhds_within
      (mem_nhds_sets (ext_chart_at_open_source I' (f x')) (mem_ext_chart_source I' (f x'))),
    have : (ext_chart_at I x).symm ⁻¹' (f ⁻¹' (ext_chart_at I' (f x')).source) ∈
      nhds_within ((ext_chart_at I x) x') ((ext_chart_at I x).symm ⁻¹' s ∩ range I) :=
      ext_chart_preimage_mem_nhds_within' _ _ x'_source this,
    rw x'z at this,
    exact mem_nhds_within.1 this
  end,
  refine ⟨o, o_open, zo, _⟩,
  let u := ((ext_chart_at I x).target ∩
         (ext_chart_at I x).symm ⁻¹' (s ∩ g ∘ f ⁻¹' (ext_chart_at I'' y).source) ∩ o),
  -- it remains to show that `g ∘ f` read in the charts is `C^n` on `u`
  have u_subset : u ⊆ (ext_chart_at I x).target ∩
    (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' (f x')).source),
  { rintros p ⟨⟨hp₁, ⟨hp₂, hp₃⟩⟩, hp₄⟩,
    refine ⟨hp₁, ⟨hp₂, o_subset ⟨hp₄, ⟨hp₂, _⟩⟩⟩⟩,
    have := hp₁.1,
    rwa model_with_corners.target at this },
  have : times_cont_diff_on 𝕜 n (((ext_chart_at I'' y) ∘ g ∘ (ext_chart_at I' (f x')).symm) ∘
    ((ext_chart_at I' (f x')) ∘ f ∘ (ext_chart_at I x).symm)) u,
  { refine times_cont_diff_on.comp (hg.2 (f x') y) ((hf.2 x (f x')).mono u_subset) (λp hp, _),
    simp [local_equiv.map_source _ (u_subset hp).2.2, local_equiv.left_inv _ (u_subset hp).2.2],
    exact ⟨st (u_subset hp).2.1, hp.1.2.2⟩ },
  refine this.congr (λp hp, _),
  simp [local_equiv.left_inv _ (u_subset hp).2.2]
end

end composition

section atlas

variables {e : local_homeomorph M H} (𝕜)

/-- An atlas member is `C^∞`. -/
lemma times_cont_mdiff_on_atlas_aux (h : e ∈ atlas H M) :
  times_cont_mdiff_on I I ⊤ e e.source :=
begin
  refine ⟨e.continuous_to_fun, _⟩,
  assume x y,
  simp only [ext_chart_at, local_equiv.refl_trans, preimage_univ, inter_univ,
             chart_at_model_space_eq, local_homeomorph.refl_local_equiv, model_with_corners.source_eq,
             local_equiv.coe_trans_symm],
  have := has_groupoid.compatible (times_cont_diff_groupoid ⊤ I) (chart_mem_atlas H x) h,
  rw [times_cont_diff_groupoid, mem_groupoid_of_pregroupoid] at this,
  convert this.1 using 1,
  rw preimage_comp,
  simp [local_equiv.trans_source, local_equiv.trans_target],
  ext p,
  split;
  { assume hp, simp at hp, simp [hp] }
end

/-- An atlas member is `C^n` for any `n`. -/
lemma times_cont_mdiff_on_atlas (h : e ∈ atlas H M) (n : with_top ℕ) :
  times_cont_mdiff_on I I n e e.source :=
(times_cont_mdiff_on_atlas_aux 𝕜 h).of_le le_top

/-- The inverse of an atlas member is `C^∞`. -/
lemma times_cont_mdiff_on_atlas_symm_aux (h : e ∈ atlas H M) :
  times_cont_mdiff_on I I ⊤ e.symm e.target :=
begin
  refine ⟨e.continuous_inv_fun, _⟩,
  assume x y,
  simp only [ext_chart_at, local_equiv.refl_trans, model_with_corners.target, preimage_inter,
    chart_at_model_space_eq, local_homeomorph.refl_local_equiv, local_equiv.coe_trans,
    local_equiv.trans_source, preimage_univ, model_with_corners.to_local_equiv_coe_symm,
    local_homeomorph.coe_coe, inter_univ, model_with_corners.source_eq,
    model_with_corners.to_local_equiv_coe],
  have := has_groupoid.compatible (times_cont_diff_groupoid ⊤ I) h (chart_mem_atlas H y),
  rw [times_cont_diff_groupoid, mem_groupoid_of_pregroupoid] at this,
  convert this.1 using 1,
  simp only [local_equiv.trans_source, local_homeomorph.coe_coe_symm,
    local_homeomorph.trans_to_local_equiv, preimage_inter,
     local_equiv.symm_source, local_homeomorph.symm_to_local_equiv],
  rw preimage_comp,
  ext p,
  split;
  { assume hp, simp at hp, simp [hp] }
end

/-- The inverse of an atlas member is `C^n` for any `n`. -/
lemma times_cont_mdiff_on_atlas_symm (h : e ∈ atlas H M) (n : with_top ℕ) :
  times_cont_mdiff_on I I n e.symm e.target :=
(times_cont_mdiff_on_atlas_symm_aux 𝕜 h).of_le le_top

end atlas

section bundle_derivative

/-- If a function is `C^n` with `1 ≤ n`, then its bundled derivative is continuous. In this
auxiliary lemma, we prove this fact when the source and target space are model spaces in models
with corners. The general fact is proved in
`times_cont_mdiff_on.continuous_on_bundle_mfderiv_within`-/
lemma times_cont_mdiff_on.continuous_on_bundle_mfderiv_within_aux
  {f : H → H'} {s : set H}
  (hf : times_cont_mdiff_on I I' n f s) (hn : 1 ≤ n) (hs : unique_mdiff_on I s) :
  continuous_on (bundle_mfderiv_within I I' f s) ((tangent_bundle.proj I H) ⁻¹' s) :=
begin
  suffices h : continuous_on (λ (p : H × E), (f p.fst,
    (fderiv_within 𝕜 (written_in_ext_chart_at I I' p.fst f) (I.symm ⁻¹' s ∩ range I)
      ((ext_chart_at I p.fst) p.fst) : E →L[𝕜] E') p.snd)) (prod.fst ⁻¹' s),
  { have : ∀ (p : tangent_bundle I H), p ∈ tangent_bundle.proj I H ⁻¹' s →
      bundle_mfderiv_within I I' f s p =
      (f p.fst, ((fderiv_within 𝕜 (written_in_ext_chart_at I I' p.fst f)
      (I.symm ⁻¹' s ∩ range I) ((ext_chart_at I p.fst) p.fst)) : E →L[𝕜] E') p.snd),
    { rintros ⟨x, v⟩ hx,
      dsimp [bundle_mfderiv_within],
      ext, { refl },
      dsimp,
      apply congr_fun,
      apply congr_arg,
      rw mdifferentiable_within_at.mfderiv_within (hf.mdifferentiable_on hn x hx),
      refl },
    convert h.congr this,
    exact tangent_bundle_model_space_topology_eq_prod H I,
    exact tangent_bundle_model_space_topology_eq_prod H' I' },
  suffices h : continuous_on (λ (p : H × E), (fderiv_within 𝕜 (I' ∘ f ∘ I.symm)
    (I.symm ⁻¹' s ∩ range I) (I p.fst) : E →L[𝕜] E') p.snd) (prod.fst ⁻¹' s),
  { dsimp [written_in_ext_chart_at, ext_chart_at],
    apply continuous_on.prod
      (continuous_on.comp hf.1 continuous_fst.continuous_on (subset.refl _)),
    apply h.congr,
    assume p hp,
    refl },
  suffices h : continuous_on (fderiv_within 𝕜 (I' ∘ f ∘ I.symm)
                     (I.symm ⁻¹' s ∩ range I)) (I '' s),
  { have C := continuous_on.comp h I.continuous_to_fun.continuous_on (subset.refl _),
    have A : continuous (λq : (E →L[𝕜] E') × E, q.1 q.2) := is_bounded_bilinear_map_apply.continuous,
    have B : continuous_on (λp : H × E,
      (fderiv_within 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)
                       (I p.1), p.2)) (prod.fst ⁻¹' s),
    { apply continuous_on.prod _ continuous_snd.continuous_on,
      refine (continuous_on.comp C continuous_fst.continuous_on _ : _),
      exact preimage_mono (subset_preimage_image _ _) },
    exact A.comp_continuous_on B },
  let x : H := I.symm (0 : E),
  let y : H' := I'.symm (0 : E'),
  have A := hf.2 x y,
  simp [ext_chart_at, I.image, inter_comm] at A ⊢,
  apply A.continuous_on_fderiv_within _ hn,
  convert hs.unique_diff_on x using 1,
  simp [ext_chart_at, inter_comm]
end

/-- If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`. In this
auxiliary lemma, we prove this fact when the source and target space are model spaces in models
with corners. The general fact is proved in
`times_cont_mdiff_on.times_cont_mdiff_on_bundle_mfderiv_within` -/
lemma times_cont_mdiff_on.times_cont_mdiff_on_bundle_mfderiv_within_aux
  {f : H → H'} {s : set H}
  (hf : times_cont_mdiff_on I I' n f s) (hmn : m + 1 ≤ n) (hs : unique_mdiff_on I s) :
  times_cont_mdiff_on I.tangent I'.tangent m (bundle_mfderiv_within I I' f s)
    ((tangent_bundle.proj I H) ⁻¹' s) :=
begin
  have m_le_n : m ≤ n,
  { apply le_trans _ hmn,
    have : m + 0 ≤ m + 1 := add_le_add_left' bot_le,
    simpa using this },
  have one_le_n : 1 ≤ n,
  { apply le_trans _ hmn,
    change 0 + 1 ≤ m + 1,
    refine add_le_add_right' bot_le },
  have U': unique_diff_on 𝕜 (range I ∩ I.symm ⁻¹' s),
  { assume y hy,
    simpa [unique_mdiff_on, unique_mdiff_within_at, ext_chart_at, hy.1, inter_comm]
      using hs (I.symm y) hy.2 },
  have U : unique_diff_on 𝕜 (set.prod (range I ∩ I.symm ⁻¹' s) (univ : set E)) :=
    U'.prod unique_diff_on_univ,
  refine ⟨hf.continuous_on_bundle_mfderiv_within_aux one_le_n hs, λp q, _⟩,
  have A : (λ (p : E × E), (I.symm p.1, p.2)) ⁻¹' (tangent_bundle.proj I H ⁻¹' s)
           = set.prod (I.symm ⁻¹' s) univ,
    by { ext p, simp [tangent_bundle.proj] },
  -- unfold the definitions to reduce to a statement on vector spaces
  suffices h : times_cont_diff_on 𝕜 m
    ((λ (p : H' × E'), (I' p.1, p.2)) ∘ bundle_mfderiv_within I I' f s ∘
        λ (p : E × E), (I.symm p.1, p.2))
    (set.prod (range I ∩ I.symm ⁻¹' s) univ),
  by simp [ext_chart_at, @local_equiv.refl_symm (H × E),
           local_equiv.trans_target, model_with_corners.prod, @local_equiv.refl_target (H × E),
           local_equiv.trans_source, @local_equiv.refl_source (H' × E'), h, A, prod_inter_prod,
           model_with_corners.tangent],
  change times_cont_diff_on 𝕜 m (λ (p : E × E),
    ((I' (f (I.symm p.fst)), ((mfderiv_within I I' f s (I.symm p.fst)) : E → E') p.snd) : E' × E'))
    (set.prod (range I ∩ I.symm ⁻¹' s) univ),
  -- check that all bits in this formula are `C^n`
  have A : times_cont_diff_on 𝕜 m (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) :=
    by simpa [ext_chart_at] using (hf.2 (I.symm 0) (I'.symm 0)).of_le m_le_n,
  have B : times_cont_diff_on 𝕜 m ((I' ∘ f ∘ I.symm) ∘ prod.fst)
           (set.prod (range I ∩ I.symm ⁻¹' s) (univ : set E)) :=
    A.comp (times_cont_diff_fst.times_cont_diff_on) (prod_subset_preimage_fst _ _),
  suffices C : times_cont_diff_on 𝕜 m (λ (p : E × E),
    ((fderiv_within 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) p.1 : _) p.2))
    (set.prod (range I ∩ I.symm ⁻¹' s) univ),
  { apply times_cont_diff_on.prod B _,
    apply C.congr (λp hp, _),
    unfold_coes,
    congr,
    simp [-mem_range] at hp,
    simp [mfderiv_within, hf.mdifferentiable_within_at one_le_n hp.2, written_in_ext_chart_at,
          ext_chart_at, hp.1] },
  have D : times_cont_diff_on 𝕜 m (λ x,
    (fderiv_within 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) x))
    (range I ∩ I.symm ⁻¹' s),
  { have : times_cont_diff_on 𝕜 n (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) :=
      by simpa [ext_chart_at] using (hf.2 (I.symm 0) (I'.symm 0)),
    simpa [inter_comm] using this.fderiv_within U' hmn },
  have := D.comp (times_cont_diff_fst.times_cont_diff_on) (prod_subset_preimage_fst _ _),
  have := times_cont_diff_on.prod this (times_cont_diff_snd.times_cont_diff_on),
  exact is_bounded_bilinear_map_apply.times_cont_diff.comp_times_cont_diff_on this,
end

/-- If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`. -/
theorem times_cont_mdiff_on.times_cont_mdiff_on_bundle_mfderiv_within
  (hf : times_cont_mdiff_on I I' n f s) (hmn : m + 1 ≤ n) (hs : unique_mdiff_on I s) :
  times_cont_mdiff_on I.tangent I'.tangent m (bundle_mfderiv_within I I' f s)
  ((tangent_bundle.proj I M) ⁻¹' s) :=
begin
  /- The strategy of the proof is to avoid unfolding the definitions, and reduce by functoriality
  to the case of functions on the model spaces, where we have already proved the result.
  Let `l` and `r` be the charts to the left and to the right, so that we have
  ```
     l      f       r
  H ---> M ---> M' ---> H'
  ```
  Then the derivative `D(r ∘ f ∘ l)` is smooth by a previous result. Consider the composition
  ```
      Dl^{-1}          il      D(r ∘ f ∘ l)       ir            Dr^{-1}
  TM ---------> H × E ---> TH -------------> TH' ---> H' × E' ----------> TM'
  ```
  where `Dr^{-1}` and `Dl^{-1}` denote the charts on `TM` and `TM'` (they are smooth, by definition
  of charts) and `ir` and `il` are charts of `TH` and `TH'`, also smooth (they are the identity,
  between two Types which are defeq but which carry two manifold structures which are not defeq a
  priori, which is why they are needed here). The composition of all these maps is `Df`, and is
  therefore smooth as a composition of smooth maps.
  -/
  have m_le_n : m ≤ n,
  { apply le_trans _ hmn,
    have : m + 0 ≤ m + 1 := add_le_add_left' bot_le,
    simpa },
  have one_le_n : 1 ≤ n,
  { apply le_trans _ hmn,
    change 0 + 1 ≤ m + 1,
    exact add_le_add_right' bot_le },
  /- First step: local reduction on the space, to a set `s'` which is contained in chart domains. -/
  refine times_cont_mdiff_on_of_locally_times_cont_mdiff_on (λp hp, _),
  simp [tangent_bundle.proj] at hp,
  let l  := chart_at H p.1,
  let Dl := chart_at (H × E) p,
  let r  := chart_at H' (f p.1),
  let Dr := chart_at (H' × E') (bundle_mfderiv_within I I' f s p),
  let il := chart_at (H × E) (bundle_mfderiv I I l p),
  let ir := chart_at (H' × E') (bundle_mfderiv I I' (r ∘ f) p),
  let s' := f ⁻¹' r.source ∩ s ∩ l.source,
  let s'_lift := (tangent_bundle.proj I M)⁻¹' s',
  let s'l := l.target ∩ l.symm ⁻¹' s',
  let s'l_lift := (tangent_bundle.proj I H) ⁻¹' s'l,
  rcases continuous_on_iff'.1 hf.1 r.source r.open_source with ⟨o, o_open, ho⟩,
  suffices h : times_cont_mdiff_on I.tangent I'.tangent m (bundle_mfderiv_within I I' f s) s'_lift,
  { refine ⟨(tangent_bundle.proj I M)⁻¹' (o ∩ l.source), _, _, _⟩,
    show is_open ((tangent_bundle.proj I M)⁻¹' (o ∩ l.source)), from
      tangent_bundle_proj_continuous _ _ _ (is_open_inter o_open l.open_source),
    show p ∈ tangent_bundle.proj I M ⁻¹' (o ∩ l.source),
    { simp [tangent_bundle.proj] at ⊢,
      have : p.1 ∈ f ⁻¹' r.source ∩ s, by simp [hp],
      rw ho at this,
      exact this.1 },
    have : tangent_bundle.proj I M ⁻¹' s ∩ tangent_bundle.proj I M ⁻¹' (o ∩ l.source) = s'_lift,
    { dsimp only [s'_lift, s'],
      rw [ho],
      ext p,
      split;
      { assume hp, simp at hp, simp [hp] } },
    rw this,
    exact h },
  /- Second step: check that all functions are smooth, and use the chain rule to write the bundled
  derivative as a composition of a function between model spaces and of charts. -/
  have U' : unique_mdiff_on I s',
  { apply unique_mdiff_on.inter _ l.open_source,
    rw [ho, inter_comm],
    exact hs.inter o_open },
  have U'l : unique_mdiff_on I s'l :=
    U'.unique_mdiff_on_preimage (mdifferentiable_chart _ _),
  have diff_f : times_cont_mdiff_on I I' n f s',
  { apply hf.mono (λx hx, _),
    simp [s'] at hx, simp [hx] },
  have diff_r : times_cont_mdiff_on I' I' n r r.source :=
    times_cont_mdiff_on_atlas _ (chart_mem_atlas _ _) _,
  have diff_rf : times_cont_mdiff_on I I' n (r ∘ f) s',
  { apply times_cont_mdiff_on.comp diff_r diff_f (λx hx, _),
    simp [s'] at hx, simp [hx] },
  have diff_l : times_cont_mdiff_on I I n l.symm s'l,
  { have A : times_cont_mdiff_on I I n l.symm l.target :=
      times_cont_mdiff_on_atlas_symm _ (chart_mem_atlas _ _) _,
    refine A.mono (λx hx, _),
    simp [s'l] at hx, simp [hx] },
  have diff_rfl : times_cont_mdiff_on I I' n (r ∘ f ∘ l.symm) s'l,
  { apply times_cont_mdiff_on.comp diff_rf diff_l (λx hx, _),
    simp [s'l] at hx, simp [hx] },
  have diff_rfl_lift : times_cont_mdiff_on I.tangent I'.tangent m
      (bundle_mfderiv_within I I' (r ∘ f ∘ l.symm) s'l) s'l_lift :=
    diff_rfl.times_cont_mdiff_on_bundle_mfderiv_within_aux hmn U'l,
  have diff_irrfl_lift : times_cont_mdiff_on I.tangent I'.tangent m
      (ir ∘ (bundle_mfderiv_within I I' (r ∘ f ∘ l.symm) s'l)) s'l_lift,
  { have A : times_cont_mdiff_on I'.tangent I'.tangent m ir ir.source :=
      times_cont_mdiff_on_atlas _ (chart_mem_atlas _ _) _,
    refine times_cont_mdiff_on.comp A diff_rfl_lift (λp hp, by simp [ir]) },
  have diff_Drirrfl_lift : times_cont_mdiff_on I.tangent I'.tangent m
    (Dr.symm ∘ (ir ∘ (bundle_mfderiv_within I I' (r ∘ f ∘ l.symm) s'l))) s'l_lift,
  { have A : times_cont_mdiff_on I'.tangent I'.tangent m Dr.symm Dr.target :=
      times_cont_mdiff_on_atlas_symm _ (chart_mem_atlas _ _) _,
    apply times_cont_mdiff_on.comp A diff_irrfl_lift (λp hp, _),
    simp [s'l_lift, tangent_bundle.proj] at hp,
    simp [ir, local_equiv.trans_target, @local_equiv.refl_coe (H' × E'), hp] },
  -- conclusion of this step: the composition of all the maps above is smooth
  have diff_DrirrflilDl : times_cont_mdiff_on I.tangent I'.tangent m
    (Dr.symm ∘ (ir ∘ (bundle_mfderiv_within I I' (r ∘ f ∘ l.symm) s'l)) ∘
      (il.symm ∘ Dl)) s'_lift,
  { have A : times_cont_mdiff_on I.tangent I.tangent m Dl Dl.source :=
      times_cont_mdiff_on_atlas _ (chart_mem_atlas _ _) _,
    have A' : times_cont_mdiff_on I.tangent I.tangent m Dl s'_lift,
    { apply A.mono (λp hp, _),
      simp [s'_lift, tangent_bundle.proj] at hp,
      simp [Dl, hp] },
    have B : times_cont_mdiff_on I.tangent I.tangent m il.symm il.target :=
      times_cont_mdiff_on_atlas_symm _ (chart_mem_atlas _ _) _,
    have C : times_cont_mdiff_on I.tangent I.tangent m (il.symm ∘ Dl) s'_lift :=
      times_cont_mdiff_on.comp B A' (λp hp, by simp [il]),
    apply times_cont_mdiff_on.comp diff_Drirrfl_lift C (λp hp, _),
    simp [s'_lift, tangent_bundle.proj] at hp,
    simp [il, s'l_lift, hp, @local_equiv.refl_symm (H × E), tangent_bundle.proj] },
  /- Third step: check that the composition of all the maps indeed coincides with the derivative we
  are looking for -/
  have eq_comp : ∀q ∈ s'_lift, bundle_mfderiv_within I I' f s q =
      (Dr.symm ∘ ir ∘ (bundle_mfderiv_within I I' (r ∘ f ∘ l.symm) s'l) ∘
      (il.symm ∘ Dl)) q,
  { assume q hq,
    simp [s'_lift, tangent_bundle.proj] at hq,
    have U'q : unique_mdiff_within_at I s' q.1,
      by { apply U', simp [hq, s'] },
    have U'lq : unique_mdiff_within_at I s'l (Dl q).1,
      by { apply U'l, simp [hq, s'l] },
    have A : bundle_mfderiv_within I I' ((r ∘ f) ∘ l.symm) s'l (Dl q) =
      bundle_mfderiv_within I I' (r ∘ f) s'
        (bundle_mfderiv_within I I l.symm s'l (Dl q)),
    { refine bundle_mfderiv_within_comp_at (Dl q) _ _ (λp hp, _) U'lq,
      { apply diff_rf.mdifferentiable_within_at one_le_n,
        simp [hq] },
      { apply diff_l.mdifferentiable_within_at one_le_n,
        simp [s'l, hq] },
      { simp at hp, simp [hp] } },
    have B : bundle_mfderiv_within I I l.symm s'l (Dl q) = q,
    { have : bundle_mfderiv_within I I l.symm s'l (Dl q) =
             bundle_mfderiv I I l.symm (Dl q),
      { refine bundle_mfderiv_within_eq_bundle_mfderiv U'lq _,
        refine mdifferentiable_at_atlas_symm _ (chart_mem_atlas _ _) _,
        simp [hq] },
      rw [this, bundle_mfderiv_chart_symm, local_homeomorph.left_inv];
      simp [hq] },
    have C : bundle_mfderiv_within I I' (r ∘ f) s' q
      = bundle_mfderiv_within I' I' r r.source (bundle_mfderiv_within I I' f s' q),
    { refine bundle_mfderiv_within_comp_at q _ _ (λr hr, _) U'q,
      { apply diff_r.mdifferentiable_within_at one_le_n,
        simp [hq] },
      { apply diff_f.mdifferentiable_within_at one_le_n,
        simp [hq] },
      { simp [s'] at hr, simp [hr] } },
    have D : Dr.symm (bundle_mfderiv_within I' I' r r.source (bundle_mfderiv_within I I' f s' q))
      = bundle_mfderiv_within I I' f s' q,
    { have A : bundle_mfderiv_within I' I' r r.source (bundle_mfderiv_within I I' f s' q) =
             bundle_mfderiv I' I' r (bundle_mfderiv_within I I' f s' q),
      { apply bundle_mfderiv_within_eq_bundle_mfderiv,
        { apply is_open.unique_mdiff_within_at _ r.open_source, simp [hq] },
        { refine mdifferentiable_at_atlas _ (chart_mem_atlas _ _) _,
          simp [hq] } },
      have : f p.1 = (bundle_mfderiv_within I I' f s p).1 := rfl,
      rw [A],
      dsimp [r, Dr],
      rw [this, bundle_mfderiv_chart, local_homeomorph.left_inv];
      simp [hq] },
    have M : bundle_mfderiv_within I I' f s' q = bundle_mfderiv_within I I' f s q,
    { apply bundle_mfderiv_within_subset _ U'q _,
      { assume r hr, simp [s'] at hr, simp [hr] },
      { apply hf.mdifferentiable_within_at one_le_n, simp [hq] } },
    simp [il, ir, @local_equiv.refl_coe (H' × E'),
          @local_equiv.refl_symm (H × E), A, B, C, D, M.symm] },
  exact diff_DrirrflilDl.congr eq_comp,
end

/-- If a function is `C^n`, then its bundled derivative is continuous. -/
theorem times_cont_mdiff_on.continuous_on_bundle_mfderiv_within
  (hf : times_cont_mdiff_on I I' n f s) (hmn : 1 ≤ n) (hs : unique_mdiff_on I s) :
  continuous_on (bundle_mfderiv_within I I' f s) ((tangent_bundle.proj I M) ⁻¹' s) :=
begin
  have : times_cont_mdiff_on I.tangent I'.tangent 0 (bundle_mfderiv_within I I' f s)
         ((tangent_bundle.proj I M) ⁻¹' s) :=
    hf.times_cont_mdiff_on_bundle_mfderiv_within hmn hs,
  exact this.continuous_on
end

end bundle_derivative
