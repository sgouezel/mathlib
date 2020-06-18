/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import geometry.manifold.charted_space


noncomputable theory
open_locale classical manifold topological_space
universes u

variables {H : Type u} {M : Type*} [topological_space H] [topological_space M] [charted_space H M]
{H' : Type*} {M' : Type*} [topological_space H'] [topological_space M'] [charted_space H' M']

namespace structure_groupoid

variables (G : structure_groupoid H)

structure invariant_prop_set_pt (G : structure_groupoid H) (P : set H → H → Prop) : Prop :=
(is_local   : ∀ {s x u}, is_open u → x ∈ u → (P s x ↔ P (s ∩ u) x))
(invariance : ∀ s x (e : local_homeomorph H H), e ∈ G → P s x →
                P (e.target ∩ e.symm ⁻¹' s) (e x))

structure invariant_prop_set (G : structure_groupoid H) (P : set H → Prop) : Prop :=
(is_local   : ∀ s, (∀ x ∈ s, ∃ u, is_open u ∧ x ∈ u ∧ P (s ∩ u)) → P s)
(mono       : ∀ s u, P s → is_open u → P (s ∩ u))
(invariance : ∀ s (e : local_homeomorph H H), e ∈ G → P s →
                P (e.target ∩ e.symm ⁻¹' s))

lemma invariant_prop_set_pt.invariant_prop_set {P : set H → H → Prop}
  (h : G.invariant_prop_set_pt P) : G.invariant_prop_set (λ s, (∀ x ∈ s, P s x)) :=
begin
  split,
  { assume s hs x hx,
    rcases hs x hx with ⟨u, ⟨u_open, xu, hu⟩⟩,
    rw h.is_local u_open xu,
    exact hu x ⟨hx, xu⟩ },
  { assume s u hs hu x hx,
    exact (h.is_local hu hx.2).1 (hs x hx.1) },
  { assume s e eG hP x hx,
    set y := e.symm x with hy,
    have : P (e.target ∩ e.symm ⁻¹' s) (e y) :=
      h.invariance s y e eG (hP y hx.2),
    rwa [hy, e.right_inv hx.1] at this }
end

structure invariant_prop_fun_set_pt (G : structure_groupoid H) (G' : structure_groupoid H')
  (P : (H → H') → (set H) → H → Prop) : Prop :=
(is_local : ∀ {s x u} {f : H → H'}, is_open u → x ∈ u → (P f s x ↔ P f (s ∩ u) x))
(right_invariance : ∀ s x f (e : local_homeomorph H H), e ∈ G → P f s x →
                      P (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' s) (e x))
(congr : ∀ s x (f g : H → H'), (∀ y ∈ s, f y = g y) → P f s x → P g s x)
(left_invariance : ∀ s x f (e' : local_homeomorph H' H'), e' ∈ G' → s ⊆ f ⁻¹' (e'.source) →
                     P f s x → P (e' ∘ f) s x)

end structure_groupoid


/-- If one can define a property of pointed sets in the model space, then one define a
corresponding property in the manifold, using the preferred chart at the point. -/
def charted_space.lift_prop_set_pt (P : set H → H → Prop) (s : set M) (x : M) : Prop :=
P ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' s) (chart_at H x x)

/-- If one can define a property of sets in the model space, then one define a
corresponding property in the manifold, by requiring that it holds for all preferred charts. -/
def charted_space.lift_prop_set (P : set H → Prop) (s : set M) : Prop :=
∀ x, P ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' s)

/-- If one can define a property of germs of functions and sets in the model space, then one define
a corresponding property in the manifold, by requiring that it holds for all preferred charts. -/
def charted_space.lift_fun_prop_set (P : (H → H') → set H → H → Prop)
  (f : M → M') (s : set M) (x : M) : Prop :=
continuous_within_at f s x ∧
P ((chart_at H' (f x)) ∘ f ∘ (chart_at H x).symm)
  ((chart_at H x).target ∩ (chart_at H x).symm ⁻¹' (s ∩ f ⁻¹' (chart_at H' (f x)).source))
  (chart_at H x x)

section invariant_properties

variables {G : structure_groupoid H} [has_groupoid M G]
{G' : structure_groupoid H'} [has_groupoid M' G']

/- If a property of a pointed set is invariant under the structure groupoid, then expressing it in
the charted space does not depend on the element of the atlas one uses provided it contains the
point in its source. -/
lemma structure_groupoid.invariant_prop_set_pt.indep_chart
  {P : set H → H → Prop} (hG : G.invariant_prop_set_pt P) {e e' : local_homeomorph M H} (x : M)
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source) (he' : e' ∈ G.maximal_atlas M) (xe' : x ∈ e'.source)
  {s : set M} (h : P (e.target ∩ e.symm ⁻¹' s) (e x)) :
  P (e'.target ∩ e'.symm ⁻¹' s) (e' x) :=
begin
  set c := e.symm ≫ₕ e' with hc,
  have cG : c ∈ G := compatible_of_mem_maximal_atlas he he',
  suffices A : P ((e'.target ∩ e'.symm ⁻¹' s) ∩ c.target) (e' x),
  { apply (hG.is_local c.open_target _).2 A,
    simp [c, local_equiv.trans_target, xe, xe'] },
  set t := e.target ∩ e.symm ⁻¹' s with ht,
  have B : (e'.target ∩ e'.symm ⁻¹' s) ∩ c.target =
           c.target ∩ c.symm ⁻¹' t,
  { ext y,
    simp [c, local_equiv.trans_source, local_equiv.trans_target],
    split,
    { assume hy,
      simp [hy] },
    { assume hy,
      simp [hy],
      simpa [hy] using hy } },
  have : P (c.target ∩ c.symm ⁻¹' t) (c (e x)) :=
    hG.invariance _ _ _ cG h,
  convert this using 1,
  { exact B },
  { simp [c, xe, xe'] }
end

/- If a property of a pointed set is invariant under the structure groupoid, then it is equivalent
to express it in the charted space using the preferred chart at the point, or any maximal atlas
member containing the point in its source. -/
lemma structure_groupoid.invariant_prop_set_pt.lift_prop_set_pt_iff
  {P : set H → H → Prop} (hG : G.invariant_prop_set_pt P) {e : local_homeomorph M H} (x : M)
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source) (s : set M) :
  charted_space.lift_prop_set_pt P s x ↔ P (e.target ∩ e.symm ⁻¹' s) (e x) :=
⟨hG.indep_chart x (G.chart_mem_maximal_atlas x) (mem_chart_source H x) he xe,
hG.indep_chart x he xe (G.chart_mem_maximal_atlas x) (mem_chart_source H x)⟩


/- If a property of a pointed set is invariant under the structure groupoid, then expressing it in
the charted space does not depend on the element of the atlas one uses provided it contains the
point in its source. -/
lemma structure_groupoid.invariant_prop_fun_set_pt.indep_chart
  {P : (H → H') → set H → H → Prop} (hG : G.invariant_prop_fun_set_pt G' P)
  {e e' : local_homeomorph M H} {f f' : local_homeomorph M' H'} (g : M → M') (x : M)
  (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source)
  (he' : e' ∈ G.maximal_atlas M) (xe' : x ∈ e'.source)
  (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source)
  (hf' : f' ∈ G'.maximal_atlas M') (xf' : g x ∈ f'.source)
  {s : set M} (hgs : continuous_within_at g s x)
  (h : P (f ∘ g ∘ e.symm) (e.target ∩ e.symm ⁻¹' (s ∩ g⁻¹' f.source)) (e x)) :
  P (f' ∘ g ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' (s ∩ g⁻¹' f'.source)) (e' x) :=
begin
  obtain ⟨o, o_open, xo, oe, oe', of, of'⟩ :
    ∃ (o : set M), is_open o ∧ x ∈ o ∧ o ⊆ e.source ∧ o ⊆ e'.source ∧
      o ∩ s ⊆ g ⁻¹' f.source ∧ o ∩ s ⊆  g⁻¹' f'.to_local_equiv.source,
  { have : f.source ∩ f'.source ∈ 𝓝 (g x) :=
      mem_nhds_sets (is_open_inter f.open_source f'.open_source) ⟨xf, xf'⟩,
    rcases mem_nhds_within.1 (hgs.preimage_mem_nhds_within this) with ⟨u, u_open, xu, hu⟩,
    refine ⟨u ∩ e.source ∩ e'.source, _, ⟨⟨xu, xe⟩, xe'⟩, _, _, _, _⟩,
    { exact is_open_inter (is_open_inter u_open e.open_source) e'.open_source },
    { assume x hx, exact hx.1.2 },
    { assume x hx, exact hx.2 },
    { assume x hx, exact (hu ⟨hx.1.1.1, hx.2⟩).1 },
    { assume x hx, exact (hu ⟨hx.1.1.1, hx.2⟩).2 } },
  have A : P (f ∘ g ∘ e.symm)
             (e.target ∩ e.symm ⁻¹' (s ∩ g⁻¹' f.source) ∩ (e.target ∩ e.symm ⁻¹' o)) (e x),
  { apply (hG.is_local _ _).1 h,
    { library_search

    },

    { simp [xe, xo] },

  }
end


end invariant_properties
