import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib.Topology.Covering.Quotient

namespace CurveComplex

open Topology

private abbrev UnitDisc :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1

private def DiscBoundary : Set UnitDisc :=
  {x | (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1}

/-- If an embedded disc lies inside its image under a homeomorphism, then the
homeomorphism has a fixed point. The fixed-point property is isolated for
instantiation from Brouwer's disc theorem. -/
theorem fixedPoint_of_disc_subset_homeomorph_image
    {E : Type*} [TopologicalSpace E]
    (d : C(UnitDisc, E)) (hd : IsEmbedding d)
    (hBrouwer : ∀ u : C(UnitDisc, UnitDisc), ∃ x, u x = x)
    (t : E ≃ₜ E)
    (hinc : Set.range d ⊆ t '' Set.range d) :
    ∃ y : E, t y = y := by
  let e : UnitDisc ≃ₜ Set.range d := hd.toHomeomorph
  have hmem : ∀ x : UnitDisc, t.symm (d x) ∈ Set.range d := by
    intro x
    obtain ⟨z, hz, heq⟩ := hinc ⟨x, rfl⟩
    simpa [← heq] using hz
  let u : C(UnitDisc, UnitDisc) :=
    ⟨fun x => e.symm ⟨t.symm (d x), hmem x⟩,
      e.symm.continuous.comp
        ((t.symm.continuous.comp d.continuous).subtype_mk hmem)⟩
  obtain ⟨x, hx⟩ := hBrouwer u
  have hfixed : t.symm (d x) = d x := by
    have he := congrArg (fun z : UnitDisc => e z) hx
    have hv := congrArg Subtype.val he
    simpa [u, e] using hv
  refine ⟨d x, ?_⟩
  exact (t.symm_apply_eq.mp hfixed).symm

/-- Turn a continuous group action into the homeomorphism associated with one
group element. -/
private def actionHomeomorph
    {G E : Type*} [Group G] [TopologicalSpace E] [MulAction G E]
    (hcont : ∀ g : G, Continuous (g • · : E → E)) (g : G) : E ≃ₜ E where
  toFun := fun x => g • x
  invFun := fun x => g⁻¹ • x
  left_inv := fun x => by simp
  right_inv := fun x => by simp
  continuous_toFun := hcont g
  continuous_invFun := hcont g⁻¹

/-- A freely acting deck transformation cannot carry an embedded disc into
itself or contain it. The contradiction uses Brouwer, not properness of the
group action. -/
theorem deck_translate_disc_ne_nested
    {G E S : Type*} [Group G] [TopologicalSpace E] [MulAction G E]
    [TopologicalSpace S]
    (p : E → S) (hp : IsQuotientCoveringMap p G)
    (d : C(UnitDisc, E)) (hd : IsEmbedding d)
    (hBrouwer : ∀ u : C(UnitDisc, UnitDisc), ∃ x, u x = x)
    (g : G) (hg : g ≠ 1) :
    ¬ Set.range d ⊆ (g • ·) '' Set.range d ∧
    ¬ (g • ·) '' Set.range d ⊆ Set.range d := by
  let t : E ≃ₜ E := actionHomeomorph (E := E) hp.continuous_const_smul g
  have hfree : ∀ x : E, t x ≠ x := by
    intro x hfix
    change g • x = x at hfix
    exact hg ((hp.isCancelSMul.right_cancel g 1 x) (by simpa using hfix))
  constructor
  · intro hinc
    obtain ⟨y, hy⟩ := fixedPoint_of_disc_subset_homeomorph_image d hd hBrouwer t hinc
    exact hfree y hy
  · intro hinc
    have hinc' : Set.range d ⊆ t.symm '' Set.range d := by
      intro y hy
      have hgy : g • y ∈ Set.range d :=
        hinc ⟨y, hy, rfl⟩
      refine ⟨g • y, hgy, ?_⟩
      change g⁻¹ • (g • y) = y
      simp
    obtain ⟨y, hy⟩ :=
      fixedPoint_of_disc_subset_homeomorph_image d hd hBrouwer t.symm hinc'
    exact hfree y ((t.symm_apply_eq.mp hy).symm)

/-- Jordan separation reduces two disjoint-boundary discs to disjointness or
nesting. Brouwer excludes both nesting alternatives for a free deck action, so
the quotient projection is injective on the chosen embedded disc. -/
theorem projection_injective_on_disc_of_jordan_trichotomy
    {G E S : Type*} [Group G] [TopologicalSpace E] [MulAction G E]
    [TopologicalSpace S]
    (p : E → S) (hp : IsQuotientCoveringMap p G)
    (d : C(UnitDisc, E)) (hd : IsEmbedding d)
    (hBrouwer : ∀ u : C(UnitDisc, UnitDisc), ∃ x, u x = x)
    (hJordan : ∀ g : G, g ≠ 1 →
      Disjoint (Set.range d) ((g • ·) '' Set.range d) ∨
      Set.range d ⊆ (g • ·) '' Set.range d ∨
      (g • ·) '' Set.range d ⊆ Set.range d) :
    Set.InjOn p (Set.range d) := by
  have hdisj (g : G) (hg : g ≠ 1) :
      Disjoint (Set.range d) ((g • ·) '' Set.range d) := by
    obtain h | h | h := hJordan g hg
    · exact h
    · exact False.elim ((deck_translate_disc_ne_nested p hp d hd hBrouwer g hg).1 h)
    · exact False.elim ((deck_translate_disc_ne_nested p hp d hd hBrouwer g hg).2 h)
  intro x hx y hy hxy
  obtain ⟨g, hgy⟩ := hp.apply_eq_iff_mem_orbit.mp hxy
  by_cases hg : g = 1
  · simpa [hg] using hgy.symm
  · have hx' : x ∈ (g • ·) '' Set.range d := ⟨y, hy, hgy⟩
    exact False.elim ((Set.disjoint_left.mp (hdisj g hg)) hx hx')

/-- Distinct deck translates of a lifted embedded circle are disjoint.
This boundary fact follows from embeddedness downstairs and freeness upstairs;
it requires no Jordan theorem. -/
theorem disjoint_lifted_circle_deck_translate
    {G E S : Type*} [Group G] [TopologicalSpace E] [MulAction G E]
    [TopologicalSpace S]
    (p : E → S) (hp : IsQuotientCoveringMap p G)
    (r : C(Circle, E))
    (hr : IsEmbedding (p ∘ (r : Circle → E)))
    (g : G) (hg : g ≠ 1) :
    Disjoint (Set.range r) ((g • ·) '' Set.range r) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨y, ⟨b, rfl⟩, hgy⟩ := hx'
  have hpab : p (r a) = p (r b) := by
    rw [← hgy]
    exact hp.map_smul g
  have hab : a = b := hr.injective hpab
  subst b
  have hfix : g • r a = r a := hgy
  exact hg ((hp.isCancelSMul.right_cancel g 1 (r a)) (by simpa using hfix))

/-- An embedded lifted Jordan disc projects to an embedded disc when Jordan
separation gives the standard disjoint-or-nested alternatives for translated
discs. Boundary disjointness and exclusion of nesting are proved above. -/
theorem boundsDisc_of_quotient_cover_jordan_disc
    {G E S : Type*} [Group G] [TopologicalSpace E] [MulAction G E]
    [TopologicalSpace S] [T2Space S]
    (p : E → S) (hp : IsQuotientCoveringMap p G)
    (c : Curve S) (r : C(Circle, E))
    (hpr : p ∘ (r : Circle → E) = c.map)
    (d : C(UnitDisc, E)) (hd : IsEmbedding d)
    (hbd : d '' DiscBoundary = Set.range r)
    (hBrouwer : ∀ u : C(UnitDisc, UnitDisc), ∃ x, u x = x)
    (hJordan : ∀ g : G, g ≠ 1 →
      Disjoint (d '' DiscBoundary) ((g • ·) '' (d '' DiscBoundary)) →
      Disjoint (Set.range d) ((g • ·) '' Set.range d) ∨
      Set.range d ⊆ (g • ·) '' Set.range d ∨
      (g • ·) '' Set.range d ⊆ Set.range d) :
    BoundsDisc c := by
  have hr : IsEmbedding (p ∘ (r : Circle → E)) := by
    rw [hpr]
    exact c.embedded
  have htri : ∀ g : G, g ≠ 1 →
      Disjoint (Set.range d) ((g • ·) '' Set.range d) ∨
      Set.range d ⊆ (g • ·) '' Set.range d ∨
      (g • ·) '' Set.range d ⊆ Set.range d := by
    intro g hg
    apply hJordan g hg
    rw [hbd]
    exact disjoint_lifted_circle_deck_translate p hp r hr g hg
  have hinj : Set.InjOn p (Set.range d) :=
    projection_injective_on_disc_of_jordan_trichotomy p hp d hd hBrouwer htri
  have hcont : Continuous p := hp.isCoveringMap.continuous
  let f : C(UnitDisc, S) := ⟨fun x => p (d x), hcont.comp d.continuous⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact hd.injective (hinj ⟨x, rfl⟩ ⟨y, rfl⟩ hxy)
  refine ⟨f, f.continuous.isClosedEmbedding hf_inj |>.isEmbedding, ?_⟩
  change (p ∘ (d : UnitDisc → E)) '' DiscBoundary = c.image
  rw [Set.image_comp]
  rw [hbd, ← Set.range_comp, hpr]
  rfl

end CurveComplex
