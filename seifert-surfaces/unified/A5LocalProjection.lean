import A5PuncturedProjection
import A5PuncturedPlane
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
open Set Topology Filter Metric
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations

private theorem subtype_val_local_homeomorph_interior
    {X : Type*} [TopologicalSpace X] (K : Set X) :
    IsLocalHomeomorphOn (Subtype.val : K → X) (Subtype.val ⁻¹' interior K) := by
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mpr
  intro z hz
  let U : Set K := Subtype.val ⁻¹' interior K
  refine ⟨U, (isOpen_interior.preimage continuous_subtype_val).mem_nhds hz, ?_⟩
  have he : IsEmbedding (U.domRestrict (Subtype.val : K → X)) :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  refine ⟨he, ?_⟩
  have hr : range (U.domRestrict (Subtype.val : K → X)) = interior K := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact z.property
    · intro hy
      exact ⟨⟨⟨y, interior_subset hy⟩, hy⟩, rfl⟩
  rw [hr]
  exact isOpen_interior

private theorem punctured_neighborhoods_subtype
    {X : Type*} [TopologicalSpace X] (K : Set X) (x : X) (hx : x ∈ interior K)
    (hp : ∀ V : Set X, IsOpen V → x ∈ V →
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ IsPreconnected (W \ {x})) :
    ∀ V : Set K, IsOpen V → (⟨x, interior_subset hx⟩ : K) ∈ V →
      ∃ W : Set K, IsOpen W ∧ (⟨x, interior_subset hx⟩ : K) ∈ W ∧ W ⊆ V ∧
        IsPreconnected (W \ {(⟨x, interior_subset hx⟩ : K)}) := by
  intro V hV hxV
  obtain ⟨O, hO, rfl⟩ := IsInducing.subtypeVal.isOpen_iff.mp hV
  obtain ⟨W, hW, hxW, hWO, hpW⟩ := hp (O ∩ interior K)
    (hO.inter isOpen_interior) ⟨hxV, hx⟩
  refine ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hxW,
    fun z hz => (hWO hz).1, ?_⟩
  apply IsInducing.subtypeVal.isPreconnected_image.mp
  have he : (Subtype.val : K → X) ''
      ((Subtype.val ⁻¹' W) \ {(⟨x, interior_subset hx⟩ : K)}) = W \ {x} := by
    ext y
    constructor
    · rintro ⟨z, ⟨hzW, hzx⟩, rfl⟩
      exact ⟨hzW, fun he => hzx (Subtype.ext he)⟩
    · intro hy
      exact ⟨⟨y, interior_subset (hWO hy.1).2⟩, ⟨hy.1,
        fun he => hy.2 (congrArg Subtype.val he)⟩, rfl⟩
  rw [he]
  exact hpW

/-- A compact neighborhood can be chosen during the proof. A continuous
projection with a locally unique center fiber, local homeomorphisms off the
center, and an embedded real height is a local homeomorphism at the center.
This is the local form needed for actual surface coordinate neighborhoods. -/
theorem projection_local_homeomorph_across_point
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (f : X → Euc 2) (hf : Continuous f) (x : X)
    (V : Set X) (hV : IsOpen V) (hxV : x ∈ V)
    (hzero : ∀ z ∈ V, f z = f x → z = x)
    (hlocal : IsLocalHomeomorphOn f (V \ {x}))
    (hsourceacc : x ∈ closure ({x}ᶜ : Set X))
    (hpuncture : ∀ O : Set X, IsOpen O → x ∈ O →
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ IsPreconnected (W \ {x}))
    (height : X → ℝ) (hheight : Continuous height)
    (hseparate : InjOn (fun z => (f z, height z)) V) :
    IsLocalHomeomorphOn f {x} := by
  obtain ⟨K, hK, hxK, hKV⟩ := exists_compact_subset hV hxV
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let xK : K := ⟨x, interior_subset hxK⟩
  let fK : K → Euc 2 := f ∘ Subtype.val
  have hfK : Continuous fK := hf.comp continuous_subtype_val
  have hzeroK : ∀ z, fK z = fK xK → z = xK := by
    intro z hz
    exact Subtype.ext (hzero z (hKV z.property) hz)
  have hbad : IsCompact (f '' (K \ interior K)) :=
    (hK.diff isOpen_interior).image hf
  have hxgood : f x ∈ (f '' (K \ interior K))ᶜ := by
    rintro ⟨z, hz, he⟩
    exact hz.2 (hzero z (hKV hz.1) he ▸ hxK)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hbad.isClosed.isOpen_compl.mem_nhds hxgood)
  let U := ball (f x) r
  have hinterior (z : K) (hz : fK z ∈ U) : z.val ∈ interior K := by
    by_contra hn
    exact hrsub hz ⟨z, ⟨z.property, hn⟩, rfl⟩
  have hlocalK : IsLocalHomeomorphOn fK (fK ⁻¹' (U \ {fK xK})) := by
    apply hlocal.comp ((subtype_val_local_homeomorph_interior K).mono ?_) ?_
    · intro z hz
      exact hinterior z hz.1
    · intro z hz
      exact ⟨hKV z.property, fun he => hz.2 (congrArg f he)⟩
  have haccK : xK ∈ closure ({xK}ᶜ : Set K) := by
    apply mem_closure_iff_nhds.mpr
    intro O hO
    obtain ⟨O', hO'O, hO', hxO'⟩ := mem_nhds_iff.mp hO
    obtain ⟨A, hA, hAO⟩ := IsInducing.subtypeVal.isOpen_iff.mp hO'
    have hxA : x ∈ A := by rw [← hAO] at hxO'; exact hxO'
    obtain ⟨y, hy, hyx⟩ := mem_closure_iff_nhds.mp hsourceacc _
      ((hA.inter isOpen_interior).mem_nhds ⟨hxA, hxK⟩)
    refine ⟨⟨y, interior_subset hy.2⟩, hO'O ?_, ?_⟩
    · rw [← hAO]
      exact hy.1
    · intro he
      exact hyx (congrArg Subtype.val he)
  have hhomeo := projection_homeomorph_across_exceptional_point fK hfK xK U
    isOpen_ball (mem_ball_self hr) hzeroK hlocalK
    (punctured_planar_ball_preconnected (f x) r hr)
    (center_mem_closure_punctured_planar_ball (f x) r hr) haccK
    (punctured_neighborhoods_subtype K x hxK hpuncture)
    (height ∘ Subtype.val) (hheight.comp continuous_subtype_val)
    (fun a b hab => Subtype.ext (hseparate (hKV a.property) (hKV b.property) hab))
  let D := fK ⁻¹' U
  let g : D → X := fun z => z.val.val
  have hg : IsOpenEmbedding g := by
    refine ⟨IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal, ?_⟩
    have he : range g = interior K ∩ f ⁻¹' U := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨hinterior z.val z.property, z.property⟩
      · intro hy
        exact ⟨⟨⟨y, interior_subset hy.1⟩, hy.2⟩, rfl⟩
    rw [he]
    exact isOpen_interior.inter (isOpen_ball.preimage hf)
  have hfg : IsOpenEmbedding (f ∘ g) :=
    isOpen_ball.isOpenEmbedding_subtypeVal.comp hhomeo.isOpenEmbedding
  have hl : IsLocalHomeomorphOn f (g '' (univ : Set D)) :=
    hfg.isLocalHomeomorph.isLocalHomeomorphOn.of_comp_right
      hg.isLocalHomeomorph.isLocalHomeomorphOn
  apply hl.mono
  intro z hz
  subst z
  exact ⟨⟨xK, mem_ball_self hr⟩, mem_univ _, rfl⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
