import OriginalA25SourceDefinitionsV464
import A5NativeSeamSector
import A5NativeLocalCover
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-- An embedded native boundary interval lying on the same embedded regular
seam contains a neighbourhood in that original seam clock. This proves local
image surjectivity before asking for any differentiability of a boundary lift. -/
theorem embedded_boundary_contains_seam_interval
    {X : Type*} [TopologicalSpace X] (V W : Set ℝ) (hV : IsOpen V)
    (boundary : V → X) (hboundary : IsEmbedding boundary)
    (edge : W → X) (hedge : IsEmbedding edge)
    (hmaps : MapsTo boundary univ (range edge)) :
    ∃ U : Set ℝ, IsOpen U ∧ U ⊆ W ∧
      (∀ s : W, edge s ∈ range boundary ↔ (s : ℝ) ∈ U) := by
  let e := hedge.toHomeomorph
  let f : V → range edge := fun t => ⟨boundary t, hmaps (mem_univ t)⟩
  have hf : Continuous f := hboundary.continuous.subtype_mk _
  let clock : V → ℝ := fun t => (e.symm (f t) : ℝ)
  have hc : Continuous clock := continuous_subtype_val.comp (e.symm.continuous.comp hf)
  have hinj : Function.Injective clock := by
    intro t u htu
    apply hboundary.injective
    have hs : e.symm (f t) = e.symm (f u) := Subtype.ext htu
    have he : f t = f u := e.symm.injective hs
    exact congrArg Subtype.val he
  have hopen : IsOpen (range clock) :=
    DifferentialGeometry.Topology.isOpen_range_of_isOpen_of_continuous_injective_real
      𝓘(ℝ) hV clock hc hinj
  refine ⟨range clock, hopen, ?_, ?_⟩
  · rintro s ⟨t, rfl⟩
    exact (e.symm (f t)).property
  · intro s
    constructor
    · rintro ⟨t, hts⟩
      refine ⟨t, ?_⟩
      have he : f t = e s := Subtype.ext hts
      change (e.symm (f t) : ℝ) = (s : ℝ)
      rw [he, e.symm_apply_apply]
    · rintro ⟨t, hts⟩
      refine ⟨t, ?_⟩
      have hs : e.symm (f t) = s := Subtype.ext hts
      have he := congrArg e hs
      rw [e.apply_symm_apply] at he
      exact congrArg Subtype.val he

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
