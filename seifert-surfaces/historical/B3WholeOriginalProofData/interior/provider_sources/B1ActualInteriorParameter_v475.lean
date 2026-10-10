import B1ActualInteriorLift_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Recover an actual source parameter through the neat immersion, with no
assumed smoothness of the inverse embedding. -/
theorem native_actual_interior_source_parameter_v475
    {S : CompactOrientedSurface.{u}} (f : NeatEmbedding S E.Carrier) (q₀ : S)
    (O : Set E2) (hO : IsOpen O) (Γ : E2 → E.Carrier)
    (hΓ : ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 3) ∞ Γ O)
    (hmaps : ∀ x ∈ O, Γ x ∈ f.image)
    (hinterior : ∀ x ∈ O, Γ x ∈ (𝓡∂ 3).interior E.Carrier) :
    ∃ q : E2 → S,
      (∀ x ∈ O, f.toFun (q x)=Γ x) ∧
      (∀ x ∈ O, q x ∉ S.boundary) ∧
      ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ q O := by
  classical
  let q : E2 → S := fun x => if hx : x ∈ O then (hmaps x hx).choose else q₀
  have heq (x : E2) (hx : x ∈ O) : f.toFun (q x)=Γ x := by
    simp only [q,dif_pos hx]
    exact (hmaps x hx).choose_spec
  have hqcont : ContinuousOn q O := by
    apply f.smoothEmbedding.isEmbedding.isInducing.continuousOn_iff.mpr
    exact hΓ.continuousOn.congr heq
  have hqnb (x : E2) (hx : x ∈ O) : q x ∉ S.boundary := by
    have hn (a : E.Carrier) (ha : a ∈ (𝓡∂ 3).interior E.Carrier) :
        a ∉ (𝓡∂ 3).boundary E.Carrier := by
      rw [← (𝓡∂ 3).compl_boundary] at ha
      exact ha
    intro hbd
    have hh : f.toFun (q x) ∈ (𝓡∂ 3).boundary E.Carrier := by
      rwa [← f.boundary_preimage] at hbd
    rw [heq x hx] at hh
    exact hn _ (hinterior x hx) hh
  refine ⟨q,heq,hqnb,?_⟩
  intro x hx
  have hcomp : ContMDiffAt 𝓘(ℝ,E2) (𝓡∂ 3) ∞ (f.toFun ∘ q) x := by
    apply (hΓ.contMDiffAt (hO.mem_nhds hx)).congr_of_eventuallyEq
    exact Filter.eventuallyEq_of_mem (hO.mem_nhds hx) (fun y hy => heq y hy)
  exact ((ContMDiffAt.iff_comp_isImmersionAt (I := 𝓘(ℝ,E2))
    (f.smoothEmbedding.isImmersion.isImmersionAt (q x))).mpr
      ⟨(hqcont x hx).continuousAt (hO.mem_nhds hx),hcomp⟩).contMDiffWithinAt

#print axioms native_actual_interior_source_parameter_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
