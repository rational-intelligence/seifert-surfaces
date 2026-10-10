import B1ActualGermContact_v475
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionInterior
import DifferentialGeometry.Topology.Embedding.SliceChart
import EndpointGeometry
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- An actual neat surface has a smooth ambient sphere slice chart at every
interior source point. The complement is proved one-dimensional from the
immersion equivalence; no graph or tangent-plane premise is introduced. -/
theorem native_actual_interior_slice_chart_v475
    {S : CompactOrientedSurface.{u}} (f : NeatEmbedding S E.Carrier)
    (x : S) (hx : x ∉ S.boundary) :
    ∃ Φ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ),
      E.toSphere (f.toFun x) ∈ Φ.source ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source ∧
      ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target ∧
      Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) =
        Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
  classical
  let hf := f.smoothEmbedding.isImmersion.isImmersionAt x
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  let hg := hinc.isImmersion.isImmersionAt (f.toFun x)
  let F := hf.complement
  let G := hg.complement
  have hfc := hf.isImmersionAtOfComplement_complement
  have hgc := hg.isImmersionAtOfComplement_complement
  have hxi : (𝓡∂ 2).IsInteriorPoint x :=
    ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mpr hx
  letI : CompleteSpace F := Manifold.completeSpace_of_continuousLinearEquiv_prod hfc.equiv
  letI : CompleteSpace G := Manifold.completeSpace_of_continuousLinearEquiv_prod hgc.equiv
  have hc := Manifold.IsImmersionAtOfComplement.comp_of_isInteriorPoint hfc hgc (by simp) hxi
  let H := F × G
  letI : FiniteDimensional ℝ (E2 × H) :=
    FiniteDimensional.of_injective hc.equiv.toLinearEquiv.toLinearMap hc.equiv.injective
  letI : FiniteDimensional ℝ H :=
    FiniteDimensional.of_injective (LinearMap.inr ℝ E2 H) LinearMap.inr_injective
  have hdim : Module.finrank ℝ H = Module.finrank ℝ ℝ := by
    have hs := hc.equiv.toLinearEquiv.finrank_eq
    change Module.finrank ℝ (E2 × H) = Module.finrank ℝ E3 at hs
    simp only [Module.finrank_prod] at hs
    have h2 : Module.finrank ℝ E2 = 2 := by simp [E2]
    have h3 : Module.finrank ℝ E3 = 3 := by simp [E3]
    rw [h2,h3] at hs
    simp only [Module.finrank_self]
    omega
  let hr := hc.trans_F (ContinuousLinearEquiv.ofFinrankEq hdim)
  have hi : IsInducing (E.toSphere ∘ f.toFun) :=
    (hinc.isEmbedding.comp f.smoothEmbedding.isEmbedding).isInducing
  exact hr.exists_contMDiffOn_slice_chart hi

#print axioms native_actual_interior_slice_chart_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
