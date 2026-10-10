import B1ActualInteriorLift_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The smooth actual chart lift has injective differential. -/
theorem native_actual_interior_lift_differential_injective_v475
    (c : SmoothAmbientChart ThreeSphere) (χ : E3 → E.Carrier)
    (hχ : ContMDiffOn 𝓘(ℝ,E3) (𝓡∂ 3) ∞ χ c.chart.target)
    (heq : ∀ y ∈ c.chart.target, E.toSphere (χ y)=c.chart.symm y)
    (y : E3) (hy : y ∈ c.chart.target) :
    Function.Injective (mfderiv 𝓘(ℝ,E3) (𝓡∂ 3) χ y) := by
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hχd := (hχ.contMDiffAt (c.chart.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  have hincd := (hinc.contMDiff.contMDiffAt (x := χ y)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp y hincd hχd
  have hev : E.toSphere ∘ χ =ᶠ[𝓝 y] c.chart.symm :=
    Filter.eventuallyEq_of_mem (c.chart.open_target.mem_nhds hy) (fun z hz => heq z hz)
  have hm := hev.mfderiv_eq (I := 𝓘(ℝ,E3)) (I' := 𝓡 3)
  have hi : Function.Injective (mfderiv 𝓘(ℝ,E3) (𝓡 3) c.chart.symm y) := by
    have hh : c.chart.MDifferentiable (𝓡 3) 𝓘(ℝ,E3) :=
      ⟨c.smooth.mdifferentiableOn (by simp),c.inverse_smooth.mdifferentiableOn (by simp)⟩
    exact hh.symm.mfderiv_injective hy
  intro a b hab
  have hh := congrArg (mfderiv (𝓡∂ 3) (𝓡 3) E.toSphere (χ y)) hab
  have hc : mfderiv 𝓘(ℝ,E3) (𝓡 3) (E.toSphere ∘ χ) y a =
      mfderiv 𝓘(ℝ,E3) (𝓡 3) (E.toSphere ∘ χ) y b := by
    rw [hd]
    exact hh
  rw [hm] at hc
  have hpt : (E.toSphere ∘ χ) y = c.chart.symm y := by simp [heq y hy]
  rw [hpt] at hc
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe] at hc
  apply hi
  exact (tangentSpaceCast (𝓡 3) (c.chart.symm y) (c.chart.symm y)).injective hc

#print axioms native_actual_interior_lift_differential_injective_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
