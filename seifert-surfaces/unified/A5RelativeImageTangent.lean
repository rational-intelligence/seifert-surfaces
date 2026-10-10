import A5NativeSphereCoordinateRank
import A5NativeImageChartPlane
import A5SeamTangents

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates

/-- Two regular parametrizations of one local image have the same tangent
range even when the first is only differentiable within a closed sector.
A continuous coordinate lift is sufficient and its derivative is derived. -/
theorem relative_tangent_range_of_continuous_image_lift
    (g Φ : E2 → E3) (q : E2 → E2) (A : Set E2) (z : E2)
    (hz : z ∈ A) (hA : UniqueDiffWithinAt ℝ A z)
    (D DΦ : E2 →L[ℝ] E3)
    (hg : HasFDerivWithinAt g D A z) (hD : Function.Injective D)
    (hΦ : HasFDerivAt Φ DΦ (q z)) (hDΦ : Function.Injective DΦ)
    (hq : ContinuousWithinAt q A z)
    (heq : (Φ ∘ q) =ᶠ[𝓝[A] z] g) (hpoint : Φ (q z) = g z) :
    D.toLinearMap.range = DΦ.toLinearMap.range := by
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hDΦ
  have hqd : HasFDerivWithinAt q (L.comp D) A z := by
    have ht : Tendsto q (𝓝[A] z) (𝓝[univ] (q z)) := by
      rw [nhdsWithin_univ]
      exact hq
    exact HasFDerivWithinAt.of_comp_of_leftInverse ht hΦ.hasFDerivWithinAt hg heq hL hz
  have hcomp : HasFDerivWithinAt g (DΦ.comp (L.comp D)) A z :=
    (hΦ.comp_hasFDerivWithinAt z hqd).congr_of_eventuallyEq heq.symm hpoint.symm
  have hd : DΦ.comp (L.comp D) = D := hA.eq hcomp hg
  have hsub : D.toLinearMap.range ≤ DΦ.toLinearMap.range := by
    rintro v ⟨w, rfl⟩
    exact ⟨(L.comp D) w, congrArg (fun H : E2 →L[ℝ] E3 => H w) hd⟩
  exact Submodule.eq_of_le_of_finrank_eq hsub (by
    rw [LinearMap.finrank_range_of_inj hD, LinearMap.finrank_range_of_inj hDΦ])

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
