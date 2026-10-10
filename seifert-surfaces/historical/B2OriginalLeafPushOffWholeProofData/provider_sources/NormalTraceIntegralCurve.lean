import IntrinsicClosedInterval
import TraceVelocity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] {f g : NeatEmbedding S M}

def normalStageCurve (F : SmoothNormalIsotopy S M f g) (x : S) : ℝ → M :=
  fun t => (F.stage (projIcc 0 1 (by norm_num) t)).toFun x

theorem normalStageCurve_contMDiffOn
    (F : SmoothNormalIsotopy S M f g) (x : S) :
    ContMDiffOn 𝓘(ℝ,ℝ) (𝓡∂ 3) ∞ (normalStageCurve F x) (Icc 0 1) := by
  have hc : ContMDiff (𝓡∂ 1) (𝓡∂ 3) ∞ (fun t : Time => (F.stage t).toFun x) :=
    F.smooth_family.comp (contMDiff_id.prodMk contMDiff_const)
  exact hc.comp_contMDiffOn contMDiffOn_projIcc

/-- The prescribed trace is an intrinsic integral curve, including at both
closed time endpoints. The canonical interval tangent vector pays the coefficient. -/
theorem normalStageCurve_hasMFDerivWithinAt
    (F : SmoothNormalIsotopy S M f g) (x : S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) (normalStageCurve F x) (Icc 0 1) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight
        (traceVelocity F (projIcc 0 1 (by norm_num) t,x))) := by
  have hd := (normalStageCurve_contMDiffOn F x).mdifferentiableOn (by simp) t ht
  have hone : mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 3) (normalStageCurve F x) (Icc 0 1) t 1 =
      traceVelocity F (projIcc 0 1 (by norm_num) t,x) := by
    have hh := mfderivWithin_comp_projIcc_one
      (I := 𝓡∂ 3) (f := fun u : Time => (F.stage u).toFun x) (w := (⟨t,ht⟩ : Time))
    rw [projIcc_of_mem (by norm_num) ht]
    exact hh
  apply hd.hasMFDerivWithinAt.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  let ar : ℝ := a
  change mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 3) (normalStageCurve F x) (Icc 0 1) t ar =
    ar • traceVelocity F (projIcc 0 1 (by norm_num) t,x)
  calc
    _ = mfderivWithin 𝓘(ℝ,ℝ) (𝓡∂ 3) (normalStageCurve F x) (Icc 0 1) t
        (ar • (1 : TangentSpace 𝓘(ℝ,ℝ) t)) := by
          congr 1
          change ar = ar * 1
          rw [mul_one]
    _ = _ := by rw [map_smul,hone]

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
