import A5RelativeHalfdiscInverse
import A5HalfspaceChartTangents

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- Native C1 half-space regularity gives the exact Euclidean half-disc
jet used by the relative inverse theorem. The derivative is that of the
original parametrization, expressed in its actual model coordinates. -/
theorem regular_C1_halfspace_local_halfdisc
    (f : EuclideanHalfSpace 2 → Euc 3) (V : Set (EuclideanHalfSpace 2))
    (hV : IsOpen V) (hzero : (0 : EuclideanHalfSpace 2) ∈ V)
    (hf : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 3) 1 f V)
    (hinj : Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 3) f 0)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      MapsTo (𝓡∂ 2).symm (closedHalfDisc ρ) V ∧
      ContDiffOn ℝ 1 (f ∘ (𝓡∂ 2).symm) (closedHalfDisc ρ) ∧
      Function.Injective (fderivWithin ℝ (f ∘ (𝓡∂ 2).symm) (closedHalfDisc ρ) 0) := by
  let U := (𝓡∂ 2).symm ⁻¹' V
  have hU : IsOpen U := hV.preimage (𝓡∂ 2).continuous_symm
  have hzU : (0 : E2) ∈ U := by
    change (𝓡∂ 2).symm ((𝓡∂ 2) (0 : EuclideanHalfSpace 2)) ∈ V
    rwa [ModelWithCorners.left_inv]
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  let ρ := r / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hsub : closedHalfDisc ρ ⊆ U := by
    intro z hz
    apply hrU
    have hzdist := Metric.mem_closedBall.mp hz.1
    rw [Metric.mem_ball]
    dsimp [ρ] at hzdist
    linarith
  have hrange : closedHalfDisc ρ ⊆ range (𝓡∂ 2) := by
    intro z hz
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact hz.2
  have hs : ContDiffOn ℝ 1 (f ∘ (𝓡∂ 2).symm) (closedHalfDisc ρ) :=
    (hf.comp ((𝓡∂ 2).contMDiffOn_symm.mono hrange) (fun z hz => hsub hz)).contDiffOn
  have hfd := ((hf.contMDiffAt (hV.mem_nhds hzero)).mdifferentiableAt (by norm_num)).hasMFDerivAt.2
  change HasFDerivWithinAt (f ∘ (𝓡∂ 2).symm)
    ((tangentSpaceCastModel 𝓘(ℝ,Euc 3) (f 0)).toContinuousLinearMap.comp
      ((mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 3) f 0).comp
        (tangentSpaceCastModel (𝓡∂ 2) (0 : EuclideanHalfSpace 2)).symm.toContinuousLinearMap))
    (range (𝓡∂ 2)) 0 at hfd
  refine ⟨ρ,hρ,fun z hz => hsub hz,hs,?_⟩
  rw [(hfd.mono hrange).fderivWithin
    (closedHalfDisc_uniqueDiffOn hρ 0 ⟨Metric.mem_closedBall_self hρ.le,by simp⟩)]
  exact (tangentSpaceCastModel 𝓘(ℝ,Euc 3) (f 0)).injective.comp
    (hinj.comp (tangentSpaceCastModel (𝓡∂ 2) (0 : EuclideanHalfSpace 2)).symm.injective)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
