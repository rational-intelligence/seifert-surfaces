import A5C1HalfspaceHalfdisc
import A5RelativeImageTangent

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- A smooth regular image boundary clock has a nonzero tangential
derivative in any actual C1 regular half-disc image chart. Only continuity
of the source clock is used; its derivative is a conclusion. -/
theorem C1_halfdisc_boundary_clock_derivative
    (ρ : ℝ) (hρ : 0 < ρ) (f : E2 → E3)
    (hf : ContDiffOn ℝ 1 f (closedHalfDisc ρ))
    (hfi : Function.Injective (fderivWithin ℝ f (closedHalfDisc ρ) 0))
    (q : ℝ → E2) (hq0 : q 0 = 0) (hq : ContinuousAt q 0)
    (hqmap : ∀ᶠ t in 𝓝 0, q t ∈ closedHalfDisc ρ)
    (hqflat : ∀ᶠ t in 𝓝 0, q t 0 = 0)
    (γ : ℝ → E3) (v : E3) (hv : HasDerivAt γ v 0) (hvn : v ≠ 0)
    (heq : f ∘ q =ᶠ[𝓝 0] γ) :
    ∃ a : ℝ, a ≠ 0 ∧ HasDerivAt q (a • coordinateVector 2 1) 0 ∧
      fderivWithin ℝ f (closedHalfDisc ρ) 0 (a • coordinateVector 2 1) = v := by
  have hz : (0 : E2) ∈ closedHalfDisc ρ := ⟨Metric.mem_closedBall_self hρ.le,by simp⟩
  obtain ⟨g,hg,hge⟩ := C1_closed_halfdisc_local_extension ρ hρ f hf
  have hdg : fderiv ℝ g 0 = fderivWithin ℝ f (closedHalfDisc ρ) 0 := by
    rw [← fderivWithin_eq_fderiv (closedHalfDisc_uniqueDiffOn hρ 0 hz)
      (hg.differentiableAt (by norm_num))]
    exact hge.fderivWithin_eq_of_mem hz
  have hgi : Function.Injective (fderiv ℝ g 0) := by rwa [hdg]
  obtain ⟨L,hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hgi
  have hqt : Tendsto q (𝓝 0) (𝓝[closedHalfDisc ρ] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [hq0] using hq.tendsto,hqmap⟩
  have hgq : g ∘ q =ᶠ[𝓝 0] γ := (hge.comp_tendsto hqt).trans heq
  have hgqd : HasFDerivAt g (fderiv ℝ g 0) (q 0) := by
    rw [hq0]
    exact (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hqd : HasDerivAt q (L v) 0 := by
    have hh := HasFDerivAt.of_comp_of_leftInverse hq hgqd hv.hasFDerivAt hgq hL
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] using hh.hasDerivAt
  have hgv : fderiv ℝ g 0 (L v) = v := by
    have hh := (hgqd.comp_hasDerivAt 0 hqd).congr_of_eventuallyEq hgq.symm
    exact hh.unique hv
  have hflat : (L v) 0 = 0 := by
    have hh := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.comp_hasDerivAt 0 hqd
    have hconst : HasDerivAt (fun t : ℝ => q t 0) 0 0 :=
      (hasDerivAt_const 0 (0 : ℝ)).congr_of_eventuallyEq hqflat
    exact hh.unique hconst
  have hw : (L v) 1 • coordinateVector 2 1 = L v := by
    ext i
    fin_cases i <;> simp [coordinateVector,EuclideanSpace.single,hflat]
  refine ⟨(L v) 1,?_,hw.symm ▸ hqd,?_⟩
  · intro ha
    apply hvn
    rw [← hgv,← hw,ha,zero_smul,map_zero]
  · rw [hw,← hdg]
    exact hgv

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
