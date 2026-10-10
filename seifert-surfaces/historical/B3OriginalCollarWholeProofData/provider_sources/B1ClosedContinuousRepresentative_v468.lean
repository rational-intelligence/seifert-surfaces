import B1FlatContinuousRepresentative_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
local instance (R : ℝ) : DecidablePred (· ∈ halfDisc R) := Classical.decPred _

/-- The two actual barriers provide a continuous representative on the entire
closed half-disc, including its two corner points. -/
theorem halfdisc_closed_continuous_representative_v468
    (R S M N : ℝ) (hR : 0 < R) (hM : 0 ≤ M) (hN : 0 ≤ N) (hS : 0 ≤ S)
    (f : E2 → ℝ) (hf : ContinuousOn f (halfDisc R))
    (hflatBound : ∀ x ∈ halfDisc R, |f x-1| ≤ M*(2*S*x 1-(x 1)^2))
    (hcircleBound : ∀ x ∈ halfDisc R, |f x-1| ≤ N*(R^2-‖x‖^2)) :
    let h := (halfDisc R).piecewise f (fun _ => 1)
    ContinuousOn h (closedHalfDisc R) ∧
    (∀ x ∈ frontier (halfDisc R), h x = 1) ∧
    (∀ x ∈ halfDisc R, h x = f x) := by
  classical
  let U := halfDisc R
  let h := U.piecewise f (fun _ => 1)
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  obtain ⟨hcap,hflat,heq⟩ := halfdisc_flat_continuous_representative_v468 R S M hR hM hS f hf hflatBound
  have hout (x : E2) (hx : x ∉ U) : h x = 1 := by simp only [h,Set.piecewise,ite_eq_right hx]
  refine ⟨?_,?_,heq⟩
  · intro x hx
    have hn : ‖x‖ ≤ R := by simpa only [closedDisc,Metric.mem_closedBall,dist_zero_right] using hx.1
    by_cases hnr : ‖x‖ < R
    · have hxcap : x ∈ Metric.ball (0 : E2) R ∩ {x : E2 | 0 ≤ x 1} :=
        ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hnr,hx.2⟩
      have hnear : Metric.ball (0 : E2) R ∈ 𝓝[closedHalfDisc R] x :=
        mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hxcap.1)
      apply (hcap x hxcap).mono_of_mem_nhdsWithin
      filter_upwards [self_mem_nhdsWithin,hnear] with y hy hyball
      exact ⟨hyball,hy.2⟩
    · have hnrEq : ‖x‖ = R := le_antisymm hn (le_of_not_gt hnr)
      have hxout : x ∉ U := by
        intro hh
        have ht : ‖x‖ < R := by
          simpa only [disc,Metric.mem_ball,dist_zero_right] using hh.1
        linarith
      have hxone : h x = 1 := hout x hxout
      have hg : Continuous (fun y : E2 => N*|R^2-‖y‖^2|) := by fun_prop
      have hgx : N*|R^2-‖x‖^2| = 0 := by rw [hnrEq]; simp
      have hglobal (y : E2) : dist (h y) (h x) ≤ N*|R^2-‖y‖^2| := by
        rw [hxone,Real.dist_eq]
        by_cases hy : y ∈ U
        · rw [show h y = f y from heq y hy]
          exact (hcircleBound y hy).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hN)
        · rw [hout y hy,sub_self,abs_zero]
          positivity
      have hcx : ContinuousAt h x := by
        rw [Metric.continuousAt_iff]
        intro ε hε
        obtain ⟨δ,hδ,hδbound⟩ := Metric.continuousAt_iff.mp hg.continuousAt ε hε
        refine ⟨δ,hδ,?_⟩
        intro y hy
        have hb := hδbound hy
        rw [Real.dist_eq,hgx,sub_zero,abs_of_nonneg (by positivity : 0 ≤ N*|R^2-‖y‖^2|)] at hb
        exact lt_of_le_of_lt (hglobal y) hb
      exact hcx.continuousWithinAt
  · intro x hx
    apply hout
    rw [hU.frontier_eq] at hx
    exact hx.2

end SeifertSurfaces.OriginalEndpoints.B1Tangency
