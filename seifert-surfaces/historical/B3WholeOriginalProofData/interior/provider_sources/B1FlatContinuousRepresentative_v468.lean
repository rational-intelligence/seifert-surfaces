import B1HalfDiscNativeClassicalInterior_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
local instance (R : ℝ) : DecidablePred (· ∈ halfDisc R) := Classical.decPred _

/-- A native flat-edge bound supplies an actual continuous representative,
with value 1 on the flat edge. -/
theorem halfdisc_flat_continuous_representative_v468
    (R S M : ℝ) (hR : 0 < R) (hM : 0 ≤ M) (hS : 0 ≤ S)
    (f : E2 → ℝ) (hf : ContinuousOn f (halfDisc R))
    (hbound : ∀ x ∈ halfDisc R, |f x-1| ≤ M*(2*S*x 1-(x 1)^2)) :
    let h := (halfDisc R).piecewise f (fun _ => 1)
    ContinuousOn h (Metric.ball 0 R ∩ {x : E2 | 0 ≤ x 1}) ∧
    (∀ x : E2, x 1 = 0 → h x = 1) ∧
    (∀ x ∈ halfDisc R, h x = f x) := by
  classical
  let U := halfDisc R
  let h := U.piecewise f (fun _ => 1)
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  have hflat (x : E2) (hx : x 1 = 0) : h x = 1 := by
    simp only [h,Set.piecewise]
    split_ifs with hh
    · exact False.elim (by have ht := hh.2; rw [hx] at ht; linarith)
    · rfl
  have heq (x : E2) (hx : x ∈ U) : h x = f x := by simp only [h,Set.piecewise,ite_eq_left hx]
  refine ⟨?_,hflat,heq⟩
  intro x hx
  by_cases hxp : 0 < x 1
  · have hxU : x ∈ U := ⟨hx.1,hxp⟩
    have hn : h =ᶠ[𝓝 x] f := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact heq y hy
    exact ((hf.continuousAt (hU.mem_nhds hxU)).congr hn.symm).continuousWithinAt
  · have hx0 : x 1 = 0 := le_antisymm (le_of_not_gt hxp) hx.2
    have hxc : ContinuousAt h x := by
      rw [Metric.continuousAt_iff]
      intro ε hε
      let C := 2*M*S+1
      have hC : 0 < C := by dsimp [C]; positivity
      refine ⟨ε/C,div_pos hε hC,?_⟩
      intro y hy
      rw [hflat x hx0]
      by_cases hyU : y ∈ U
      · rw [heq y hyU,Real.dist_eq]
        have hycoord : |y 1| ≤ dist y x := by
          have hh := PiLp.norm_apply_le (y-x) (1 : Fin 2)
          simpa only [PiLp.sub_apply,hx0,sub_zero,dist_eq_norm,Real.norm_eq_abs] using hh
        have hb : |f y-1| ≤ 2*M*S*dist y x := by
          have hs : M*(2*S*y 1-(y 1)^2) ≤ 2*M*S*|y 1| := by
            rw [abs_of_pos hyU.2]
            nlinarith [mul_nonneg hM (sq_nonneg (y 1))]
          exact (hbound y hyU).trans (hs.trans (mul_le_mul_of_nonneg_left hycoord (by positivity)))
        have hc : 2*M*S ≤ C := by dsimp [C]; linarith
        have he : C*dist y x < ε := by
          have hεd := (lt_div_iff₀ hC).mp hy
          nlinarith
        exact lt_of_le_of_lt (hb.trans (mul_le_mul_of_nonneg_right hc dist_nonneg)) he
      · have hh : h y = 1 := by simp only [h,Set.piecewise,ite_eq_right hyU]
        rw [hh,dist_self]
        exact hε
    exact hxc.continuousWithinAt

end SeifertSurfaces.OriginalEndpoints.B1Tangency
