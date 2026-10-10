import QuotientGeometry
import SegmentCalculus

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearLocalization
open SeifertSurfaces.AppendixACoordinates

namespace QuotientHelpers

lemma jetSegment_joint_continuousOn (Ω : Set E2) (hΩ : IsOpen Ω) (u : E2 → ℝ)
    (hC1 : ContDiffOn ℝ 1 u Ω) (x₀ : E2) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω) (k : Fin 2) (h : ℝ) (hh : |h| < r) :
    ContinuousOn (fun z : E2 × ℝ => jetSegment u k h z.1 z.2)
      (Metric.closedBall x₀ (3 * r) ×ˢ Icc (0 : ℝ) 1) := by
  have hj : ContinuousOn (firstJet u) Ω :=
    continuousOn_id.prodMk (hC1.continuousOn.prodMk (Helpers.gradient_continuousOn Ω hΩ u hC1))
  have hs : Continuous (shift k h) := by unfold shift; fun_prop
  have hfst : ContinuousOn (fun z : E2 × ℝ => firstJet u z.1)
      (Metric.closedBall x₀ (3 * r) ×ˢ Icc (0 : ℝ) 1) :=
    hj.comp continuous_fst.continuousOn (fun z hz =>
      hball (Metric.closedBall_subset_closedBall (by linarith) hz.1))
  have hshift : ContinuousOn (fun z : E2 × ℝ => firstJet u (shift k h z.1))
      (Metric.closedBall x₀ (3 * r) ×ˢ Icc (0 : ℝ) 1) :=
    hj.comp (hs.comp continuous_fst).continuousOn (fun z hz =>
      hball (shift_mem_closedBall x₀ z.1 r hr hz.1 k h hh))
  exact (continuousOn_const.sub continuous_snd.continuousOn).smul hfst |>.add
    (continuous_snd.continuousOn.smul hshift)

section AverageContinuity
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma integral_continuousOn_ball (x₀ : E2) (r : ℝ) (hr : 0 < r)
    (f : E2 → ℝ → F)
    (hf : ContinuousOn f.uncurry (Metric.closedBall x₀ (3 * r) ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousOn (fun x => ∫ t in Icc (0 : ℝ) 1, f x t) (Metric.ball x₀ (2 * r)) := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x₀ (3 * r)).prod isCompact_Icc).exists_bound_of_continuousOn hf
  intro x hx
  have hx3 : x ∈ Metric.ball x₀ (3 * r) := Metric.ball_subset_ball (by linarith) hx
  have hn : Metric.closedBall x₀ (3 * r) ∈ 𝓝 x :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hx3) Metric.ball_subset_closedBall
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_of_dominated (bound := fun _ : ℝ => M)
  · filter_upwards [hn] with y hy
    exact ((hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hy, ht⟩)).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  · filter_upwards [hn] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hM (y, t) ⟨hy, ht⟩
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun y hy => ⟨hy, ht⟩)).continuousAt hn

lemma jet_average_continuousOn (Ω : Set E2) (hΩ : IsOpen Ω) (u : E2 → ℝ)
    (hC1 : ContDiffOn ℝ 1 u Ω) (x₀ : E2) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω) (J T : Set Jet)
    (hT : Convex ℝ T) (hTJ : T ⊆ J)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (k : Fin 2) (h : ℝ) (hhr : |h| < r) (f : Jet → F) (hf : ContinuousOn f J) :
    ContinuousOn (fun x => ∫ t in Icc (0 : ℝ) 1, f (jetSegment u k h x t))
      (Metric.ball x₀ (2 * r)) := by
  apply integral_continuousOn_ball x₀ r hr
  exact hf.comp (jetSegment_joint_continuousOn Ω hΩ u hC1 x₀ r hr hball k h hhr)
    (fun z hz => hTJ (jetSegment_mem u x₀ r hr T hT hjetsT k h hhr z.1 hz.1 z.2 hz.2))

end AverageContinuity
end QuotientHelpers

theorem R2_averaged_coefficients_continuous
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (x₀ : E2) (r : ℝ) (hr : 0 < r) (T : Set Jet)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (hT : Convex ℝ T) (hTJ : T ⊆ J)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (k : Fin 2) (h : ℝ) (hh : 0 < |h|) (hhr : |h| < r) :
    coefficientsContinuousOn (Metric.ball x₀ (2 * r)) (averagedCoefficients Q u k h) ∧
      CoefficientMeasurableOn (Metric.ball x₀ (2 * r)) (averagedCoefficients Q u k h) := by
  have ha := QuotientHelpers.jet_average_continuousOn Ω hΩ u hC1 x₀ r hr hball J T hT hTJ hjetsT k h hhr
    (fluxDp Q) (QuotientHelpers.p_partial_continuousOn J hJ Q.flux Q.flux_smooth)
  have hc := QuotientHelpers.jet_average_continuousOn Ω hΩ u hC1 x₀ r hr hball J T hT hTJ hjetsT k h hhr
    (fluxDz Q) (QuotientHelpers.z_partial_continuousOn J hJ Q.flux Q.flux_smooth)
  have hd := QuotientHelpers.jet_average_continuousOn Ω hΩ u hC1 x₀ r hr hball J T hT hTJ hjetsT k h hhr
    (fun j => fluxDx Q j (coordinateVector 2 k))
    ((QuotientHelpers.x_partial_continuousOn J hJ Q.flux Q.flux_smooth).clm_apply continuousOn_const)
  have hb := QuotientHelpers.jet_average_continuousOn Ω hΩ u hC1 x₀ r hr hball J T hT hTJ hjetsT k h hhr
    (lowerDp Q) (QuotientHelpers.p_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth)
  have hq := QuotientHelpers.jet_average_continuousOn Ω hΩ u hC1 x₀ r hr hball J T hT hTJ hjetsT k h hhr
    (lowerDz Q) (QuotientHelpers.z_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth)
  have hf := QuotientHelpers.jet_average_continuousOn Ω hΩ u hC1 x₀ r hr hball J T hT hTJ hjetsT k h hhr
    (fun j => lowerDx Q j (coordinateVector 2 k))
    ((QuotientHelpers.x_partial_continuousOn J hJ Q.lowerOrder Q.lowerOrder_smooth).clm_apply continuousOn_const)
  exact ⟨⟨ha, hc, hd, hb, hq, hf⟩,
    ha.aestronglyMeasurable measurableSet_ball, hc.aestronglyMeasurable measurableSet_ball,
    hd.aestronglyMeasurable measurableSet_ball, hb.aestronglyMeasurable measurableSet_ball,
    hq.aestronglyMeasurable measurableSet_ball, hf.aestronglyMeasurable measurableSet_ball⟩

end SeifertSurfaces.QuasilinearLocalization
