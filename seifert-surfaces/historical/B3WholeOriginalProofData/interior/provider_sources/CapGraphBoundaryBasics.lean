import CapAreaEnergy
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cap_lens_lower_radicand_pos (q y : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (hy : y∈Icc (-capLensReach q) (capLensReach q)) : 0<q^2-y^2 := by
  have hv := cap_lens_reach q hq hq1
  have hh : |y|<q := (abs_le.mpr hy).trans_lt hv.2.1
  have hs := (sq_lt_sq₀ (abs_nonneg y) hq.le).mpr hh
  nlinarith [sq_abs y]

theorem cap_lens_lower_smooth (q : ℝ) (hq : 0<q) (hq1 : q≤1/2) :
    ContDiffOn ℝ ∞ (capLensLower q) (Icc (-capLensReach q) (capLensReach q)) := by
  intro y hy
  have hs : ContDiffAt ℝ ∞ (fun y:ℝ => q^2-y^2) y := by fun_prop
  have hh := hs.sqrt (ne_of_gt (cap_lens_lower_radicand_pos q y hq hq1 hy))
  exact (contDiffAt_const.sub hh).contDiffWithinAt

theorem cap_lens_upper_smooth (q : ℝ) (hq : 0<q) (hq1 : q≤1/2) :
    ContDiffOn ℝ ∞ capLensUpper (Icc (-capLensReach q) (capLensReach q)) := by
  intro y hy
  have hs : ContDiffAt ℝ ∞ (fun y:ℝ => 1-y^2) y := by fun_prop
  exact (hs.sqrt (ne_of_gt (cap_transverse_interval_bounds q y hq hq1 hy).2.1)).contDiffWithinAt

theorem cap_lens_boundary_endpoints (q : ℝ) (hq : 0<q) (hq1 : q≤1/2) :
    capLensLower q (-capLensReach q)=capLensUpper (-capLensReach q) ∧
    capLensLower q (capLensReach q)=capLensUpper (capLensReach q) := by
  have hv := cap_lens_reach q hq hq1
  have hq2 : 0≤q^2/2 := by positivity
  have hk : 0≤1-q^2/2 := by nlinarith
  have hL : Real.sqrt (q^2-(capLensReach q)^2)=q^2/2 := by
    have he : q^2-(capLensReach q)^2=(q^2/2)^2 := by rw [hv.2.2.1];ring
    rw [he,Real.sqrt_sq hq2]
  have hU : Real.sqrt (1-(capLensReach q)^2)=1-q^2/2 := by
    have he : 1-(capLensReach q)^2=(1-q^2/2)^2 := by rw [hv.2.2.2];ring
    rw [he,Real.sqrt_sq hk]
  simp [capLensLower,capLensUpper,neg_sq,hL,hU]

theorem cap_lens_lower_deriv (q y : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (hy : y∈Icc (-capLensReach q) (capLensReach q)) :
    HasDerivAt (capLensLower q) (y/Real.sqrt (q^2-y^2)) y := by
  have hs := ((hasDerivAt_const y (q^2)).sub ((hasDerivAt_id y).pow 2)).sqrt
    (ne_of_gt (cap_lens_lower_radicand_pos q y hq hq1 hy))
  dsimp at hs
  convert (hasDerivAt_const y 1).sub hs using 1
  · rfl
  · field_simp
    ring

theorem cap_lens_upper_deriv (q y : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (hy : y∈Icc (-capLensReach q) (capLensReach q)) :
    HasDerivAt capLensUpper (-y/Real.sqrt (1-y^2)) y := by
  have hs := ((hasDerivAt_const y (1:ℝ)).sub ((hasDerivAt_id y).pow 2)).sqrt
    (ne_of_gt (cap_transverse_interval_bounds q y hq hq1 hy).2.1)
  dsimp at hs
  convert hs using 1
  · rfl
  · field_simp
    ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
