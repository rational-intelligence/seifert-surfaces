import CapLensGeometry
import CapCoordinateVolume
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cap_zero_coordinates_iff (q : ℝ) (hq : 0 < q) (z : E2) :
    z ∈ planarCap (coordinateVector 2 0) q ↔
      z 0^2+z 1^2<1 ∧ (z 0-1)^2+z 1^2<q^2 := by
  have hn1 := EuclideanSpace.real_norm_sq_eq z
  rw [Fin.sum_univ_two] at hn1
  have hn2 := EuclideanSpace.real_norm_sq_eq (z-coordinateVector 2 0)
  rw [Fin.sum_univ_two] at hn2
  simp [PiLp.sub_apply,coordinateVector] at hn2
  change ‖z-coordinateVector 2 0‖^2=(z 0-1)^2+z 1^2 at hn2
  simp only [planarCap,disc,mem_inter_iff,Metric.mem_ball,dist_eq_norm,sub_zero]
  rw [← hn1,← hn2]
  exact and_congr (by simpa using (sq_lt_sq₀ (norm_nonneg z) (show 0≤(1:ℝ) by norm_num)).symm)
    (sq_lt_sq₀ (norm_nonneg (z-coordinateVector 2 0)) hq.le).symm

theorem cap_open_tangent_bound (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2) (z : E2)
    (hz : z ∈ planarCap (coordinateVector 2 0) q) : |z 1|<capLensReach q := by
  have hh := (cap_zero_coordinates_iff q hq z).mp hz
  have hv := (cap_lens_reach q hq hq1).2.2.2
  let k := 1-q^2/2
  have hq2 : q^2 ≤ 1/4 := by nlinarith
  have hk : 0≤k := by dsimp [k];nlinarith
  have hk1 : k≤1 := by dsimp [k];nlinarith [sq_nonneg q]
  have hs : z 1^2<(capLensReach q)^2 := by
    by_cases hx : k≤z 0
    · have hsk : k^2≤z 0^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0≤z 0+k by linarith)]
      change (capLensReach q)^2=1-k^2 at hv
      nlinarith [hh.1]
    · have hx1 : z 0≤k := (lt_of_not_ge hx).le
      have hsk : (k-1)^2≤(z 0-1)^2 := by nlinarith [mul_nonneg (show 0≤k-z 0 by linarith) (show 0≤2-z 0-k by linarith)]
      have he : q^2-(k-1)^2=(capLensReach q)^2 := by
        rw [(cap_lens_reach q hq hq1).2.2.1]
        dsimp [k]
        ring
      nlinarith [hh.2]
  exact (sq_lt_sq₀ (abs_nonneg _) (cap_lens_reach q hq hq1).1.le).mp (by simpa [sq_abs] using hs)

theorem cap_zero_graph_iff (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2) (z : E2) :
    z ∈ planarCap (coordinateVector 2 0) q ↔
      z 1∈Ioo (-capLensReach q) (capLensReach q) ∧
      z 0∈Ioo (capLensLower q (z 1)) (capLensUpper (z 1)) := by
  constructor
  · intro hz
    have hy := cap_open_tangent_bound q hq hq1 z hz
    exact ⟨abs_lt.mp hy,(cap_lens_slice q hq hq1 z hy).mp hz⟩
  · intro hz
    exact (cap_lens_slice q hq hq1 z (abs_lt.mpr hz.1)).mpr hz.2

theorem cap_coordinate_graph_iff (s q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2) (p : ℝ×ℝ) :
    capCoordinateEquiv s p∈planarCap (unitCircleParameter s) q ↔
      p.2∈Ioo (-capLensReach q) (capLensReach q) ∧
      p.1∈Ioo (capLensLower q p.2) (capLensUpper p.2) := by
  change capRotateEquiv s (capPairEquiv.symm p)∈_ ↔ _
  rw [capRotateEquiv_cap,cap_zero_graph_iff q hq hq1]
  rfl

theorem cap_lens_width_pos (q y : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2)
    (hy : |y|<capLensReach q) : capLensLower q y<capLensUpper y := by
  have hv := cap_lens_reach q hq hq1
  have hyq : y^2<q^2 := by have hh := (sq_lt_sq₀ (abs_nonneg y) hq.le).mpr (hy.trans hv.2.1);simpa [sq_abs] using hh
  have hyv : y^2<(capLensReach q)^2 := by have hh := (sq_lt_sq₀ (abs_nonneg y) hv.1.le).mpr hy;simpa [sq_abs] using hh
  have hq2 : q^2≤1/4 := by nlinarith
  have hU : Real.sqrt (1-y^2)^2=1-y^2 := Real.sq_sqrt (by nlinarith)
  have hL : Real.sqrt (q^2-y^2)^2=q^2-y^2 := Real.sq_sqrt (by nlinarith)
  have hU0 := Real.sqrt_nonneg (1-y^2)
  have hL0 := Real.sqrt_nonneg (q^2-y^2)
  have hU1 : Real.sqrt (1-y^2)≤1 := by nlinarith [sq_nonneg y]
  have hk : 0≤1-q^2/2 := by nlinarith
  have hUk : 1-q^2/2<Real.sqrt (1-y^2) := by nlinarith [hv.2.2.2]
  have he : (1-Real.sqrt (1-y^2))^2<Real.sqrt (q^2-y^2)^2 := by nlinarith
  have hh : 1-Real.sqrt (1-y^2)<Real.sqrt (q^2-y^2) :=
    (sq_lt_sq₀ (by linarith) hL0).mp he
  unfold capLensLower capLensUpper
  linarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
