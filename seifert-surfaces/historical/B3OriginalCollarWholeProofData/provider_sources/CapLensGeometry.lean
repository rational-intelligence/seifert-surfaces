import CapRotatedCoordinates
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def capLensReach (q : ℝ) : ℝ := q*Real.cos (Real.arcsin (q/2))
def capLensLower (q y : ℝ) : ℝ := 1-Real.sqrt (q^2-y^2)
def capLensUpper (y : ℝ) : ℝ := Real.sqrt (1-y^2)

theorem cap_lens_reach (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2) :
    0 < capLensReach q ∧ capLensReach q < q ∧
    (capLensReach q)^2 = q^2-q^4/4 ∧
    (capLensReach q)^2 = 1-(1-q^2/2)^2 := by
  have he := cap_arcsin_bounds q hq hq1
  have hp : 0 < Real.cos (Real.arcsin (q/2)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,he.1],by linarith [Real.pi_pos,he.2.1]⟩
  have hc : Real.cos (Real.arcsin (q/2)) < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (x:=0) (y:=Real.arcsin (q/2))
      le_rfl (by linarith [Real.pi_pos,he.2.1]) he.1
  have hs : Real.sin (Real.arcsin (q/2)) = q/2 := Real.sin_arcsin (by linarith) (by linarith)
  have hcs : Real.cos (Real.arcsin (q/2))^2 = 1-(q/2)^2 := by
    nlinarith [Real.cos_sq_add_sin_sq (Real.arcsin (q/2))]
  have hv : (capLensReach q)^2 = q^2-q^4/4 := by
    dsimp [capLensReach]
    rw [mul_pow,hcs]
    ring
  refine ⟨mul_pos hq hp,?_,hv,?_⟩
  · dsimp [capLensReach]
    nlinarith
  · rw [hv]
    ring

theorem cap_lens_tangent_sq_bound (q x y : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2)
    (h1 : x^2+y^2 ≤ 1) (h2 : (x-1)^2+y^2 ≤ q^2) :
    y^2 ≤ (capLensReach q)^2 := by
  have hv := (cap_lens_reach q hq hq1).2.2.2
  have hq2 : q^2 ≤ 1/4 := by nlinarith
  let k := 1-q^2/2
  have hk : 0 ≤ k := by dsimp [k]; nlinarith
  have hk1 : k ≤ 1 := by dsimp [k]; nlinarith [sq_nonneg q]
  by_cases hx : k ≤ x
  · have hs : k^2 ≤ x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0≤x+k by linarith)]
    change (capLensReach q)^2=1-k^2 at hv
    nlinarith
  · have hx1 : x ≤ k := (lt_of_not_ge hx).le
    have hs : (k-1)^2 ≤ (x-1)^2 := by
      nlinarith [mul_nonneg (show 0≤k-x by linarith) (show 0≤2-x-k by linarith)]
    have he : q^2-(k-1)^2=(capLensReach q)^2 := by
      rw [(cap_lens_reach q hq hq1).2.2.1]
      dsimp [k]
      ring
    nlinarith

theorem cap_lens_tangent_bound (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2) (z : E2)
    (hz : z ∈ Metric.closedBall (0:E2) 1 ∩ Metric.closedBall (coordinateVector 2 0) q) :
    |z 1| ≤ capLensReach q := by
  have h1 : z 0^2+z 1^2 ≤ 1 := by
    have hh := (Metric.mem_closedBall.mp hz.1)
    rw [dist_zero_right] at hh
    have hn := EuclideanSpace.real_norm_sq_eq z
    rw [Fin.sum_univ_two] at hn
    nlinarith [norm_nonneg z]
  have h2 : (z 0-1)^2+z 1^2 ≤ q^2 := by
    have hh := (Metric.mem_closedBall.mp hz.2)
    rw [dist_eq_norm] at hh
    have hn := EuclideanSpace.real_norm_sq_eq (z-coordinateVector 2 0)
    rw [Fin.sum_univ_two] at hn
    simp [PiLp.sub_apply,coordinateVector,EuclideanSpace.single_apply] at hn
    change ‖z-coordinateVector 2 0‖^2=(z 0-1)^2+z 1^2 at hn
    have hs := (sq_le_sq₀ (norm_nonneg (z-coordinateVector 2 0)) hq.le).mpr hh
    nlinarith
  have hb := cap_lens_tangent_sq_bound q (z 0) (z 1) hq hq1 h1 h2
  exact (sq_le_sq₀ (abs_nonneg _) (cap_lens_reach q hq hq1).1.le).mp (by simpa [sq_abs] using hb)

theorem cap_lens_arcsin_range (q y : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2)
    (hy : |y| ≤ capLensReach q) :
    Real.arcsin y ∈ Icc (-2*Real.arcsin (q/2)) (2*Real.arcsin (q/2)) := by
  have he : Real.arcsin (capLensReach q)=2*Real.arcsin (q/2) := cap_arcsin_tangent_endpoint q hq hq1
  have hb := abs_le.mp hy
  constructor
  · have hh := Real.arcsin_le_arcsin hb.1
    rw [Real.arcsin_neg,he] at hh
    linarith
  · rw [← he]
    exact Real.arcsin_le_arcsin hb.2

theorem cap_lens_slice (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2) (z : E2)
    (hy : |z 1| < capLensReach q) :
    z ∈ planarCap (coordinateVector 2 0) q ↔
      z 0 ∈ Ioo (capLensLower q (z 1)) (capLensUpper (z 1)) := by
  have hv := cap_lens_reach q hq hq1
  have hyq : |z 1| < q := hy.trans hv.2.1
  have hy1 : |z 1| < 1 := by linarith
  have hyq2 : z 1^2 < q^2 := by
    have hh := (sq_lt_sq₀ (abs_nonneg (z 1)) hq.le).mpr hyq
    simpa [sq_abs] using hh
  have hy12 : z 1^2 < 1 := by
    have hh := (sq_lt_sq₀ (abs_nonneg (z 1)) (show 0≤(1:ℝ) by norm_num)).mpr hy1
    simpa [sq_abs] using hh
  have hLsq : Real.sqrt (q^2-z 1^2)^2=q^2-z 1^2 := Real.sq_sqrt (by linarith)
  have hUsq : Real.sqrt (1-z 1^2)^2=1-z 1^2 := Real.sq_sqrt (by linarith)
  have hLpos : 0 < Real.sqrt (q^2-z 1^2) := Real.sqrt_pos.mpr (by linarith)
  have hUpos : 0 < Real.sqrt (1-z 1^2) := Real.sqrt_pos.mpr (by linarith)
  have hLle : Real.sqrt (q^2-z 1^2) ≤ q := by nlinarith [sq_nonneg (z 1)]
  have hUle : Real.sqrt (1-z 1^2) ≤ 1 := by nlinarith [sq_nonneg (z 1)]
  have hn1 := EuclideanSpace.real_norm_sq_eq z
  rw [Fin.sum_univ_two] at hn1
  have hn2 := EuclideanSpace.real_norm_sq_eq (z-coordinateVector 2 0)
  rw [Fin.sum_univ_two] at hn2
  simp [PiLp.sub_apply,coordinateVector] at hn2
  change ‖z-coordinateVector 2 0‖^2=(z 0-1)^2+z 1^2 at hn2
  simp only [planarCap,disc,mem_inter_iff,Metric.mem_ball,dist_eq_norm,sub_zero]
  change (‖z‖<1 ∧ ‖z-coordinateVector 2 0‖<q) ↔ _
  constructor
  · intro hz
    have h1 := (sq_lt_sq₀ (norm_nonneg z) (show 0≤(1:ℝ) by norm_num)).mpr hz.1
    have h2 := (sq_lt_sq₀ (norm_nonneg (z-coordinateVector 2 0)) hq.le).mpr hz.2
    have hxq : |z 0-1| < q := (sq_lt_sq₀ (abs_nonneg _) hq.le).mp (by rw [sq_abs]; nlinarith [sq_nonneg (z 1)])
    have hx0 : 0 < z 0 := by have hh := (abs_lt.mp hxq).1; linarith
    have hxl : 1-Real.sqrt (q^2-z 1^2) < z 0 := by
      have hx := (sq_lt_sq₀ (abs_nonneg (z 0-1)) hLpos.le).mp (by rw [sq_abs];nlinarith)
      linarith [abs_lt.mp hx |>.1]
    have hxu : z 0 < Real.sqrt (1-z 1^2) := by nlinarith
    exact ⟨hxl,hxu⟩
  · intro hz
    change 1-Real.sqrt (q^2-z 1^2)<z 0 ∧ z 0<Real.sqrt (1-z 1^2) at hz
    have hx0 : 0 < z 0 := by linarith
    have hx1 : z 0 < 1 := hz.2.trans_le hUle
    have h1 : ‖z‖^2<1^2 := by
      have hs := (sq_lt_sq₀ hx0.le hUpos.le).mpr hz.2
      nlinarith
    have h2 : ‖z-coordinateVector 2 0‖^2<q^2 := by
      have hs := (sq_lt_sq₀ (show 0≤1-z 0 by linarith) hLpos.le).mpr (show 1-z 0<Real.sqrt (q^2-z 1^2) by linarith)
      nlinarith
    exact ⟨(sq_lt_sq₀ (norm_nonneg z) (show 0≤(1:ℝ) by norm_num)).mp h1,
      (sq_lt_sq₀ (norm_nonneg (z-coordinateVector 2 0)) hq.le).mp h2⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
