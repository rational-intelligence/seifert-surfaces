import CapTangentGeometry
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def capNormal (s : ℝ) (z : E2) : ℝ := inner ℝ (unitCircleParameter s) z

def capRotateLinear (s : ℝ) : E2 →ₗ[ℝ] E2 where
  toFun z := z 0 • unitCircleParameter s + z 1 • rotateQuarter (unitCircleParameter s)
  map_add' := by intro x y; simp [add_smul];module
  map_smul' := by intro a z; simp [mul_smul,smul_add]

theorem capRotateLinear_norm_sq (s : ℝ) (z : E2) :
    ‖capRotateLinear s z‖^2 = ‖z‖^2 := by
  change ‖z 0 • unitCircleParameter s + z 1 • rotateQuarter (unitCircleParameter s)‖^2 = _
  rw [frame_norm_sq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]

def capRotateIsometry (s : ℝ) : E2 →ₗᵢ[ℝ] E2 where
  toLinearMap := capRotateLinear s
  norm_map' z := by nlinarith [capRotateLinear_norm_sq s z,norm_nonneg (capRotateLinear s z),norm_nonneg z]

theorem capRotateLinear_inverse (s : ℝ) (z : E2) :
    capRotateLinear s (capRotateLinear (-s) z) = z := by
  ext i
  fin_cases i <;> simp [capRotateLinear,unitCircleParameter,rotateQuarter,EuclideanSpace.equiv]
  · linear_combination (z 0) * Real.cos_sq_add_sin_sq s
  · linear_combination (z 1) * Real.cos_sq_add_sin_sq s

def capRotateEquiv (s : ℝ) : E2 ≃ₗᵢ[ℝ] E2 := LinearIsometryEquiv.ofSurjective
  (capRotateIsometry s) (fun z => ⟨capRotateLinear (-s) z,capRotateLinear_inverse s z⟩)

theorem capRotateEquiv_apply (s : ℝ) (z : E2) :
    capRotateEquiv s z = z 0 • unitCircleParameter s + z 1 • rotateQuarter (unitCircleParameter s) := rfl

theorem capRotateEquiv_center (s : ℝ) : capRotateEquiv s (coordinateVector 2 0) = unitCircleParameter s := by
  simp [capRotateEquiv_apply,coordinateVector]

theorem capRotateEquiv_tangent (s : ℝ) (z : E2) : capTangent s (capRotateEquiv s z) = z 1 := by
  rw [capTangent,capRotateEquiv_apply,PiLp.inner_apply,Fin.sum_univ_two]
  simp [rotateQuarter,unitCircleParameter,EuclideanSpace.equiv,Real.inner_apply]
  linear_combination (z 1) * Real.cos_sq_add_sin_sq s

theorem capRotateEquiv_normal (s : ℝ) (z : E2) : capNormal s (capRotateEquiv s z) = z 0 := by
  rw [capNormal,capRotateEquiv_apply,PiLp.inner_apply,Fin.sum_univ_two]
  simp [rotateQuarter,unitCircleParameter,EuclideanSpace.equiv,Real.inner_apply]
  linear_combination (z 0) * Real.cos_sq_add_sin_sq s

theorem capRotateEquiv_cap (s q : ℝ) (z : E2) :
    capRotateEquiv s z ∈ planarCap (unitCircleParameter s) q ↔
    z ∈ planarCap (coordinateVector 2 0) q := by
  simp only [planarCap,mem_inter_iff,disc,Metric.mem_ball,dist_zero_right]
  rw [(capRotateEquiv s).norm_map,← capRotateEquiv_center s,(capRotateEquiv s).isometry.dist_eq]

theorem capTangent_abs_on_closed_ball (s q : ℝ) (z : E2)
    (hz : z ∈ Metric.closedBall (unitCircleParameter s) q) : |capTangent s z| ≤ q := by
  have hr : ‖rotateQuarter (unitCircleParameter s)‖ = 1 := by
    have hh := frame_norm_sq 0 1 s
    simp only [zero_smul,one_smul,zero_add,zero_pow (by decide : 2≠0),one_pow,zero_add] at hh
    nlinarith [norm_nonneg (rotateQuarter (unitCircleParameter s))]
  have he : capTangent s (z-unitCircleParameter s) = capTangent s z := by
    rw [capTangent,inner_sub_right]
    change capTangent s z-capTangent s (unitCircleParameter s) = _
    rw [capTangent_center,sub_zero]
  rw [← he]
  have hh := norm_inner_le_norm (𝕜:=ℝ) (rotateQuarter (unitCircleParameter s)) (z-unitCircleParameter s)
  rw [hr,one_mul] at hh
  exact hh.trans (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz)
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
