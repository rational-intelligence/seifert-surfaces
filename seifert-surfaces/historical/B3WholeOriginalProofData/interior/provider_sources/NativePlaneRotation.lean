import NativeBallH1Extension

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def rotatePlane (s : ℝ) (z : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![Real.cos s * z 0 - Real.sin s * z 1,
      Real.sin s * z 0 + Real.cos s * z 1]

theorem rotatePlane_norm (s : ℝ) (z : E2) : ‖rotatePlane s z‖ = ‖z‖ := by
  have he : ‖rotatePlane s z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change (Real.cos s * z 0 - Real.sin s * z 1) ^ 2 +
      (Real.sin s * z 0 + Real.cos s * z 1) ^ 2 = z 0 ^ 2 + z 1 ^ 2
    nlinarith [Real.cos_sq_add_sin_sq s,
      mul_nonneg (sq_nonneg (z 0)) (sq_nonneg (Real.cos s)),
      congrArg (fun t : ℝ => t * z 0 ^ 2) (Real.cos_sq_add_sin_sq s),
      congrArg (fun t : ℝ => t * z 1 ^ 2) (Real.cos_sq_add_sin_sq s)]
  nlinarith [norm_nonneg (rotatePlane s z), norm_nonneg z]

theorem rotatePlane_neg_left (s : ℝ) (z : E2) : rotatePlane (-s) (rotatePlane s z) = z := by
  ext i
  fin_cases i <;> simp [rotatePlane]
  · nlinarith [congrArg (fun t : ℝ => t * z 0) (Real.cos_sq_add_sin_sq s)]
  · nlinarith [congrArg (fun t : ℝ => t * z 1) (Real.cos_sq_add_sin_sq s)]

def planeRotation (s : ℝ) : E2 ≃ₗᵢ[ℝ] E2 where
  toFun := rotatePlane s
  invFun := rotatePlane (-s)
  left_inv := rotatePlane_neg_left s
  right_inv z := by simpa only [neg_neg] using rotatePlane_neg_left (-s) z
  map_add' z w := by ext i; fin_cases i <;> simp [rotatePlane] <;> ring
  map_smul' a z := by ext i; fin_cases i <;> simp [rotatePlane] <;> ring
  norm_map' := rotatePlane_norm s

@[simp] theorem planeRotation_apply (s : ℝ) (z : E2) : planeRotation s z = rotatePlane s z := rfl

@[simp] theorem planeRotation_symm_apply (s : ℝ) (z : E2) :
    (planeRotation s).symm z = rotatePlane (-s) z := rfl

theorem planeRotation_circle (s t : ℝ) :
    planeRotation s (unitCircleParameter t) = unitCircleParameter (s + t) := by
  ext i
  fin_cases i <;> simp [planeRotation_apply, rotatePlane, unitCircleParameter,
    Real.cos_add, Real.sin_add] <;> ring

theorem planeRotation_coord (s : ℝ) (z : E2) (j : Fin 2) :
    planeRotation s z j =
      z 0 * unitCircleParameter s j + z 1 * rotateQuarter (unitCircleParameter s) j := by
  fin_cases j <;> simp [planeRotation_apply, rotatePlane, unitCircleParameter, rotateQuarter] <;> ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
