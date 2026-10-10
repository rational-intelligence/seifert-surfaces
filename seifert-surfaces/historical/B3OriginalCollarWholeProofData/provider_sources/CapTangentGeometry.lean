import NativeBallH1Extension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def capTangent (s : ℝ) (z : E2) : ℝ := inner ℝ (rotateQuarter (unitCircleParameter s)) z

theorem capTangent_circle (s t : ℝ) : capTangent s (unitCircleParameter t) = Real.sin (t-s) := by
  rw [capTangent, PiLp.inner_apply, Fin.sum_univ_two]
  simp [rotateQuarter, unitCircleParameter, EuclideanSpace.equiv, Real.sin_sub, RCLike.inner_apply]
  ring

theorem capTangent_center (s : ℝ) : capTangent s (unitCircleParameter s) = 0 := by
  rw [capTangent_circle, sub_self, Real.sin_zero]

theorem capTangent_artificial (s q t : ℝ) :
    capTangent s (unitCircleParameter s + q • unitCircleParameter t) = q * Real.sin (t-s) := by
  rw [capTangent, inner_add_right, inner_smul_right]
  change capTangent s (unitCircleParameter s) + q * capTangent s (unitCircleParameter t) = _
  rw [capTangent_center, capTangent_circle, zero_add]

theorem cap_arcsin_bounds (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2) :
    0 < Real.arcsin (q/2) ∧ Real.arcsin (q/2) ≤ Real.pi/6 ∧
    2 * Real.arcsin (q/2) < Real.pi/2 ∧
    Real.sin (2 * Real.arcsin (q/2)) = q * Real.cos (Real.arcsin (q/2)) := by
  have he : 0 < Real.arcsin (q/2) := Real.arcsin_pos.mpr (by linarith)
  have hs : Real.arcsin (1/2) = Real.pi/6 := by
    rw [← Real.sin_pi_div_six]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hb : Real.arcsin (q/2) ≤ Real.pi/6 := by
    rw [← hs]
    exact Real.arcsin_le_arcsin (by linarith)
  refine ⟨he,hb,by linarith [Real.pi_pos],?_⟩
  rw [Real.sin_two_mul, Real.sin_arcsin (by linarith) (by linarith)]
  ring

theorem cap_arcsin_tangent_endpoint (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2) :
    Real.arcsin (q * Real.cos (Real.arcsin (q/2))) = 2 * Real.arcsin (q/2) := by
  obtain ⟨he,hb,hp,hs⟩ := cap_arcsin_bounds q hq hq1
  rw [← hs]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) hp.le

theorem cap_base_endpoints (s q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2) (b : ℝ → E2) :
    b (s + Real.arcsin (q * Real.sin ((s+Real.pi/2+Real.arcsin (q/2))-s))) =
      b (s+2*Real.arcsin (q/2)) ∧
    b (s + Real.arcsin (q * Real.sin ((s+3*Real.pi/2-Real.arcsin (q/2))-s))) =
      b (s-2*Real.arcsin (q/2)) := by
  have h1 : Real.sin (Real.pi/2+Real.arcsin (q/2)) = Real.cos (Real.arcsin (q/2)) := by
    rw [Real.sin_add]; simp
  have h2 : Real.sin (3*Real.pi/2-Real.arcsin (q/2)) = -Real.cos (Real.arcsin (q/2)) := by
    rw [show 3*Real.pi/2-Real.arcsin (q/2) = Real.pi + (Real.pi/2-Real.arcsin (q/2)) by ring]
    rw [Real.sin_add,Real.sin_sub];simp
  constructor
  · rw [show s+Real.pi/2+Real.arcsin (q/2)-s = Real.pi/2+Real.arcsin (q/2) by ring,h1,
      cap_arcsin_tangent_endpoint q hq hq1]
  · rw [show s+3*Real.pi/2-Real.arcsin (q/2)-s = 3*Real.pi/2-Real.arcsin (q/2) by ring,h2,
      mul_neg,Real.arcsin_neg,cap_arcsin_tangent_endpoint q hq hq1]
    congr 1
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
