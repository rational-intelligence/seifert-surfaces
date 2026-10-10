import CapBoundaryCoordinateCurves
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cap_circle_periodic : Periodic unitCircleParameter (2*Real.pi) := by
  intro t
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [unitCircleParameter,EuclideanSpace.equiv,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem cap_circle_distance_sq (s t : ℝ) :
    dist (unitCircleParameter t) (unitCircleParameter s)^2=2-2*Real.cos (t-s) := by
  rw [dist_eq_norm,cap_circle_frame s t]
  have hv : Real.cos (t-s) • unitCircleParameter s+Real.sin (t-s) • rotateQuarter (unitCircleParameter s)-unitCircleParameter s =
      (Real.cos (t-s)-1) • unitCircleParameter s+Real.sin (t-s) • rotateQuarter (unitCircleParameter s) := by module
  rw [hv,frame_norm_sq]
  nlinarith [Real.cos_sq_add_sin_sq (t-s)]

theorem cap_local_circle_ball_iff (s q t : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (ht : t∈Icc (s-Real.pi) (s+Real.pi)) :
    unitCircleParameter t∈Metric.ball (unitCircleParameter s) q ↔
      t∈Ioo (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)) := by
  have he := cap_arcsin_bounds q hq hq1
  have he0 : 0≤2*Real.arcsin (q/2) := by linarith [he.1]
  have hepi : 2*Real.arcsin (q/2)≤Real.pi := by linarith [he.2.2.1,Real.pi_pos]
  have hs : Real.sin (Real.arcsin (q/2))=q/2 := Real.sin_arcsin (by linarith) (by linarith)
  have hc : Real.cos (2*Real.arcsin (q/2))=1-q^2/2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.cos_sq_add_sin_sq (Real.arcsin (q/2))]
  have hab : |t-s|≤Real.pi := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hcos : Real.cos (2*Real.arcsin (q/2))<Real.cos (t-s) ↔ |t-s|<2*Real.arcsin (q/2) := by
    rw [← Real.cos_abs (t-s)]
    exact Real.strictAntiOn_cos.lt_iff_gt ⟨he0,hepi⟩ ⟨abs_nonneg _,hab⟩
  rw [Metric.mem_ball,← sq_lt_sq₀ (dist_nonneg) hq.le,cap_circle_distance_sq]
  change (2-2*Real.cos (t-s)<q^2) ↔ _
  constructor
  · intro hh
    have hh1 : |t-s|<2*Real.arcsin (q/2) := hcos.mp (by rw [hc];linarith)
    exact ⟨by linarith [abs_lt.mp hh1 |>.1],by linarith [abs_lt.mp hh1 |>.2]⟩
  · intro hh
    have habs : |t-s|<2*Real.arcsin (q/2) := abs_lt.mpr ⟨by linarith [hh.1],by linarith [hh.2]⟩
    have hh := hcos.mpr habs
    rw [hc] at hh
    linarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
