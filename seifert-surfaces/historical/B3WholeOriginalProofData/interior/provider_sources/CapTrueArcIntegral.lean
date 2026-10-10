import CapTrueArcGeometry
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cap_circlePatch_integral (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (f : ℝ→ℝ) (hf : Periodic f (2*Real.pi)) :
    (∫ t in circlePatch (unitCircleParameter s) q, f t) =
      ∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), f t := by
  classical
  let H : Set ℝ := {t | unitCircleParameter t∈Metric.ball (unitCircleParameter s) q}
  let F := H.indicator f
  have hHm : MeasurableSet H := Metric.isOpen_ball.measurableSet.preimage circle_contDiff.continuous.measurable
  have hFp : Periodic F (2*Real.pi) := by
    intro t
    dsimp [F,H]
    change (if unitCircleParameter (t+2*Real.pi)∈Metric.ball (unitCircleParameter s) q then f (t+2*Real.pi) else 0) =
      (if unitCircleParameter t∈Metric.ball (unitCircleParameter s) q then f t else 0)
    rw [cap_circle_periodic t,hf t]
  have hset : Icc (s-Real.pi) (s+Real.pi) ∩ H =
      Ioo (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)) := by
    ext t
    constructor
    · intro ht
      exact (cap_local_circle_ball_iff s q t hq hq1 ht.1).mp ht.2
    · intro ht
      have he := cap_arcsin_bounds q hq hq1
      have ht0 : t∈Icc (s-Real.pi) (s+Real.pi) :=
        ⟨by linarith [ht.1,he.2.2.1,Real.pi_pos],by linarith [ht.2,he.2.2.1,Real.pi_pos]⟩
      exact ⟨ht0,(cap_local_circle_ball_iff s q t hq hq1 ht0).mpr ht⟩
  have hperiod := hFp.intervalIntegral_add_eq 0 (s-Real.pi)
  have hshift : s-Real.pi+2*Real.pi=s+Real.pi := by ring
  have hsle : s-Real.pi ≤ s+Real.pi := by linarith [Real.pi_pos]
  rw [zero_add,hshift,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi),
    intervalIntegral.integral_of_le hsle,
    ← integral_Icc_eq_integral_Ioc,← integral_Icc_eq_integral_Ioc] at hperiod
  calc
    _ = ∫ t in Icc 0 (2*Real.pi), F t := (setIntegral_indicator hHm).symm
    _ = ∫ t in Icc (s-Real.pi) (s+Real.pi), F t := hperiod
    _ = ∫ t in Ioo (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), f t := by
      rw [show F=H.indicator f by rfl,setIntegral_indicator hHm,hset]
    _ = _ := setIntegral_congr_set Ioo_ae_eq_Icc

theorem cap_true_boundary_integrable (s q : ℝ) (B : ℝ→E2) (hB : Continuous B)
    (psi : E2→ℝ) (hpsi : ContDiff ℝ ∞ psi) (i j : Fin 2) :
    IntegrableOn (fun t => B t i * psi (unitCircleParameter t) * unitCircleParameter t j)
      (circlePatch (unitCircleParameter s) q) := by
  have hc : Continuous (fun t => B t i * psi (unitCircleParameter t) * unitCircleParameter t j) :=
    (((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp hB).mul (hpsi.continuous.comp circle_contDiff.continuous)).mul
      ((EuclideanSpace.proj (𝕜:=ℝ) j).continuous.comp circle_contDiff.continuous)
  exact hc.integrableOn_Icc.mono_set inter_subset_left

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
