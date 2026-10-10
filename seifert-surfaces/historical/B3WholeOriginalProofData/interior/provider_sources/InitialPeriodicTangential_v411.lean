import InitialTangentialPrimitive_v411
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

private theorem periodic_tangent_all_intervals_v411
    (a : ℝ → E2) (period : Periodic a (2 * Real.pi))
    (hL2 : MemLp a 2 (volume.restrict (Ioo (-Real.pi) Real.pi))) :
    (∀ u v : ℝ, MemLp a 2 (volume.restrict (Icc u v))) ∧
      (∀ u : ℝ, (∫ t in Icc u (u + 2 * Real.pi), a t) =
        ∫ t in Ioo (-Real.pi) Real.pi, a t) ∧
      (∀ u : ℝ, (∫ t in Icc u (u + 2 * Real.pi), ‖a t‖ ^ 2) =
        ∫ t in Ioo (-Real.pi) Real.pi, ‖a t‖ ^ 2) := by
  let : IsFiniteMeasure (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top).ne
  have hbase : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have habase : IntegrableOn a (Icc (-Real.pi) Real.pi) := by
    have hi : IntegrableOn a (Ioo (-Real.pi) Real.pi) := hL2.integrable (by norm_num)
    exact hi.congr_set_ae Ioo_ae_eq_Icc.symm
  have hqbase : IntegrableOn (fun t => ‖a t‖ ^ 2) (Icc (-Real.pi) Real.pi) := by
    have hi : IntegrableOn (fun t => ‖a t‖ ^ 2) (Ioo (-Real.pi) Real.pi) := hL2.norm.integrable_sq
    exact hi.congr_set_ae Ioo_ae_eq_Icc.symm
  have haperiod : IntervalIntegrable a volume (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hbase]
    exact habase.mono_set Ioc_subset_Icc_self
  have hqperiod : IntervalIntegrable (fun t => ‖a t‖ ^ 2) volume
      (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hbase]
    exact hqbase.mono_set Ioc_subset_Icc_self
  have hpq : Periodic (fun t => ‖a t‖ ^ 2) (2 * Real.pi) :=
    fun t => congrArg (fun v : E2 => ‖v‖ ^ 2) (period t)
  have hall (u v : ℝ) : MemLp a 2 (volume.restrict (Icc u v)) := by
    have hi0 := period.intervalIntegrable (by positivity : 2 * Real.pi ≠ 0) haperiod u v
    have hi1 := hpq.intervalIntegrable (by positivity : 2 * Real.pi ≠ 0) hqperiod u v
    have hi : IntegrableOn a (Icc u v) := hi0.left.congr_set_ae Ioc_ae_eq_Icc.symm
    have hqi : IntegrableOn (fun t => ‖a t‖ ^ 2) (Icc u v) :=
      hi1.left.congr_set_ae Ioc_ae_eq_Icc.symm
    exact (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr hqi
  refine ⟨hall, ?_, ?_⟩
  · intro u
    have he := period.intervalIntegral_add_eq u (-Real.pi)
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : u ≤ u + 2 * Real.pi),
      intervalIntegral.integral_of_le hbase] at he
    simp only [integral_Ioc_eq_integral_Ioo] at he
    rw [integral_Icc_eq_integral_Ioo]
    exact he
  · intro u
    have he := hpq.intervalIntegral_add_eq u (-Real.pi)
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : u ≤ u + 2 * Real.pi),
      intervalIntegral.integral_of_le hbase] at he
    simp only [integral_Ioc_eq_integral_Ioo] at he
    rw [integral_Icc_eq_integral_Ioo]
    exact he

private theorem actual_circle_tangential_period_v411
    (d : Fin 2 → E2 → E2) (x : E2) (q : ℝ) :
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    Periodic (fun t =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun i => q * inner ℝ (d i (x + q • unitCircleParameter t))
          (J (unitCircleParameter t)))) (2 * Real.pi) := by
  dsimp only
  intro t
  dsimp only
  have hc : unitCircleParameter (t + 2 * Real.pi) = unitCircleParameter t := by
    ext i
    fin_cases i <;> simp [unitCircleParameter, Real.cos_add_two_pi, Real.sin_add_two_pi]
  rw [hc]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
