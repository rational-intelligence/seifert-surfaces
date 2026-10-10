import InitialPeriodicTraceConstancy_v460
import InitialPeriodicTangential_v411
import InitialPrimitiveGreen_v411

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 600000
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_periodic_L2" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPeriodicTangential_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.periodic_tangent_all_intervals_v411)⟩

local macro "paid_circle_primitive" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialTangentialPrimitive_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.circle_tangent_primitive_v411)⟩

local macro "paid_primitive_green" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPrimitiveGreen_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L2_primitive_green_identity_v411)⟩

private theorem periodic_zero_mean_L2_primitive_v460
    (a : ℝ → E2) (period : Periodic a (2*Real.pi))
    (hL2 : MemLp a 2 (volume.restrict (Ioo (-Real.pi) Real.pi)))
    (hmean : (∫ t in Ioo (-Real.pi) Real.pi,a t)=0) :
    let c : ℝ → E2 := fun t=>∫ u in (-Real.pi)..t,a u
    Continuous c ∧ Periodic c (2*Real.pi) ∧ c (-Real.pi)=0 ∧ c Real.pi=0 ∧
    (∀ i : Fin 2,AbsolutelyContinuousOnInterval (fun t=>c t i) (-Real.pi) Real.pi) ∧
    (∀ᵐ t ∂volume.restrict (Icc (-Real.pi) Real.pi),HasDerivAt c (a t) t) ∧
    MemLp (deriv c) 2 (volume.restrict (Icc (-Real.pi) Real.pi)) ∧
    (∫ t in Icc (-Real.pi) Real.pi,‖deriv c t‖^2)=∫ t in Ioo (-Real.pi) Real.pi,‖a t‖^2 ∧
    (∀ psi:ℝ→ℝ,ContDiff ℝ ∞ psi → ∀ i:Fin 2,
      (∫ t in Icc (-Real.pi) Real.pi,a t i*psi t+c t i*deriv psi t)=0) := by
  classical
  dsimp only
  let c : ℝ → E2 := fun t=>∫ u in (-Real.pi)..t,a u
  have hperiods := paid_periodic_L2 a period hL2
  have hInt (u v:ℝ) : IntervalIntegrable a volume u v := by
    let : IsFiniteMeasure (volume.restrict (Icc (min u v) (max u v))) :=
      isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
    have hi : IntegrableOn a (uIcc u v) := (hperiods.1 (min u v) (max u v)).integrable (by norm_num)
    exact intervalIntegrable_iff.mpr (hi.mono_set uIoc_subset_uIcc)
  have hc : Continuous c := intervalIntegral.continuous_primitive hInt (-Real.pi)
  have hprimitive := paid_circle_primitive a (0:E2) (0:E2) hL2 (by simpa using hmean)
  dsimp only at hprimitive
  simp only [zero_add] at hprimitive
  have hp : Periodic c (2*Real.pi) := by
    intro t
    change (∫ u in (-Real.pi)..(t+2*Real.pi),a u)=∫ u in (-Real.pi)..t,a u
    have hperiodIntegral : (∫ u in t..(t+2*Real.pi),a u)=0 := by
      have he := period.intervalIntegral_add_eq t (-Real.pi)
      rw [show -Real.pi+2*Real.pi=Real.pi by ring,
        intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
        integral_Ioc_eq_integral_Ioo,hmean] at he
      exact he
    rw [←intervalIntegral.integral_add_adjacent_intervals (hInt (-Real.pi) t) (hInt t (t+2*Real.pi)),
      hperiodIntegral,add_zero]
  have haCC : MemLp a 2 (volume.restrict (Icc (-Real.pi) Real.pi)) := by
    rwa [←restrict_Ioo_eq_restrict_Icc]
  have hgreen := paid_primitive_green a (0:E2) (-Real.pi) Real.pi
    (by linarith [Real.pi_pos]) haCC
  dsimp only at hgreen
  simp only [zero_add] at hgreen
  have hder : ∀ᵐ t ∂volume.restrict (Icc (-Real.pi) Real.pi),HasDerivAt c (a t) t := by
    exact ae_restrict_congr_set Ioo_ae_eq_Icc |>.mp hprimitive.2.2.2.1
  have hcd : MemLp (deriv c) 2 (volume.restrict (Icc (-Real.pi) Real.pi)) := by
    rw [←restrict_Ioo_eq_restrict_Icc]
    exact hprimitive.2.2.2.2.1
  refine ⟨hc,hp,hprimitive.2.1,hprimitive.2.2.1,hgreen.1,hder,hcd,?_,?_⟩
  · rw [integral_Icc_eq_integral_Ioo]
    exact hprimitive.2.2.2.2.2
  · intro psi hpsi i
    have hg := hgreen.2 psi hpsi i
    rw [hprimitive.2.2.1,hprimitive.2.1] at hg
    simpa only [PiLp.zero_apply,zero_mul,sub_zero] using hg

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
