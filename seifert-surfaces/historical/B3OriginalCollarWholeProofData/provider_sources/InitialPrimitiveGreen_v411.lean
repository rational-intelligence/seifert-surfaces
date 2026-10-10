import InitialTangentialPrimitive_v411
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

/- The literal L2 tangential primitive has the full Green identity, not
merely an almost-everywhere derivative and endpoint equation. -/
private theorem L2_primitive_green_identity_v411
    (a : ℝ → E2) (b0 : E2) (u v : ℝ) (huv : u ≤ v)
    (hL2 : MemLp a 2 (volume.restrict (Icc u v))) :
    let c : ℝ → E2 := fun t => b0 + ∫ x in u..t, a x
    (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) u v) ∧
      (∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi → ∀ i : Fin 2,
        (∫ t in Icc u v, a t i * psi t + c t i * deriv psi t) =
          c v i * psi v - c u i * psi u) := by
  classical
  dsimp only
  let c : ℝ → E2 := fun t => b0 + ∫ x in u..t, a x
  let : IsFiniteMeasure (volume.restrict (Icc u v)) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have hi : IntegrableOn a (Icc u v) := hL2.integrable (by norm_num)
  have hvI : IntervalIntegrable a volume u v := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le huv]
    exact hi.mono_set Ioc_subset_Icc_self
  have hInterval (t : ℝ) (ht : t ∈ Icc u v) : IntervalIntegrable a volume u t := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le ht.1]
    exact hi.mono_set (fun x hx => ⟨hx.1.le, hx.2.trans ht.2⟩)
  have hcAC (i : Fin 2) : AbsolutelyContinuousOnInterval (fun t => c t i) u v := by
    let ai : ℝ → ℝ := fun t => a t i
    have hai : IntervalIntegrable ai volume u v :=
      ⟨(EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hvI.1,
        (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hvI.2⟩
    have hp := hai.absolutelyContinuousOnInterval_intervalIntegral (c := u) (by simp)
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => b0 i) u v :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => b0 i)).contDiffOn.absolutelyContinuousOnInterval
    apply (hconst.add hp).congr
    intro t ht
    have ht' : t ∈ Icc u v := by simpa only [uIcc_of_le huv] using ht
    have hproj := (EuclideanSpace.proj (𝕜 := ℝ) i).intervalIntegral_comp_comm (hInterval t ht')
    change (∫ x in u..t, a x i) = (∫ x in u..t, a x) i at hproj
    change b0 i + (∫ x in u..t, a x i) = (b0 + ∫ x in u..t, a x) i
    rw [hproj]
    rfl
  refine ⟨hcAC, ?_⟩
  intro psi hpsi i
  have hpsiAC : AbsolutelyContinuousOnInterval psi u v :=
    (hpsi.of_le (by simp) : ContDiff ℝ 1 psi).contDiffOn.absolutelyContinuousOnInterval
  have hgreen := (hcAC i).integral_deriv_mul_eq_sub hpsiAC
  rw [intervalIntegral.integral_of_le huv, ← integral_Icc_eq_integral_Ioc] at hgreen
  rw [← hgreen]
  apply integral_congr_ae
  have hraw := hvI.ae_hasDerivAt_integral
  have hraw' := hraw.filter_mono (ae_restrict_le (μ := volume) (s := Icc u v))
  filter_upwards [hraw', ae_restrict_mem measurableSet_Icc] with t ht htm
  have hp := ht (by rwa [uIcc_of_le huv]) u (by simp)
  have hvec : HasDerivAt c (a t) t := hp.const_add b0
  have hscalar := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t hvec
  change HasDerivAt (fun t => c t i) (a t i) t at hscalar
  rw [hscalar.deriv]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
