import NativeACZeroExtension

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem translate_restrict_interval (a b d : ℝ) :
    MeasurePreserving (fun t : ℝ => d + t) (volume.restrict (Icc a b))
      (volume.restrict (Icc (d + a) (d + b))) := by
  have hp : (fun t : ℝ => d + t) ⁻¹' Icc (d + a) (d + b) = Icc a b := by
    ext t
    simp
  have hm := (measurePreserving_add_left volume d).restrict_preimage
    (s := Icc (d + a) (d + b)) measurableSet_Icc
  rw [hp] at hm
  exact hm

theorem integral_Icc_translate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b d : ℝ) (f : ℝ → F) :
    (∫ t in Icc a b, f (d + t)) = ∫ t in Icc (d + a) (d + b), f t :=
  (translate_restrict_interval a b d).integral_comp'
    (f := MeasurableEquiv.addLeft d) f

theorem ac_translate (a b d : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f (d + a) (d + b)) :
    AbsolutelyContinuousOnInterval (fun t => f (d + t)) a b := by
  have hfi : IntervalIntegrable (fun t => deriv f (d + t)) volume a b := by
    simpa only [add_sub_cancel_left] using hf.intervalIntegrable_deriv.comp_add_left d
  have hac := hfi.absolutelyContinuousOnInterval_intervalIntegral
    (show a ∈ uIcc a b by simp [hab])
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => f (d + a)) a b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => f (d + a))).contDiffOn.absolutelyContinuousOnInterval
  apply (hc.add hac).congr
  intro t ht
  have htt : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  have hsub := hf.mono (show uIcc (d + a) (d + t) ⊆ uIcc (d + a) (d + b) by
    rw [uIcc_of_le (by linarith [htt.1]), uIcc_of_le (by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith [htt.2]))
  have he := hsub.integral_deriv_eq_sub
  dsimp only [Pi.add_apply]
  rw [intervalIntegral.integral_comp_add_left, he]
  ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
