import NativeBoundarySchauderOriginalInputs
import NativeA5CoefficientExtensionV471

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_bounded_holderWith_lower_exponent
    {F : Type*} [NormedAddCommGroup F]
    (f : E2 → F) (C α β : ℝ≥0) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖f x‖ ≤ B) (hholder : HolderWith C α f) (hβα : β ≤ α) :
    HolderWith (max (Real.toNNReal (2 * B)) C) β f := by
  have hzero : HolderWith (Real.toNNReal (2 * B)) 0 f := by
    intro x y
    simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
    rw [edist_dist, ENNReal.ofReal_le_coe, Real.coe_toNNReal _ (by positivity)]
    change dist (f x) (f y) ≤ 2 * B
    calc
      _ ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * B := by linarith [hbound x, hbound y]
  exact hzero.of_le_of_le hholder zero_le hβα

theorem native_zero_source_weak_divergence_coefficient_congr
    (U : Set E2) (hU : MeasurableSet U)
    (a A : E2 → Matrix (Fin 2) (Fin 2) ℝ) (e E : E2 → E2)
    (v : E2 → ℝ) (G : E2 → E2)
    (ha : EqOn A a U) (he : EqOn E e U)
    (hw : SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.WeakDivergenceWithData
      U a e (fun _ => 0) v G) :
    SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.WeakDivergenceWithData
      U A E (fun _ => 0) v G := by
  refine ⟨hw.1, ?_⟩
  intro ψ hs hc ht
  obtain ⟨hia, hie, hEq⟩ := hw.2 ψ hs hc ht
  have hleft : (fun x => inner ℝ
      (SeifertSurfaces.OriginalEndpoints.B1Tangency.matrixAction (a x) (G x)) (planarGradient ψ x)) =ᵐ[volume.restrict U]
      (fun x => inner ℝ
        (SeifertSurfaces.OriginalEndpoints.B1Tangency.matrixAction (A x) (G x)) (planarGradient ψ x)) := by
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [ha hx]
  have hright : (fun x => inner ℝ (e x) (planarGradient ψ x) + 0 * ψ x) =ᵐ[volume.restrict U]
      (fun x => inner ℝ (E x) (planarGradient ψ x) + 0 * ψ x) := by
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [he hx]
  exact ⟨hia.congr hleft, hie.congr hright,
    (integral_congr_ae hleft).symm.trans (hEq.trans (integral_congr_ae hright))⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
