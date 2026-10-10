import InitialArcPrimitive_v411
import InitialFourierMoments_v445

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

private theorem interval_continuous_mul_integrable_v445
    (u v : ℝ) (f g : ℝ → ℝ) (hf : IntegrableOn f (Icc u v))
    (hg : Continuous g) : IntegrableOn (fun t => f t * g t) (Icc u v) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  apply hf.mul_bdd hg.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hK t ht

/- Subtracting the two actual one-dimensional Green identities cancels the
tangential derivative and leaves the residual trace paired with the derivative
of the test. All interval restrictions and integrability are explicit. -/
private theorem actual_arc_residual_pairing_v445
    (u v : ℝ) (_huv : u ≤ v) (hvp : v ≤ u + 2 * Real.pi)
    (F a c : ℝ → ℝ)
    (hF : IntegrableOn F (Icc u (u + 2 * Real.pi)))
    (ha : IntegrableOn a (Icc u (u + 2 * Real.pi)))
    (hc : ContinuousOn c (Icc u v))
    (aoutside : ∀ t ∈ Icc v (u + 2 * Real.pi), a t = 0)
    (psi : ℝ → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (original_green :
      (∫ t in Icc u (u + 2 * Real.pi), a t * psi t + F t * deriv psi t) =
        c v * psi v - c u * psi u)
    (primitive_green :
      (∫ t in Icc u v, a t * psi t + c t * deriv psi t) =
        c v * psi v - c u * psi u) :
    (∫ t in Icc u (u + 2 * Real.pi),
      (F t - (Icc u v).indicator c t) * deriv psi t) = 0 := by
  classical
  let W := Icc u (u + 2 * Real.pi)
  let V := Icc u v
  have hVW : V ⊆ W := fun t ht => ⟨ht.1, ht.2.trans hvp⟩
  have hdpsi : Continuous (deriv psi) := hpsi.continuous_deriv (by simp)
  have haP : IntegrableOn (fun t => a t * psi t) W :=
    interval_continuous_mul_integrable_v445 _ _ _ _ ha hpsi.continuous
  have hfD : IntegrableOn (fun t => F t * deriv psi t) W :=
    interval_continuous_mul_integrable_v445 _ _ _ _ hF hdpsi
  have hcD : IntegrableOn (fun t => c t * deriv psi t) V :=
    ContinuousOn.integrableOn_compact isCompact_Icc (hc.mul hdpsi.continuousOn)
  have hcInd : Integrable ((Icc u v).indicator (fun t => c t * deriv psi t)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hcD
  have hciD : IntegrableOn (fun t => (Icc u v).indicator c t * deriv psi t) W := by
    apply hcInd.integrableOn.congr_fun _ measurableSet_Icc
    intro t ht
    by_cases hv : t ∈ Icc u v <;> simp [hv]
  have hAeq : (∫ t in W, a t * psi t) = ∫ t in V, a t * psi t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hVW
    intro t ht
    have hv : v < t := by
      by_contra h
      exact ht.2 ⟨ht.1.1, le_of_not_gt h⟩
    rw [aoutside t ⟨hv.le, ht.1.2⟩, zero_mul]
  have hCeq : (∫ t in W, (Icc u v).indicator c t * deriv psi t) =
      ∫ t in V, c t * deriv psi t := by
    have he : (fun t => (Icc u v).indicator c t * deriv psi t) =
        (Icc u v).indicator (fun t => c t * deriv psi t) := by
      funext t
      by_cases hv : t ∈ Icc u v <;> simp [hv]
    rw [he, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    have hinter : V ∩ W = V := inter_eq_left.mpr hVW
    exact congrArg (fun S : Set ℝ => ∫ t in S, c t * deriv psi t) hinter
  have hAonV := haP.mono_set hVW
  rw [integral_add haP hfD, hAeq] at original_green
  rw [integral_add hAonV hcD] at primitive_green
  have hsplit : (fun t => (F t - (Icc u v).indicator c t) * deriv psi t) =
      (fun t => F t * deriv psi t - (Icc u v).indicator c t * deriv psi t) := by
    funext t
    ring
  rw [hsplit, integral_sub hfD hciD, hCeq]
  linarith [original_green, primitive_green]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
