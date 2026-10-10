import InitialActualArcPath_v411
import Mathlib.Analysis.Fourier.AddCircle

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

/- Fourier completeness identifies an actual L2 residual, with no regularity
premise on that residual. This will be applied after the original weighted
Green equations show that its nonconstant coefficients vanish. -/
private theorem circle_L2_nonconstant_coefficients_vanish_v445
    {T : ℝ} [Fact (0 < T)] (u : AddCircle T → ℂ)
    (hu : MemLp u 2 AddCircle.haarAddCircle)
    (hcoeff : ∀ n : ℤ, n ≠ 0 → fourierCoeff u n = 0) :
    u =ᵐ[AddCircle.haarAddCircle] fun _ => fourierCoeff u 0 := by
  classical
  let U : Lp ℂ 2 AddCircle.haarAddCircle := hu.toLp u
  let m : ℂ := fourierCoeff u 0
  let V : Lp ℂ 2 AddCircle.haarAddCircle := m • fourierBasis (T := T) 0
  have hU : U =ᵐ[AddCircle.haarAddCircle] u := hu.coeFn_toLp
  have hrepr : fourierBasis.repr U = fourierBasis.repr V := by
    ext n
    rw [fourierBasis_repr]
    rw [fourierCoeff_congr_ae hU]
    simp only [V, map_smul, HilbertBasis.repr_self]
    by_cases hn : n = 0
    · subst n
      simp [m]
    · simp [hn, hcoeff n hn]
  have hUV : U = V := fourierBasis.repr.injective hrepr
  have hV : V =ᵐ[AddCircle.haarAddCircle] fun _ => m := by
    have hf : (fourierBasis (T := T) 0 : AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle]
        fourier 0 := by
      simpa only [coe_fourierBasis] using coeFn_fourierLp (T := T) 2 0
    filter_upwards [Lp.coeFn_smul m (fourierBasis (T := T) 0),
      hf] with t ht hfourier
    change V t = m * (fourierBasis (T := T) 0 : AddCircle T → ℂ) t at ht
    rw [hfourier, fourier_zero, mul_one] at ht
    exact ht
  exact hU.symm.trans (hUV ▸ hV)

private theorem interval_L2_nonconstant_coefficients_vanish_v445
    (a T : ℝ) (hT : 0 < T) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc a (a + T))))
    (hcoeff : ∀ n : ℤ, n ≠ 0 →
      fourierCoeffOn (lt_add_of_pos_right a hT) u n = 0) :
    u =ᵐ[volume.restrict (Ioc a (a + T))]
      fun _ => fourierCoeffOn (lt_add_of_pos_right a hT) u 0 := by
  let : Fact (0 < T) := ⟨hT⟩
  let U : AddCircle T → ℂ := AddCircle.liftIoc T a u
  have hU : MemLp U 2 AddCircle.haarAddCircle := hu.memLp_liftIoc.haarAddCircle
  have hcoefU : ∀ n : ℤ, n ≠ 0 → fourierCoeff U n = 0 := by
    intro n hn
    simpa only [U, fourierCoeff_liftIoc_eq] using hcoeff n hn
  have hAE := circle_L2_nonconstant_coefficients_vanish_v445 U hU hcoefU
  have hAEvol : U =ᵐ[volume] fun _ => fourierCoeff U 0 := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hT).ne').mpr hAE
  have hreal : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioc a (a + T)),
      U (t : AddCircle T) = fourierCoeff U 0 :=
    (AddCircle.measurePreserving_mk T a).quasiMeasurePreserving.ae hAEvol
  filter_upwards [hreal, ae_restrict_mem measurableSet_Ioc] with t ht hmem
  simpa only [U, AddCircle.liftIoc_coe_apply hmem, fourierCoeff_liftIoc_eq] using ht

private theorem interval_L2_supported_residual_zero_v445
    (a T : ℝ) (hT : 0 < T) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc a (a + T))))
    (hcoeff : ∀ n : ℤ, n ≠ 0 →
      fourierCoeffOn (lt_add_of_pos_right a hT) u n = 0)
    (S : Set ℝ) (hS : volume S ≠ 0) (hsub : S ⊆ Ioc a (a + T))
    (hzero : ∀ t ∈ S, u t = 0) :
    u =ᵐ[volume.restrict (Ioc a (a + T))] (fun _ => (0 : ℂ)) := by
  have hconst := interval_L2_nonconstant_coefficients_vanish_v445 a T hT u hu hcoeff
  have hconstS : ∀ᵐ t ∂volume.restrict S,
      u t = fourierCoeffOn (lt_add_of_pos_right a hT) u 0 :=
    ae_restrict_of_ae_restrict_of_subset hsub hconst
  obtain ⟨t, htS, ht⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hS hconstS
  have hm : fourierCoeffOn (lt_add_of_pos_right a hT) u 0 = 0 :=
    ht.symm.trans (hzero t htS)
  filter_upwards [hconst] with t ht
  exact hm ▸ ht

private theorem original_vector_residual_zero_from_fourier_v445
    (a T : ℝ) (hT : 0 < T) (u : ℝ → E2)
    (hu : ∀ i : Fin 2, MemLp (fun t => (u t i : ℂ)) 2
      (volume.restrict (Ioc a (a + T))))
    (hcoeff : ∀ i : Fin 2, ∀ n : ℤ, n ≠ 0 →
      fourierCoeffOn (lt_add_of_pos_right a hT)
        (fun t => (u t i : ℂ)) n = 0)
    (S : Set ℝ) (hS : volume S ≠ 0) (hsub : S ⊆ Ioc a (a + T))
    (hzero : ∀ t ∈ S, u t = 0) :
    ∀ᵐ t ∂volume.restrict (Ioc a (a + T)), u t = 0 := by
  have hall : ∀ᵐ t ∂volume.restrict (Ioc a (a + T)), ∀ i : Fin 2, u t i = 0 := by
    apply ae_all_iff.mpr
    intro i
    have hz := interval_L2_supported_residual_zero_v445 a T hT
      (fun t => (u t i : ℂ)) (hu i) (hcoeff i) S hS hsub
      (fun t ht => congrArg (fun v : E2 => (v i : ℂ)) (hzero t ht))
    filter_upwards [hz] with t ht
    exact Complex.ofReal_injective ht
  filter_upwards [hall] with t ht
  ext i
  exact ht i

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
