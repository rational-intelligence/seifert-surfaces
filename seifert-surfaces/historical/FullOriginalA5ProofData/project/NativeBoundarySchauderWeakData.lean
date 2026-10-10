import NativeBoundarySchauderWeakTransport

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak

theorem native_h1_of_memW1pWitness
    (U : Set E2) (v : E2 → ℝ) (hV : DeGiorgi.MemW1pWitness 2 v U) :
    H1On U v hV.weakGrad := by
  refine ⟨⟨?_, ?_, ?_⟩, hV.memLp, hV.weakGrad_memLp⟩
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict
      (hV.memLp.locallyIntegrable (by norm_num))
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict
      (hV.weakGrad_memLp.locallyIntegrable (by norm_num))
  · intro ψ hs hc ht i
    exact hV.isWeakGrad i ψ hs hc ht

theorem native_zero_source_linear_to_weak_divergence
    (U : Set E2) (hU : MeasurableSet U) (C : LinearizedCoefficients)
    (a : E2 → Matrix (Fin 2) (Fin 2) ℝ) (v : E2 → ℝ)
    (hV : DeGiorgi.MemW1pWitness 2 v U)
    (hc : C.c = 0) (hb : C.b = 0) (hq : C.q = 0) (hf : C.f = 0)
    (ha : EqOn (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (a x)) C.a U)
    (hdLp : MemLp C.d 2 (volume.restrict U))
    (hweak : LinearWeakEquation U C v hV.weakGrad) :
    WeakDivergenceWithData U a (fun x => -C.d x) (fun _ => 0) v hV.weakGrad := by
  refine ⟨native_h1_of_memW1pWitness U v hV, ?_⟩
  intro ψ hs hψc ht
  obtain ⟨hiFlux, _, hzero⟩ := hweak ψ hs hψc ht
  have hsrc (x : E2) : linearizedSource C v hV.weakGrad x = 0 := by
    simp [linearizedSource, hb, hq, hf]
  have hflux (x : E2) (hx : x ∈ U) :
      linearizedFlux C v hV.weakGrad x = matrixAction (a x) (hV.weakGrad x) + C.d x := by
    simp only [linearizedFlux, hc, Pi.zero_apply, smul_zero, add_zero,
      native_matrixAction_eq_toEuclideanCLM, ha hx]
  have hGcompact : HasCompactSupport (planarGradient ψ) := by
    apply hψc.mono'
    intro x hx
    by_contra hn
    exact hx (planarGradient_eq_zero_off_support ψ hn)
  have htest : MemLp (planarGradient ψ) 2 (volume.restrict U) :=
    ((continuous_planarGradient hs).memLp_of_hasCompactSupport hGcompact).restrict U
  have hdInt : IntegrableOn (fun x => inner ℝ (C.d x) (planarGradient ψ x)) U := by
    apply (L2.integrable_inner (𝕜 := ℝ) (hdLp.toLp C.d)
      (htest.toLp (planarGradient ψ))).congr
    filter_upwards [hdLp.coeFn_toLp, htest.coeFn_toLp] with x hx hy
    rw [hx, hy]
  have hiA : IntegrableOn (fun x => inner ℝ (matrixAction (a x) (hV.weakGrad x))
      (planarGradient ψ x)) U := by
    apply (hiFlux.sub hdInt).congr
    filter_upwards [ae_restrict_mem hU] with x hx
    simp only [Pi.sub_apply, hflux x hx, inner_add_left, add_sub_cancel_right]
  have hie : IntegrableOn (fun x => inner ℝ (-C.d x) (planarGradient ψ x) + 0 * ψ x) U := by
    apply hdInt.neg.congr
    exact Eventually.of_forall fun x => by simp only [Pi.neg_apply, inner_neg_left, zero_mul, add_zero]
  refine ⟨hiA, hie, ?_⟩
  simp only [hsrc, zero_mul, sub_zero] at hzero
  have hexp : (∫ x in U, inner ℝ (linearizedFlux C v hV.weakGrad x) (planarGradient ψ x)) =
      (∫ x in U, inner ℝ (matrixAction (a x) (hV.weakGrad x)) (planarGradient ψ x)) +
        ∫ x in U, inner ℝ (C.d x) (planarGradient ψ x) := by
    rw [← integral_add hiA hdInt]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU] with x hx
    simp only [Pi.add_apply, hflux x hx, inner_add_left]
  rw [hexp] at hzero
  simp only [zero_mul, add_zero, inner_neg_left, integral_neg]
  linarith

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
