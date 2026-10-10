import NativeBoundaryFirstOrderSchauderData
import NativeBoundaryTangentialQuotientHolder

set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- Boundary coefficient values use the actual within gradient; on the open
positive cap this is exactly the previously proved classical quotient data. -/
def nativeClosedLinearDifferenceCoefficients (K : Set E2)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (h : ℝ) : LinearizedCoefficients where
  a x := C.a (shift 1 h x)
  c := 0
  d x := h⁻¹ • (C.d (shift 1 h x) - C.d x) +
    (h⁻¹ • (C.a (shift 1 h x) - C.a x)) (planarGradientWithin v K x)
  b := 0
  q := 0
  f := 0

theorem native_holder_planarGradientWithin
    (K : Set E2) (v : E2 → ℝ) (α : ℝ≥0)
    (hH : ∃ C, HolderOnWith C α (fderivWithin ℝ v K) K) :
    ∃ C, HolderOnWith C α (planarGradientWithin v K) K := by
  obtain ⟨A, hA⟩ := native_holder_derivative_apply_const K v α hH (coordinateVector 2 0)
  obtain ⟨B, hB⟩ := native_holder_derivative_apply_const K v α hH (coordinateVector 2 1)
  obtain ⟨C, hC⟩ := native_holder_smul_const K _ A α hA (coordinateVector 2 0)
  obtain ⟨D, hD⟩ := native_holder_smul_const K _ B α hB (coordinateVector 2 1)
  have hh := native_holder_add K _ _ C D α hC hD
  refine ⟨C + D, ?_⟩
  change HolderOnWith (C + D) α
    (fun x => ∑ i : Fin 2, fderivWithin ℝ v K x (coordinateVector 2 i) • coordinateVector 2 i) K
  simpa only [Fin.sum_univ_two] using hh

theorem native_closed_linear_difference_weak_equation
    (Ω B K : Set E2) (hΩ : IsOpen Ω) (hB : IsOpen B) (hsub : B ⊆ Ω)
    (hBK : ∀ x ∈ B, K ∈ 𝓝 x)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (hv : ContDiffOn ℝ 1 v Ω)
    (hc : C.c = 0) (hb : C.b = 0) (hq : C.q = 0) (hf : C.f = 0)
    (hw : LinearWeakEquation Ω C v (planarGradient v))
    (h : ℝ) (hne : h ≠ 0) (hshift : MapsTo (shift 1 h) B Ω) :
    LinearWeakEquation B (nativeClosedLinearDifferenceCoefficients K C v h)
      (differenceQuotient v 1 h) (planarGradient (differenceQuotient v 1 h)) := by
  have hweak := native_linear_difference_weak_equation Ω B hΩ hB hsub C v hv
    hc hb hq hf hw 1 h hne hshift
  have hg (x : E2) (hx : x ∈ B) : planarGradientWithin v K x = planarGradient v x := by
    unfold planarGradientWithin planarGradient
    rw [fderivWithin_of_mem_nhds (hBK x hx)]
  intro φ hs hcompact ht
  obtain ⟨hi, _, hz⟩ := hweak φ hs hcompact ht
  have hflux (x : E2) (hx : x ∈ B) :
      linearizedFlux (nativeClosedLinearDifferenceCoefficients K C v h)
        (differenceQuotient v 1 h) (planarGradient (differenceQuotient v 1 h)) x =
      linearizedFlux (nativeLinearDifferenceCoefficients C v 1 h)
        (differenceQuotient v 1 h) (planarGradient (differenceQuotient v 1 h)) x := by
    simp only [linearizedFlux, nativeClosedLinearDifferenceCoefficients, nativeLinearDifferenceCoefficients, hg x hx]
  have hsrc (x : E2) : linearizedSource (nativeClosedLinearDifferenceCoefficients K C v h)
      (differenceQuotient v 1 h) (planarGradient (differenceQuotient v 1 h)) x = 0 := by
    simp [linearizedSource, nativeClosedLinearDifferenceCoefficients]
  have hsrcOld (x : E2) : linearizedSource (nativeLinearDifferenceCoefficients C v 1 h)
      (differenceQuotient v 1 h) (planarGradient (differenceQuotient v 1 h)) x = 0 := by
    simp [linearizedSource, nativeLinearDifferenceCoefficients]
  have hEq : (fun x => inner ℝ
      (linearizedFlux (nativeClosedLinearDifferenceCoefficients K C v h)
        (differenceQuotient v 1 h) (planarGradient (differenceQuotient v 1 h)) x)
      (planarGradient φ x)) =ᵐ[volume.restrict B]
      (fun x => inner ℝ
        (linearizedFlux (nativeLinearDifferenceCoefficients C v 1 h)
          (differenceQuotient v 1 h) (planarGradient (differenceQuotient v 1 h)) x)
        (planarGradient φ x)) := by
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    rw [hflux x hx]
  refine ⟨hi.congr hEq.symm, by simp only [hsrc, zero_mul]; exact integrable_zero _ _ _, ?_⟩
  simp only [hsrcOld, zero_mul, sub_zero] at hz
  simp only [hsrc, zero_mul, sub_zero]
  rwa [integral_congr_ae hEq]

/-- One forcing bound and Hölder constant serve every small nonzero tangent
step. This supplies the uniform estimate needed by the weak limit argument. -/
theorem native_closed_linear_difference_forcing_uniform_holder
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (α : ℝ≥0) (hα : 0 < α)
    (ha : ContDiffOn ℝ 1 C.a (nativeClosedBoundaryCap c (2 * r)))
    (hd : ContDiffOn ℝ 1 C.d (nativeClosedBoundaryCap c (2 * r)))
    (hDa : ∃ A, HolderOnWith A α (fderivWithin ℝ C.a (nativeClosedBoundaryCap c (2 * r)))
      (nativeClosedBoundaryCap c (2 * r)))
    (hDd : ∃ A, HolderOnWith A α (fderivWithin ℝ C.d (nativeClosedBoundaryCap c (2 * r)))
      (nativeClosedBoundaryCap c (2 * r)))
    (hDv : ∃ A, HolderOnWith A α (fderivWithin ℝ v (nativeClosedBoundaryCap c (2 * r)))
      (nativeClosedBoundaryCap c (2 * r))) :
    ∃ M : ℝ, ∃ H : ℝ≥0, 0 ≤ M ∧ ∀ h : ℝ, h ≠ 0 → |h| < r →
      (∀ x ∈ nativeClosedBoundaryCap c r,
        ‖(nativeClosedLinearDifferenceCoefficients (nativeClosedBoundaryCap c (2 * r)) C v h).d x‖ ≤ M) ∧
      HolderOnWith H α
        (nativeClosedLinearDifferenceCoefficients (nativeClosedBoundaryCap c (2 * r)) C v h).d
        (nativeClosedBoundaryCap c r) := by
  let K := nativeClosedBoundaryCap c (2 * r)
  let V := nativeClosedBoundaryCap c r
  let G := planarGradientWithin v K
  haveI : CompleteSpace (E2 →L[ℝ] E2) := FiniteDimensional.complete ℝ (E2 →L[ℝ] E2)
  obtain ⟨A, hA⟩ := native_holder_derivative_apply_const K C.a α hDa (coordinateVector 2 1)
  obtain ⟨D, hD⟩ := native_holder_derivative_apply_const K C.d α hDd (coordinateVector 2 1)
  obtain ⟨Ba, hBa, hQa⟩ := native_tangential_quotient_holder_from_within_derivative c hcf r hr C.a α A ha hA
  obtain ⟨Bd, hBd, hQd⟩ := native_tangential_quotient_holder_from_within_derivative c hcf r hr C.d α D hd hD
  obtain ⟨H, hH⟩ := native_holder_planarGradientWithin K v α hDv
  have hKc : IsCompact K := (isCompact_closedBall c (2 * r)).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  obtain ⟨B0, hB0⟩ := hKc.exists_bound_of_continuousOn (hH.continuousOn hα)
  let B := max B0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hG : ∀ x ∈ K, ‖G x‖ ≤ B := fun x hx => (hB0 x hx).trans (le_max_left _ _)
  have hsub : V ⊆ K := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (by linarith : r ≤ 2 * r) hx.1, hx.2⟩
  let Hout := D + (A * Real.toNNReal B + Real.toNNReal Ba * H)
  refine ⟨Bd + Ba * B, Hout, by positivity, ?_⟩
  intro h hne hsmall
  obtain ⟨hqab, hqah⟩ := hQa h hne hsmall
  obtain ⟨hqdb, hqdh⟩ := hQd h hne hsmall
  have hprod := native_holder_clm_apply V _ G A H (Real.toNNReal Ba) (Real.toNNReal B) α
    hqah (hH.mono hsub)
    (fun x hx => (hqab x hx).trans (Real.le_coe_toNNReal Ba))
    (fun x hx => (hG x (hsub hx)).trans (Real.le_coe_toNNReal B))
  refine ⟨?_, native_holder_add V _ _ D _ α hqdh hprod⟩
  intro x hx
  change ‖h⁻¹ • (C.d (shift 1 h x) - C.d x) +
    (h⁻¹ • (C.a (shift 1 h x) - C.a x)) (G x)‖ ≤ _
  calc
    _ ≤ ‖h⁻¹ • (C.d (shift 1 h x) - C.d x)‖ +
        ‖(h⁻¹ • (C.a (shift 1 h x) - C.a x)) (G x)‖ := norm_add_le _ _
    _ ≤ Bd + ‖h⁻¹ • (C.a (shift 1 h x) - C.a x)‖ * ‖G x‖ :=
      add_le_add (hqdb x hx) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ Bd + Ba * B := by gcongr; exact hqab x hx; exact hG x (hsub hx)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
