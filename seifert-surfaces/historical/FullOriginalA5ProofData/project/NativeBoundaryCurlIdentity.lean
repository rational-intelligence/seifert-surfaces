import NativeBoundaryFluxEnergy

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

def nativeQuarterTurn : E2 ≃ₗᵢ[ℝ] E2 := coordinateSwap.trans normalReflection

theorem nativeQuarterTurn_zero (v : E2) : nativeQuarterTurn v 0 = -v 1 := by
  simp [nativeQuarterTurn, normalReflection_zero, coordinateSwap]

theorem nativeQuarterTurn_one (v : E2) : nativeQuarterTurn v 1 = v 0 := by
  simp [nativeQuarterTurn, normalReflection_one, coordinateSwap]

/-- The rotated gradient of an actual native H1 witness is divergence-free.
The proof uses the literal weak partial identities and equality of the
mixed derivatives of the same smooth test function. -/
theorem native_rotated_weak_gradient_divergence_zero
    (U : Set E2) (w : E2 → ℝ) (hw : DeGiorgi.MemW1pWitness 2 w U)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (ht : tsupport φ ⊆ U) :
    IntegrableOn (fun x => inner ℝ (nativeQuarterTurn (hw.weakGrad x)) (planarGradient φ x)) U ∧
      (∫ x in U, inner ℝ (nativeQuarterTurn (hw.weakGrad x)) (planarGradient φ x)) = 0 := by
  let d (i : Fin 2) : E2 → ℝ := fun x => fderiv ℝ φ x (coordinateVector 2 i)
  have hd (i : Fin 2) : ContDiff ℝ ∞ (d i) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdc (i : Fin 2) : HasCompactSupport (d i) := hc.fderiv_apply (𝕜 := ℝ) _
  have hdt (i : Fin 2) : tsupport (d i) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ _).trans ht
  have hdL (i : Fin 2) : MemLp (d i) 2 (volume.restrict U) :=
    ((hd i).continuous.memLp_of_hasCompactSupport (hdc i)).mono_measure Measure.restrict_le_self
  have hi0 : IntegrableOn (fun x => hw.weakGrad x 0 * d 1 x) U :=
    (hw.weakGrad_component_memLp 0).integrable_mul (hdL 1)
  have hi1 : IntegrableOn (fun x => hw.weakGrad x 1 * d 0 x) U :=
    (hw.weakGrad_component_memLp 1).integrable_mul (hdL 0)
  have h0 := hw.isWeakGrad 0 (d 1) (hd 1) (hdc 1) (hdt 1)
  have h1 := hw.isWeakGrad 1 (d 0) (hd 0) (hdc 0) (hdt 0)
  have he (x : E2) : fderiv ℝ (d 1) x (coordinateVector 2 0) =
      fderiv ℝ (d 0) x (coordinateVector 2 1) := by
    have hd1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by simp)
    have hdx : DifferentiableAt ℝ (fderiv ℝ φ) x := hd1.differentiable (by simp) x
    simp only [d, fderiv_clm_apply hdx (differentiableAt_const _), fderiv_fun_const]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, Pi.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply]
    exact ((hφ.of_le (by simp : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt.isSymmSndFDerivAt
      (by norm_num)).eq _ _
  simp only [coordinateVector] at he
  simp_rw [he] at h0
  have hinner : (fun x => inner ℝ (nativeQuarterTurn (hw.weakGrad x)) (planarGradient φ x)) =
      (fun x => hw.weakGrad x 0 * d 1 x - hw.weakGrad x 1 * d 0 x) := by
    funext x
    simp only [PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_two, nativeQuarterTurn_zero,
      nativeQuarterTurn_one, Helpers.gradient_apply, d]
    ring
  rw [hinner]
  refine ⟨hi0.sub hi1, ?_⟩
  rw [integral_sub hi0 hi1]
  linarith

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
