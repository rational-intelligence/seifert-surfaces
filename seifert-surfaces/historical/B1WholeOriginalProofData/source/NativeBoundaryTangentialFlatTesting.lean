import NativeBoundaryEvenFluxReflection

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- A weak tangential partial derivative may be tested across the flat edge.
Only the tangential derivative of a normal cutoff is used, and that derivative
is exactly zero. No zero trace of the Sobolev function is required. -/
theorem native_tangential_weak_partial_testing_to_flat
    (ρ : ℝ) (f G : E2 → ℝ)
    (hf : MemLp f 2 (volume.restrict (openHalfDisc ρ)))
    (hG : MemLp G 2 (volume.restrict (openHalfDisc ρ)))
    (hw : DeGiorgi.HasWeakPartialDeriv 1 G f (openHalfDisc ρ))
    (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ht : tsupport ψ ⊆ Metric.ball 0 ρ) :
    (∫ x in openHalfDisc ρ, f x * fderiv ℝ ψ x (coordinateVector 2 1)) =
      -(∫ x in openHalfDisc ρ, G x * ψ x) := by
  classical
  let U := openHalfDisc ρ
  let k : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hk (n : ℕ) : 0 < k n := by dsimp [k]; positivity
  let χ : ℕ → E2 → ℝ := fun n x => Real.smoothTransition (k n * x 0 - 1)
  let φ : ℕ → E2 → ℝ := fun n x => χ n x * ψ x
  have hχs (n : ℕ) : ContDiff ℝ ∞ (χ n) :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff).sub contDiff_const)
  have hφs (n : ℕ) : ContDiff ℝ ∞ (φ n) := (hχs n).mul hψ
  have hφc (n : ℕ) : HasCompactSupport (φ n) := hc.mul_left
  have hφt (n : ℕ) : tsupport (φ n) ⊆ U := by
    have hsup : tsupport (φ n) ⊆ {x : E2 | (k n)⁻¹ ≤ x 0} := by
      apply closure_minimal _ (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous)
      intro x hx
      have hχ : χ n x ≠ 0 := by intro hn; exact hx (by simp [φ, hn])
      have hpos : 0 < k n * x 0 - 1 :=
        lt_of_not_ge (fun hz => hχ (Real.smoothTransition.zero_of_nonpos hz))
      rw [← one_div]
      exact (div_le_iff₀ (hk n)).mpr (by change 1 ≤ x 0 * k n; nlinarith)
    intro x hx
    exact ⟨ht ((tsupport_mul_subset_right (f := χ n) (g := ψ)) hx),
      (inv_pos.mpr (hk n)).trans_le (hsup hx)⟩
  have hdχ (n : ℕ) (x : E2) : fderiv ℝ (χ n) x (coordinateVector 2 1) = 0 := by
    have hτ : Differentiable ℝ Real.smoothTransition :=
      (show ContDiff ℝ ∞ Real.smoothTransition from Real.smoothTransition.contDiff).differentiable (by simp)
    have hd := (hτ _).hasDerivAt.comp_hasFDerivAt x
      (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.const_mul (k n)).sub_const 1)
    rw [show fderiv ℝ (χ n) x = deriv Real.smoothTransition (k n * x 0 - 1) •
      (k n • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) from hd.fderiv]
    simp [coordinateVector]
  have hdφ (n : ℕ) (x : E2) : fderiv ℝ (φ n) x (coordinateVector 2 1) =
      χ n x * fderiv ℝ ψ x (coordinateVector 2 1) := by
    unfold φ
    rw [fderiv_fun_mul ((hχs n).differentiable (by simp) x) (hψ.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul, hdχ, mul_zero, add_zero]
  have hχbound (n : ℕ) (x : E2) : |χ n x| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hχevent (x : E2) (hx : x ∈ U) : ∀ᶠ n in atTop, χ n x = 1 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (3 / x 0)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hxpos : 0 < x 0 := hx.2
    have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hh := (div_lt_iff₀ hxpos).mp hN
    apply Real.smoothTransition.one_of_one_le
    dsimp [k]
    nlinarith
  let dψ : E2 → ℝ := fun x => fderiv ℝ ψ x (coordinateVector 2 1)
  have hdψ : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψc : HasCompactSupport dψ := hc.fderiv_apply (𝕜 := ℝ) _
  have hdψLp : MemLp dψ 2 (volume.restrict U) :=
    (hdψ.memLp_of_hasCompactSupport hdψc).restrict U
  have hψLp : MemLp ψ 2 (volume.restrict U) :=
    (hψ.continuous.memLp_of_hasCompactSupport hc).restrict U
  have hiF : Integrable (fun x => f x * dψ x) (volume.restrict U) := hf.integrable_mul hdψLp
  have hiG : Integrable (fun x => G x * ψ x) (volume.restrict U) := hG.integrable_mul hψLp
  have hlimit (H : E2 → ℝ) (hH : Integrable H (volume.restrict U)) :
      Tendsto (fun n => ∫ x in U, χ n x * H x) atTop (𝓝 (∫ x in U, H x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖H x‖)
    · intro n
      exact (hχs n).continuous.aestronglyMeasurable.mul hH.aestronglyMeasurable
    · exact hH.norm
    · intro n
      exact Eventually.of_forall (fun x => by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (hχbound n x) (norm_nonneg _)).trans_eq (one_mul _))
    · filter_upwards [ae_restrict_mem (openHalfDisc_isOpen ρ).measurableSet] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hχevent x hx] with n hn
      simp only [hn, one_mul]
  have hwe (n : ℕ) : (∫ x in U, χ n x * (f x * dψ x)) =
      -(∫ x in U, χ n x * (G x * ψ x)) := by
    have hh := hw (φ n) (hφs n) (hφc n) (hφt n)
    change (∫ x in U, f x * fderiv ℝ (φ n) x (coordinateVector 2 1)) =
      -(∫ x in U, G x * φ n x) at hh
    simp only [hdφ, φ] at hh
    have hl : (∫ x in U, χ n x * (f x * dψ x)) =
        ∫ x in U, f x * (χ n x * fderiv ℝ ψ x (coordinateVector 2 1)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by dsimp [dψ]; ring)
    have hr : (∫ x in U, χ n x * (G x * ψ x)) =
        ∫ x in U, G x * (χ n x * ψ x) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by ring)
    rw [hl, hr]
    exact hh
  exact tendsto_nhds_unique (hlimit _ hiF)
    ((hlimit _ hiG).neg.congr' (Eventually.of_forall (fun n => (hwe n).symm)))

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
