import ReplacementConstruction

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder
set_option maxHeartbeats 3000000

lemma replacement_orthogonality {Ω : Set V} (A : Mat) {v h : V → ℝ}
    (hv : H1Witness v Ω) (hh : H1Witness h Ω) (hrep : IsHarmonicReplacement A hv hh) :
    inner ℝ ((matrixActionLinear A).compLp ((weak_gradient_memLp Ω h hh).toLp hh.weakGrad))
      ((weak_gradient_memLp Ω v hv).toLp hv.weakGrad -
        (weak_gradient_memLp Ω h hh).toLp hh.weakGrad) = 0 := by
  have heq := (hrep.2 _ hrep.1 (witnessSub hv hh)).2
  rw [matrix_inner_toLp A (weak_gradient_memLp Ω h hh)
    (weak_gradient_memLp Ω _ (witnessSub hv hh))] at heq
  have hsub := MemLp.toLp_sub (weak_gradient_memLp Ω v hv) (weak_gradient_memLp Ω h hh)
  change inner ℝ ((matrixActionLinear A).compLp ((weak_gradient_memLp Ω h hh).toLp hh.weakGrad))
    (((weak_gradient_memLp Ω v hv).sub (weak_gradient_memLp Ω h hh)).toLp
      (hv.weakGrad - hh.weakGrad)) = 0 at heq
  rw [hsub] at heq
  exact heq

lemma replacement_energy_bound (center : V) (R κ Λ : ℝ)
    (hR : 0 < R) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (A : Mat)
    (hA : CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ)
    (v h : V → ℝ) (hv : H1Witness v (Metric.ball center R))
    (hh : H1Witness h (Metric.ball center R)) (hrep : IsHarmonicReplacement A hv hh) :
    energy hh.weakGrad center R ≤ (Λ / κ) ^ 2 * energy hv.weakGrad center R := by
  let Ω := Metric.ball center R
  let f := (weak_gradient_memLp Ω v hv).toLp hv.weakGrad
  let g := (weak_gradient_memLp Ω h hh).toLp hh.weakGrad
  let M := (matrixActionLinear A).compLpL 2 (volume.restrict Ω)
  have hΛ0 : 0 ≤ Λ := (hκ.trans_le hΛ).le
  have horth := replacement_orthogonality A hv hh hrep
  change inner ℝ (M g) (f - g) = 0 at horth
  rw [inner_sub_right] at horth
  have hcoercive := matrixLp_coercive center R κ Λ hR A hA g
  change κ * ‖g‖ ^ 2 ≤ inner ℝ (M g) g at hcoercive
  have hM : ‖M g‖ ≤ Λ * ‖g‖ :=
    ((matrixActionLinear A).norm_compLp_le g).trans
      (mul_le_mul_of_nonneg_right (matrixAction_norm_le center R κ Λ hR hκ hΛ A hA) (norm_nonneg _))
  have hpair : κ * ‖g‖ ^ 2 ≤ Λ * ‖g‖ * ‖f‖ := by
    calc
      _ ≤ inner ℝ (M g) g := hcoercive
      _ = inner ℝ (M g) f := by linarith
      _ ≤ ‖M g‖ * ‖f‖ := real_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hM (norm_nonneg _)
  have hnorm : ‖g‖ ≤ (Λ / κ) * ‖f‖ := by
    by_cases hg0 : ‖g‖ = 0
    · rw [hg0]
      positivity
    · have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0)
      have hcancel : κ * ‖g‖ ≤ Λ * ‖f‖ := by
        apply le_of_mul_le_mul_right _ hgpos
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hpair
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hκ).mpr
      nlinarith
  have hsq := mul_self_le_mul_self (norm_nonneg g) hnorm
  change (∫ x in Ω, ‖hh.weakGrad x‖ ^ 2) ≤ (Λ / κ) ^ 2 * (∫ x in Ω, ‖hv.weakGrad x‖ ^ 2)
  rw [← toLp_norm_sq_eq_integral (weak_gradient_memLp Ω h hh),
      ← toLp_norm_sq_eq_integral (weak_gradient_memLp Ω v hv)]
  dsimp [g, f] at hsq ⊢
  nlinarith

end SeifertSurfaces.WeakSchauder
