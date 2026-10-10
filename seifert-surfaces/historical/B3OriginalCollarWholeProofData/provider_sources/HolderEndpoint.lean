import QuasilinearProviderData
import DifferentialGeometry.External.DeGiorgi.Holder.PublicEstimate

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

private lemma holder_of_real_bound {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {s : Set X} (C α : NNReal)
    (h : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ (C : ℝ) * dist x y ^ (α : ℝ)) :
    HolderOnWith C α f s := by
  intro x hx y hy
  have he := ENNReal.ofReal_le_ofReal (h x hx y hy)
  simpa only [edist_dist, Real.dist_eq, ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
    ENNReal.ofReal_coe_nnreal] using he

private lemma inverse_dilation_ball {center : E3} {R : ℝ} (hR : 0 < R)
    {x : E3} (hx : x ∈ Metric.ball center (R / 2)) :
    R⁻¹ • (x - center) ∈ Metric.ball (0 : E3) (1 / 2 : ℝ) := by
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hx ⊢
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  exact (inv_mul_lt_iff₀ hR).mpr (by linarith)

private lemma affine_ball_maps {center : E3} {R : ℝ} (hR : 0 < R) :
    MapsTo (fun z : E3 => center + R • z) (Metric.ball (0 : E3) 1) (Metric.ball center R) := by
  intro z hz
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hz ⊢
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]
  simpa only [mul_one] using (mul_lt_mul_iff_right₀ hR).mpr hz

private lemma inverse_dilation_distance (center : E3) {R : ℝ} (hR : 0 < R) (x y : E3) :
    dist (R⁻¹ • (x - center)) (R⁻¹ • (y - center)) = R⁻¹ * dist x y := by
  simp only [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right,
    norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]

private lemma affine_l2_integral (center : E3) {R : ℝ} (hR : 0 < R) (V : E3 → ℝ) :
    (∫ z in Metric.ball (0 : E3) 1, |V (center + R • z)| ^ (2 : ℕ)) =
      (R ^ 3)⁻¹ * ∫ x in Metric.ball center R, |V x| ^ (2 : ℕ) := by
  open scoped Pointwise in
  have hscale := Measure.setIntegral_comp_smul_of_pos volume
    (fun x => |V (center + x)| ^ (2 : ℕ)) (Metric.ball (0 : E3) 1) hR
  rw [show R • Metric.ball (0 : E3) 1 = Metric.ball (0 : E3) R from by
    rw [_root_.smul_ball hR.ne']; simp [Real.norm_of_nonneg hR.le]] at hscale
  rw [hscale]
  simp only [smul_eq_mul, E3, finrank_euclideanSpace, Fintype.card_fin]
  congr 1
  rw [show Metric.ball center R = (fun x : E3 => center + x) '' Metric.ball (0 : E3) R from by
    ext x
    constructor
    · intro hx
      refine ⟨x - center, ?_, by simp⟩
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    · rintro ⟨y, hy, rfl⟩
      simpa [Metric.mem_ball, dist_eq_norm] using hy]
  exact ((measurePreserving_add_left volume center).setIntegral_image_emb
    (MeasurableEquiv.addLeft center).measurableEmbedding
    (fun x => |V x| ^ (2 : ℕ)) (Metric.ball (0 : E3) R)).symm

private lemma provider_homogeneous {B : Set E3} {A : DeGiorgi.EllipticCoeff 3 B} {V : E3 → ℝ}
    (h : ProviderHomogeneousEquation B A V) : DeGiorgi.IsHomogeneousWeakSolution A V := by
  refine ⟨h.1, ?_⟩
  intro hV ψ hψ hψw
  exact (h.2 hV ψ hψ hψw).2

theorem R3_uniform_holder_actual_homogeneous_solutions
    (center : E3) (R Λ S : ℝ) (hR : 0 < R) (hΛ : 1 ≤ Λ) (hS : 0 ≤ S) :
    ∃ K α : NNReal, 0 < α ∧ α < 1 ∧
      ∀ (A : DeGiorgi.NormalizedEllipticCoeff 3 (Metric.ball center R)) (V : E3 → ℝ),
        A.1.Λ ≤ Λ → ContinuousOn V (Metric.ball center R) →
        ProviderHomogeneousEquation (Metric.ball center R) A.1 V →
        (∫ y in Metric.ball center R, |V y| ^ (2 : ℕ)) ≤ S ^ 2 →
        HolderOnWith K α V (Metric.ball center (R / 2)) := by
  let C : ℝ := DeGiorgi.CHolderMoser 3
  have hC : 0 ≤ C := (DeGiorgi.C_harnack_nonneg (d := 3) (by norm_num)).trans
    DeGiorgi.C_harnack_le_C_holder_Moser
  have hΛ0 : 0 ≤ Λ := by linarith
  let αr : ℝ := min (1 / 2 : ℝ) (Real.exp (-(C * Λ ^ ((1 : ℝ) / 2))))
  have hαr : 0 < αr := lt_min (by norm_num) (Real.exp_pos _)
  let α : NNReal := ⟨αr, hαr.le⟩
  let C₀ : ℝ := C * Λ ^ ((3 : ℝ) / 4) * (2 : ℝ) ^ ((3 : ℝ) / 2) *
    ((R ^ 3)⁻¹ * S ^ 2) ^ ((1 : ℝ) / 2)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  let K₀ : NNReal := ⟨C₀, hC₀⟩
  let K : NNReal := ⟨C₀ * R⁻¹ ^ αr, by positivity⟩
  refine ⟨K, α, hαr, ?_, ?_⟩
  · change αr < (1 : ℝ)
    exact (min_le_left _ _).trans_lt (by norm_num)
  intro A V hA hcont hweak hL2
  let Au := DeGiorgi.rescaleNormalizedCoeffToUnitBall (d := 3) hR A
  let w : E3 → ℝ := DeGiorgi.rescaleToUnitBall (x₀ := center) (R := R) V
  have hw : DeGiorgi.IsHomogeneousWeakSolution Au.1 w :=
    DeGiorgi.rescaleToUnitBall_isHomogeneousWeakSolution hR A.1 (provider_homogeneous hweak)
  have hwLp : MemLp w 2 (volume.restrict (Metric.ball (0 : E3) 1)) := hw.1.1
  have hInt : IntegrableOn (fun z => |w z| ^ (2 : ℝ)) (Metric.ball (0 : E3) 1) := by
    simpa only [IntegrableOn, Real.norm_eq_abs, ENNReal.toReal_ofNat] using
      hwLp.integrable_norm_rpow (by norm_num) (by norm_num)
  obtain ⟨v, hae, β, hβ, hβlow, hvβ⟩ := DeGiorgi.holder_Moser_of_homogeneousWeakSolution
    (d := 3) (by norm_num) Au (p₀ := 2) (by norm_num) hw hInt
  have hAu : Au.1.Λ = A.1.Λ := rfl
  have hA0 : 0 ≤ A.1.Λ := A.1.Λ_pos.le
  have hαβ : αr ≤ β := by
    apply (min_le_right _ _).trans
    apply le_trans _ hβlow
    rw [hAu]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hA0 hA (by norm_num)) hC
  have hIl2 : (∫ z in Metric.ball (0 : E3) 1, |w z| ^ (2 : ℝ)) ≤ (R ^ 3)⁻¹ * S ^ 2 := by
    simp only [Real.rpow_two]
    rw [show w = fun z => V (center + R • z) from rfl, affine_l2_integral center hR V]
    exact mul_le_mul_of_nonneg_left hL2 (by positivity)
  have hfactor : DeGiorgi.CHolderMoser 3 * Au.1.Λ ^ ((3 : ℝ) / (2 * 2)) *
      (2 / (2 - 1 : ℝ)) ^ ((3 : ℝ) / 2) *
      (∫ z in Metric.ball (0 : E3) 1, |w z| ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤ C₀ := by
    dsimp only [C₀, C]
    rw [hAu]
    norm_num only
    gcongr
  have hv : HolderOnWith K₀ α v (Metric.ball (0 : E3) (1 / 2 : ℝ)) := by
    apply holder_of_real_bound K₀ α
    intro x hx y hy
    have hdist : dist x y ≤ 1 := by
      have := dist_triangle x (0 : E3) y
      have hx' := hx
      have hy' := hy
      simp only [Metric.mem_ball] at hx' hy'
      rw [dist_comm (0 : E3) y] at this
      linarith
    calc
      |v x - v y| ≤ _ := hvβ x hx y hy
      _ ≤ C₀ * dist x y ^ αr := by
        rw [← dist_eq_norm]
        exact mul_le_mul hfactor
          (Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hdist hαr.le hαβ)
          (by positivity) hC₀
      _ = _ := rfl
  have hcw : ContinuousOn w (Metric.ball (0 : E3) 1) :=
    hcont.comp (by fun_prop) (affine_ball_maps hR)
  have hveq : ∀ z ∈ Metric.ball (0 : E3) (1 / 2 : ℝ), v z = w z :=
    Measure.eqOn_open_of_ae_eq
      (ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball (by norm_num)) hae)
      Metric.isOpen_ball (hv.continuousOn hαr)
      (hcw.mono (Metric.ball_subset_ball (by norm_num)))
  apply holder_of_real_bound K α
  intro x hx y hy
  let x' := R⁻¹ • (x - center)
  let y' := R⁻¹ • (y - center)
  have hx' : x' ∈ Metric.ball (0 : E3) (1 / 2 : ℝ) := inverse_dilation_ball hR hx
  have hy' : y' ∈ Metric.ball (0 : E3) (1 / 2 : ℝ) := inverse_dilation_ball hR hy
  have hcancel (z : E3) : w (R⁻¹ • (z - center)) = V z := by
    dsimp [w, DeGiorgi.rescaleToUnitBall]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
  calc
    |V x - V y| = |v x' - v y'| := by rw [hveq x' hx', hveq y' hy']; simp [x', y', hcancel]
    _ ≤ C₀ * dist x' y' ^ αr := by
      have H := hv.dist_le hx' hy'
      change dist (v x') (v y') ≤ C₀ * dist x' y' ^ αr at H
      simpa only [Real.dist_eq] using H
    _ = C₀ * (R⁻¹ * dist x y) ^ αr := by rw [inverse_dilation_distance center hR]
    _ = (K : ℝ) * dist x y ^ (α : ℝ) := by
      rw [Real.mul_rpow (inv_nonneg.mpr hR.le) dist_nonneg]
      change C₀ * (R⁻¹ ^ αr * dist x y ^ αr) = (C₀ * R⁻¹ ^ αr) * dist x y ^ αr
      ring

theorem R3_holder_actual_continuous_homogeneous_solution
    (center : E3) (R : ℝ) (hR : 0 < R)
    (A : DeGiorgi.NormalizedEllipticCoeff 3 (Metric.ball center R))
    (V : E3 → ℝ) (hcont : ContinuousOn V (Metric.ball center R))
    (hweak : ProviderHomogeneousEquation (Metric.ball center R) A.1 V) :
    ∃ K α : NNReal, 0 < α ∧ α < 1 ∧
      HolderOnWith K α V (Metric.ball center (R / 2)) := by
  let I : ℝ := ∫ y in Metric.ball center R, |V y| ^ (2 : ℕ)
  have hI : 0 ≤ I := integral_nonneg (fun _ => sq_nonneg _)
  have hΛ : 1 ≤ A.1.Λ := by simpa only [A.2] using A.1.hΛ
  obtain ⟨K, α, hα, hα1, h⟩ := R3_uniform_holder_actual_homogeneous_solutions
    center R A.1.Λ (Real.sqrt I) hR hΛ (Real.sqrt_nonneg _)
  refine ⟨K, α, hα, hα1, h A V le_rfl hcont hweak ?_⟩
  exact (Real.sq_sqrt hI).ge
end SeifertSurfaces.QuasilinearProviderBridge
