import ReplacementComparison
import ConstantExcessDecay
import WeakBridges
import CampanatoVector.Basic
import WeakDivergenceData
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import NumericIteration

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff ENNReal
namespace SeifertSurfaces.WeakSchauder

private lemma ball_measure_pos (center : V) (R : ℝ) (hR : 0 < R) :
    0 < (volume (Metric.ball center R)).toReal := by
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume center hR).ne' measure_ball_lt_top.ne

private lemma ballMean_mul_measure (G : V → V) (center : V) (R : ℝ) (hR : 0 < R) :
    (volume (Metric.ball center R)).toReal • ballMean G center R =
      ∫ y in Metric.ball center R, G y := by
  rw [ballMean, smul_smul, mul_inv_cancel₀ (ball_measure_pos center R hR).ne', one_smul]

/-- Exact energy/excess/mean decomposition, needed to keep the mean-gradient
term in the coefficient error rather than assume it bounded. -/
theorem energy_excess_mean (G : V → V) (center : V) (R : ℝ) (hR : 0 < R)
    (hG : MemLp G 2 (volume.restrict (Metric.ball center R))) :
    energy G center R = excess G center R +
      (volume (Metric.ball center R)).toReal * ‖ballMean G center R‖ ^ 2 := by
  let μ := volume.restrict (Metric.ball center R)
  have : IsFiniteMeasure μ := ⟨by
    change (volume.restrict (Metric.ball center R)) Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hGi : Integrable G μ := hG.integrable (by norm_num)
  have hsq : Integrable (fun y => ‖G y‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  let b := ballMean G center R
  have hi : Integrable (fun y => inner ℝ (G y) b) μ := hGi.inner_const b
  have hconst : Integrable (fun _ : V => ‖b‖ ^ 2) μ := integrable_const _
  have hid : (∫ y, inner ℝ (G y) b ∂μ) =
      (volume (Metric.ball center R)).toReal * ‖b‖ ^ 2 := by
    conv_lhs => arg 2; ext y; rw [real_inner_comm]
    rw [integral_inner hGi]
    rw [← ballMean_mul_measure G center R hR]
    simp [b, inner_smul_right]
  have hex : excess G center R = energy G center R -
      2 * ((volume (Metric.ball center R)).toReal * ‖b‖ ^ 2) +
      (volume (Metric.ball center R)).toReal * ‖b‖ ^ 2 := by
    unfold excess energy
    change (∫ y, ‖G y - b‖ ^ 2 ∂μ) = _
    simp_rw [norm_sub_sq_real]
    have hscaled : Integrable (fun y => 2 * inner ℝ (G y) b) μ := hi.const_mul 2
    have hdiff : Integrable (fun y => ‖G y‖ ^ 2 - 2 * inner ℝ (G y) b) μ :=
      hsq.sub hscaled
    rw [integral_add hdiff hconst, integral_sub hsq hscaled, integral_const_mul, hid]
    simp [μ, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
  change energy G center R = excess G center R +
    (volume (Metric.ball center R)).toReal * ‖b‖ ^ 2
  linarith

private lemma ball_measure_scale (center : V) (r : ℝ) (hr : 0 < r) :
    (volume (Metric.ball center r)).toReal =
      r ^ (3 : ℕ) * (volume (Metric.ball (0 : V) 1)).toReal := by
  rw [Measure.addHaar_ball_of_pos volume center hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  simp [V]

private lemma mean_sub_const (G : V → V) (center : V) (r : ℝ) (hr : 0 < r)
    (hG : MemLp G 2 (volume.restrict (Metric.ball center r))) (b : V) :
    ballMean (fun y => G y - b) center r = ballMean G center r - b := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball center r)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hi := hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simp only [ballMean, integral_sub hi (integrable_const b), integral_const,
    measureReal_def, Measure.restrict_apply_univ, smul_sub, smul_smul,
    inv_mul_cancel₀ (ball_measure_pos center r hr).ne', one_smul]

/-- The mean change estimate is purely analytic, independent of the PDE. -/
theorem nested_mean_change :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : V → V) (center : V) (R r : ℝ),
      0 < r → r ≤ R → MemLp G 2 (volume.restrict (Metric.ball center R)) →
      ‖ballMean G center r - ballMean G center R‖ ≤
        C * r ^ (-(3 : ℝ) / 2) * Real.sqrt (excess G center R) := by
  let v₁ := (volume (Metric.ball (0 : V) 1)).toReal
  have hv₁ : 0 < v₁ := ball_measure_pos 0 1 zero_lt_one
  refine ⟨(Real.sqrt v₁)⁻¹, by positivity, ?_⟩
  intro G center R r hr hrR hG
  have hR : 0 < R := hr.trans_le hrR
  have : IsFiniteMeasure (volume.restrict (Metric.ball center R)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have : IsFiniteMeasure (volume.restrict (Metric.ball center r)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  let b := ballMean G center R
  let F := fun y => G y - b
  have hF : MemLp F 2 (volume.restrict (Metric.ball center R)) :=
    hG.sub (memLp_const b)
  have hsub : Metric.ball center r ⊆ Metric.ball center R := Metric.ball_subset_ball hrR
  have hFr := hF.mono_measure (Measure.restrict_mono_set volume hsub)
  have hGr := hG.mono_measure (Measure.restrict_mono_set volume hsub)
  have hsq : Integrable (fun y => ‖F y‖ ^ 2) (volume.restrict (Metric.ball center R)) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hener : energy F center r ≤ excess G center R :=
    integral_mono_measure (Measure.restrict_mono_set volume hsub)
      (Filter.Eventually.of_forall fun y => sq_nonneg _) hsq
  have hexnonneg : 0 ≤ excess F center r := integral_nonneg fun _ => sq_nonneg _
  have hdecomp := energy_excess_mean F center r hr hFr
  have hmean := mean_sub_const G center r hr hGr b
  have hmain : (volume (Metric.ball center r)).toReal *
      ‖ballMean G center r - ballMean G center R‖ ^ 2 ≤ excess G center R := by
    change ballMean F center r = _ at hmean
    rw [hmean] at hdecomp
    linarith
  have hz := ball_measure_pos center r hr
  have hE : 0 ≤ excess G center R := integral_nonneg fun _ => sq_nonneg _
  have hfac : ((Real.sqrt v₁)⁻¹ * r ^ (-(3 : ℝ) / 2)) ^ 2 *
      (volume (Metric.ball center r)).toReal = 1 := by
    rw [ball_measure_scale center r hr, mul_pow, inv_pow,
      Real.sq_sqrt hv₁.le, ← Real.rpow_mul_natCast hr.le]
    rw [show (-(3 : ℝ) / 2) * (2 : ℕ) = -3 by norm_num,
      Real.rpow_neg hr.le]
    rw [show r ^ (3 : ℝ) = r ^ (3 : ℕ) from Real.rpow_natCast r 3]
    change v₁⁻¹ * (r ^ 3)⁻¹ * (r ^ 3 * v₁) = 1
    field_simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  apply (mul_le_mul_iff_right₀ hz).mp
  calc
    (volume (Metric.ball center r)).toReal *
        ‖ballMean G center r - ballMean G center R‖ ^ 2 ≤ excess G center R := hmain
    _ = (volume (Metric.ball center r)).toReal *
        ((Real.sqrt v₁)⁻¹ * r ^ (-(3 : ℝ) / 2) * Real.sqrt (excess G center R)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hE]
      calc
        _ = 1 * excess G center R := by ring
        _ = _ := by rw [← hfac]; ring

/-- Coupled numerical iteration with concrete mean vectors and the retained
mean contribution. The smallness threshold and output constant precede both
sequences and the initial radius. This helper does not assert PDE decay. -/
theorem coupled_excess_mean_iteration (α β : NNReal)
    (hβ : 0 < β) (hβα : β < α) (θ D : ℝ)
    (hθ : 0 < θ) (hθone : θ < 1) (hD : 1 ≤ D) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (r₀ : ℝ), 0 < r₀ → D * r₀ ^ (2 * (α : ℝ)) ≤ ε →
      ∀ (e : ℕ → ℝ) (m : ℕ → V), (∀ k, 0 ≤ e k) →
      (∀ k, e (k + 1) ≤ (θ ^ (2 * (β : ℝ)) / 4) * e k +
        D * θ ^ (-(3 : ℝ)) * (r₀ * θ ^ k) ^ (2 * (α : ℝ)) *
          (e k + ‖m k‖ ^ 2)) →
      (∀ k, ‖m (k + 1) - m k‖ ≤ D * θ ^ (-(3 : ℝ) / 2) * Real.sqrt (e k)) →
      (∀ k, e k ≤ C * (e 0 + ‖m 0‖ ^ 2) * (θ ^ k) ^ (2 * (β : ℝ))) ∧
      (∀ k, ‖m k‖ ^ 2 ≤ C * (e 0 + ‖m 0‖ ^ 2)) := by
  let q := θ ^ (β : ℝ)
  let L := D * θ ^ (-(3 : ℝ) / 2)
  let B := 1 + L / (1 - q)
  have hβr : 0 < (β : ℝ) := hβ
  have hqr : 0 < q := Real.rpow_pos_of_pos hθ _
  have hq1 : q < 1 := Real.rpow_lt_one hθ.le hθone hβr
  have hL : 0 < L := mul_pos (by linarith) (Real.rpow_pos_of_pos hθ _)
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [div_nonneg hL.le (sub_pos.mpr hq1).le]
  let ε := q ^ 2 / (2 * θ ^ (-(3 : ℝ)) * (1 + B ^ 2))
  refine ⟨ε, B ^ 2, by dsimp [ε]; positivity, by positivity, ?_⟩
  intro r₀ hr₀ hsmall e m he herec hmrec
  let b := D * r₀ ^ (2 * (α : ℝ)) * θ ^ (-(3 : ℝ))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hsmall' : b * (1 + (1 + L / (1 - q)) ^ 2) ≤ q ^ 2 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hsmall
      (show 0 ≤ θ ^ (-(3 : ℝ)) * (1 + B ^ 2) by positivity)
    have hid : ε * (θ ^ (-(3 : ℝ)) * (1 + B ^ 2)) = q ^ 2 / 2 := by
      dsimp [ε]
      field_simp
    dsimp [b]
    change D * r₀ ^ (2 * (α : ℝ)) * θ ^ (-(3 : ℝ)) * (1 + B ^ 2) ≤ _
    rw [hid] at hmul
    nlinarith only [hmul]
  have hpβ (k : ℕ) : (θ ^ k) ^ (2 * (β : ℝ)) = (q ^ k) ^ 2 := by
    rw [show 2 * (β : ℝ) = (β : ℝ) * (2 : ℕ) by simp [mul_comm],
      Real.rpow_mul_natCast (pow_nonneg hθ.le k)]
    dsimp [q]
    rw [Real.rpow_pow_comm hθ.le]
  have hcoef (k : ℕ) : D * θ ^ (-(3 : ℝ)) *
      (r₀ * θ ^ k) ^ (2 * (α : ℝ)) ≤ b * (q ^ k) ^ 2 := by
    rw [Real.mul_rpow hr₀.le (pow_nonneg hθ.le k)]
    rw [← hpβ k]
    have hp : (θ ^ k) ^ (2 * (α : ℝ)) ≤ (θ ^ k) ^ (2 * (β : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge (pow_pos hθ k)
        (pow_le_one₀ hθ.le hθone.le) (by exact_mod_cast mul_le_mul_of_nonneg_left hβα.le (by norm_num : (0 : ℝ) ≤ 2))
    calc
      _ = b * (θ ^ k) ^ (2 * (α : ℝ)) := by dsimp [b]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hb
  have hrec' (k : ℕ) : e (k + 1) ≤ q ^ 2 / 4 * e k +
      b * (q ^ k) ^ 2 * (e k + ‖m k‖ ^ 2) := by
    have hq2 : θ ^ (2 * (β : ℝ)) = q ^ 2 := by
      dsimp [q]
      rw [show 2 * (β : ℝ) = (β : ℝ) * (2 : ℕ) by simp [mul_comm],
        Real.rpow_mul_natCast hθ.le]
    rw [hq2] at herec
    exact (herec k).trans (add_le_add_right
      (mul_le_mul_of_nonneg_right (hcoef k) (add_nonneg (he k) (sq_nonneg _))) _)
  have hresult := numeric_coupled_bounds q L b hqr hq1 hL.le hb hsmall' e m he hrec' hmrec
  constructor
  · intro k
    rw [hpβ k]
    have hE : 0 ≤ e 0 + ‖m 0‖ ^ 2 := add_nonneg (he 0) (sq_nonneg _)
    have hBsq : 1 ≤ B ^ 2 := by nlinarith [hB]
    calc
      _ ≤ (e 0 + ‖m 0‖ ^ 2) * (q ^ k) ^ 2 := hresult.1 k
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by nlinarith only [mul_le_mul_of_nonneg_right hBsq hE]) (sq_nonneg _)
  · exact hresult.2

end SeifertSurfaces.WeakSchauder

namespace SeifertSurfaces.WeakSchauder
set_option maxHeartbeats 3000000
theorem variable_excess_one_scale (κ Λ : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (center : V) (R : ℝ), 0 < R →
      ∀ (a : V → Mat), CoefficientBounds a (Metric.ball center R) κ Λ →
      ∀ (δ : ℝ), 0 ≤ δ → OscillationBound a (a center) (Metric.ball center R) δ →
      ∀ (v : V → ℝ) (hv : H1Witness v (Metric.ball center R)),
      WeakEquation a hv → ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
        excess hv.weakGrad center (θ * R) ≤
          C * θ ^ (5 : ℕ) * excess hv.weakGrad center R +
          C * δ ^ 2 * energy hv.weakGrad center R := by
  have compare (F G : V → V) (c : V) (r : ℝ) (hr : 0 < r)
      (hF : MemLp F 2 (volume.restrict (Metric.ball c r)))
      (hG : MemLp G 2 (volume.restrict (Metric.ball c r))) :
      excess F c r ≤ 2 * energy (fun x => F x - G x) c r + 2 * excess G c r := by
    let μ := volume.restrict (Metric.ball c r)
    haveI : IsFiniteMeasure μ :=
      isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
    have hv : 0 < (volume (Metric.ball c r)).toReal :=
      ENNReal.toReal_pos (Metric.measure_ball_pos volume c hr).ne' measure_ball_lt_top.ne
    let b := ballMean G c r
    have hFi : Integrable F μ := hF.integrable (by norm_num)
    have hshift : ballMean (fun x => F x - b) c r = ballMean F c r - b := by
      change (volume (Metric.ball c r)).toReal⁻¹ • (∫ x, F x - b ∂μ) = _
      simp only [integral_sub hFi (integrable_const b), integral_const,
        μ, measureReal_def, Measure.restrict_apply_univ, smul_sub, smul_smul,
        inv_mul_cancel₀ hv.ne', one_smul]
      rfl
    have hFe : excess (fun x => F x - b) c r = excess F c r := by
      unfold excess
      rw [hshift]
      congr 1
      ext x
      rw [show F x - b - (ballMean F c r - b) = F x - ballMean F c r by abel]
    have hmin : excess F c r ≤ energy (fun x => F x - b) c r := by
      have h := energy_excess_mean (fun x => F x - b) c r hr (hF.sub (memLp_const b))
      rw [hFe] at h
      have hp : 0 ≤ (volume (Metric.ball c r)).toReal *
          ‖ballMean (fun x => F x - b) c r‖ ^ 2 := by positivity
      linarith
    have hiFG : Integrable (fun x => ‖F x - G x‖ ^ 2) μ :=
      (hF.sub hG).norm.integrable_sq
    have hiGb : Integrable (fun x => ‖G x - b‖ ^ 2) μ :=
      (hG.sub (memLp_const b)).norm.integrable_sq
    have hiFb : Integrable (fun x => ‖F x - b‖ ^ 2) μ :=
      (hF.sub (memLp_const b)).norm.integrable_sq
    have hp : ∀ x, ‖F x - b‖ ^ 2 ≤ 2 * ‖F x - G x‖ ^ 2 + 2 * ‖G x - b‖ ^ 2 := by
      intro x
      have ht : ‖F x - b‖ ≤ ‖F x - G x‖ + ‖G x - b‖ := by
        simpa only [dist_eq_norm] using dist_triangle (F x) (G x) b
      nlinarith [norm_nonneg (F x - b), norm_nonneg (F x - G x), norm_nonneg (G x - b),
        sq_nonneg (‖F x - G x‖ - ‖G x - b‖)]
    have h := integral_mono hiFb ((hiFG.const_mul 2).add (hiGb.const_mul 2)) hp
    simp only [Pi.add_apply] at h
    rw [integral_add (hiFG.const_mul 2) (hiGb.const_mul 2), integral_const_mul,
      integral_const_mul] at h
    exact hmin.trans h
  obtain ⟨D, hD, hdecay⟩ := constant_gradient_excess_decay κ Λ hκ hΛ
  let C := 4 * D + (4 * D + 2) / κ ^ 2 + 1
  have hκsq : 0 < κ ^ 2 := sq_pos_of_pos hκ
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro c R hR a ha δ hδ hosc v hv hw θ hθ hθhalf
  have hcenter : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hA : CoefficientBounds (fun _ => a c) (Metric.ball c R) κ Λ :=
    ⟨fun i j => aemeasurable_const, fun _ _ => ha.coercive c hcenter,
      fun _ _ => ha.mixed c hcenter⟩
  obtain ⟨h, hh, hrep, -, -⟩ := harmonic_replacement_exists c R κ Λ hR hκ hΛ (a c) hA v hv
  have herr := replacement_energy_comparison c R κ Λ δ hR hκ hΛ hδ a (a c) ha hA
    hosc v h hv hh hw hrep
  have hr : 0 < θ * R := mul_pos hθ hR
  have hrhalf : θ * R ≤ R / 2 := by nlinarith
  have hrR : θ * R ≤ R := by linarith
  have hsub := Metric.ball_subset_ball (x := c) hrR
  have hV := hv.weakGrad_memLp
  have hH := hh.weakGrad_memLp
  have hVr := hV.mono_measure (Measure.restrict_mono_set volume hsub)
  have hHr := hH.mono_measure (Measure.restrict_mono_set volume hsub)
  have hint : Integrable (fun x => ‖hv.weakGrad x - hh.weakGrad x‖ ^ 2)
      (volume.restrict (Metric.ball c R)) := (hV.sub hH).norm.integrable_sq
  have hmono : energy (fun x => hv.weakGrad x - hh.weakGrad x) c (θ * R) ≤
      energy (fun x => hv.weakGrad x - hh.weakGrad x) c R :=
    integral_mono_measure (Measure.restrict_mono_set volume hsub)
      (Filter.Eventually.of_forall fun x => sq_nonneg _) hint
  have hreverse : energy (fun x => hh.weakGrad x - hv.weakGrad x) c R =
      energy (fun x => hv.weakGrad x - hh.weakGrad x) c R := by
    unfold energy
    simp only [norm_sub_rev]
  have hwhole := compare hh.weakGrad hv.weakGrad c R hR hH hV
  rw [hreverse] at hwhole
  have hsmall := compare hv.weakGrad hh.weakGrad c (θ * R) hr hVr hHr
  have hd := hdecay c R hR (a c) hA h hh hrep.2 (θ * R) hr hrhalf
  rw [mul_div_cancel_right₀ θ hR.ne'] at hd
  have hnon : 0 ≤ energy hv.weakGrad c R := integral_nonneg fun _ => sq_nonneg _
  have hex : 0 ≤ excess hv.weakGrad c R := integral_nonneg fun _ => sq_nonneg _
  have hθpow : θ ^ (5 : ℕ) ≤ 1 := pow_le_one₀ hθ.le (by linarith)
  have ht0 : 0 ≤ θ ^ (5 : ℕ) := pow_nonneg hθ.le _
  have he0 : 0 ≤ energy (fun x => hv.weakGrad x - hh.weakGrad x) c R :=
    integral_nonneg fun _ => sq_nonneg _
  have hwholedecay := mul_le_mul_of_nonneg_left hwhole (mul_nonneg hD.le ht0)
  have herr' : energy (fun x => hv.weakGrad x - hh.weakGrad x) c R ≤
      δ ^ 2 / κ ^ 2 * energy hv.weakGrad c R := by simpa [div_pow] using herr
  have hb : excess hv.weakGrad c (θ * R) ≤
      4 * D * θ ^ 5 * excess hv.weakGrad c R +
        (4 * D + 2) * energy (fun x => hv.weakGrad x - hh.weakGrad x) c R := by
    have ht := mul_le_mul_of_nonneg_right hθpow (mul_nonneg (by positivity : 0 ≤ 4 * D) he0)
    nlinarith only [hsmall, hd, hwholedecay, hmono, ht]
  have herrscaled := mul_le_mul_of_nonneg_left herr' (by positivity : 0 ≤ 4 * D + 2)
  have hCD : 4 * D ≤ C := by
    dsimp [C]
    have hp : 0 ≤ (4 * D + 2) / κ ^ 2 := by positivity
    linarith
  have hCerr : (4 * D + 2) / κ ^ 2 ≤ C := by dsimp [C]; linarith
  calc
    _ ≤ 4 * D * θ ^ 5 * excess hv.weakGrad c R +
        ((4 * D + 2) / κ ^ 2) * δ ^ 2 * energy hv.weakGrad c R := by
      exact hb.trans (add_le_add_right (by
        convert herrscaled using 1 <;> ring) _)
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD ht0) hex)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCerr (sq_nonneg δ)) hnon)


theorem gradient_campanato_from_weak_equation
    (κ Λ R : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (hR : 0 < R)
    (H α : NNReal) (hα : 0 < α) (hαone : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (center : V) (a : V → Mat),
      CoefficientBounds a (Metric.ball center R) κ Λ →
      CoefficientHolder a (Metric.ball center R) H α →
      ∀ (v : V → ℝ) (hv : H1Witness v (Metric.ball center R)),
      WeakEquation a hv →
      CampanatoBound hv.weakGrad (Metric.ball center (3 * R / 4)) (R / 8) (α / 2)
        (C * energy hv.weakGrad center R) := by
  let β := α / 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβα : β < α := by
    change α / 2 < α
    exact half_lt_self hα
  obtain ⟨A, hA, hscale⟩ := variable_excess_one_scale κ Λ hκ hΛ
  obtain ⟨N, hN, hmean⟩ := nested_mean_change
  let v₁ := CampanatoVector.unitBallVolume 3
  have hv₁ : 0 < v₁ := CampanatoVector.unitBallVolume_pos
  let p := 2 - 2 * (β : ℝ)
  have hp : 0 < p := by
    have ha : (α : ℝ) < 1 := hαone
    dsimp [p, β]
    linarith
  let θ := min (1 / 2 : ℝ) ((1 / (4 * A)) ^ p⁻¹)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθhalf : θ ≤ 1 / 2 := min_le_left _ _
  have hθone : θ < 1 := lt_of_le_of_lt hθhalf (by norm_num)
  have hθsmall : A * θ ^ p ≤ 1 / 4 := by
    have he := Real.rpow_le_rpow hθ.le (min_le_right (1 / 2 : ℝ) _) hp.le
    rw [Real.rpow_inv_rpow (by positivity : 0 ≤ 1 / (4 * A)) hp.ne'] at he
    have ht := mul_le_mul_of_nonneg_left he hA.le
    have hi : A * (1 / (4 * A)) = 1 / 4 := by field_simp
    exact ht.trans_eq hi
  let D := 1 + N + 9 * A * (H : ℝ) ^ 2 * (1 + v₁)
  have hD : 1 ≤ D := by
    dsimp [D]
    have hh : 0 ≤ 9 * A * (H : ℝ) ^ 2 * (1 + v₁) := by positivity
    linarith
  obtain ⟨ε, T, hε, hT, hiterate⟩ := coupled_excess_mean_iteration α β hβ hβα θ D hθ hθone hD
  let r₀ := min (R / 8) ((ε / D) ^ (2 * (α : ℝ))⁻¹)
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hr₀R : r₀ ≤ R / 8 := min_le_left _ _
  have hsmall : D * r₀ ^ (2 * (α : ℝ)) ≤ ε := by
    have har : 0 < (α : ℝ) := hα
    have he := Real.rpow_le_rpow hr₀.le (min_le_right (R / 8) _)
      (by positivity : 0 ≤ 2 * (α : ℝ))
    rw [Real.rpow_inv_rpow (by positivity : 0 ≤ ε / D) (by positivity : 2 * (α : ℝ) ≠ 0)] at he
    have hi : D * (ε / D) = ε := by field_simp
    exact (mul_le_mul_of_nonneg_left he hDpos.le).trans_eq hi
  let γ := 3 + 2 * (β : ℝ)
  let P := 1 + v₁⁻¹
  let C := 1 + 4 * T * P * r₀ ^ (-γ) * θ ^ (-γ) + r₀ ^ (-γ)
  have hC : 0 < C := by dsimp [C, P]; positivity
  refine ⟨C, hC, ?_⟩
  intro c a ha hah v hv hw
  intro x hx r hr hrr
  let G := hv.weakGrad
  have ball_sub (t : ℝ) (ht : t ≤ R / 8) : Metric.ball x t ⊆ Metric.ball c R := by
    intro y hy
    have hxc := Metric.mem_ball.mp hx
    have hyx := Metric.mem_ball.mp hy
    have htriangle := dist_triangle y x c
    exact Metric.mem_ball.mpr (by linarith)
  let ρ : ℕ → ℝ := fun k => r₀ * θ ^ k
  have hρ (k : ℕ) : 0 < ρ k := mul_pos hr₀ (pow_pos hθ _)
  have hρR (k : ℕ) : ρ k ≤ R / 8 := by
    have hp := pow_le_one₀ hθ.le hθone.le (n := k)
    exact (mul_le_mul_of_nonneg_left hp hr₀.le).trans (by simpa using hr₀R)
  let e : ℕ → ℝ := fun k => excess G x (ρ k) / ρ k ^ 3
  let m : ℕ → V := fun k => ballMean G x (ρ k)
  have he (k : ℕ) : 0 ≤ e k := div_nonneg (integral_nonneg fun _ => sq_nonneg _)
    (pow_nonneg (hρ k).le _)
  have hρsucc (k : ℕ) : ρ (k + 1) = θ * ρ k := by dsimp [ρ]; rw [pow_succ]; ring
  have hmem (k : ℕ) : MemLp G 2 (volume.restrict (Metric.ball x (ρ k))) :=
    hv.weakGrad_memLp.mono_measure (Measure.restrict_mono_set volume (ball_sub _ (hρR k)))
  have hvol (k : ℕ) : (volume (Metric.ball x (ρ k))).toReal = ρ k ^ 3 * v₁ :=
    CampanatoVector.measureReal_ball x (hρ k)
  have henergy (k : ℕ) : energy G x (ρ k) =
      ρ k ^ 3 * (e k + v₁ * ‖m k‖ ^ 2) := by
    have hb := energy_excess_mean G x (ρ k) (hρ k) (hmem k)
    rw [hvol] at hb
    dsimp [e, m]
    rw [hb]
    field_simp [(hρ k).ne']
    <;> ring
  have hbase : A * θ ^ 2 ≤ θ ^ (2 * (β : ℝ)) / 4 := by
    have hm := mul_le_mul_of_nonneg_right hθsmall (Real.rpow_nonneg hθ.le (2 * (β : ℝ)))
    have hpow : θ ^ p * θ ^ (2 * (β : ℝ)) = θ ^ (2 : ℕ) := by
      rw [← Real.rpow_add hθ]
      dsimp [p]
      rw [sub_add_cancel, Real.rpow_two]
    rw [mul_assoc, hpow] at hm
    linarith
  have hDN : N ≤ D := by
    dsimp [D]
    have hp : 0 ≤ 9 * A * (H : ℝ) ^ 2 * (1 + v₁) := by positivity
    linarith
  have hDE : 9 * A * (H : ℝ) ^ 2 ≤ D := by
    dsimp [D]
    have hp : 0 ≤ 9 * A * (H : ℝ) ^ 2 * v₁ := by positivity
    nlinarith only [hN.le, hp]
  have hDM : 9 * A * (H : ℝ) ^ 2 * v₁ ≤ D := by
    dsimp [D]
    have hp : 0 ≤ 9 * A * (H : ℝ) ^ 2 := by positivity
    nlinarith only [hN.le, hp]
  have herec (k : ℕ) : e (k + 1) ≤ θ ^ (2 * (β : ℝ)) / 4 * e k +
      D * θ ^ (-(3 : ℝ)) * (r₀ * θ ^ k) ^ (2 * (α : ℝ)) * (e k + ‖m k‖ ^ 2) := by
    obtain ⟨hs, hgs, hws⟩ := weak_equation_restrict a _ Metric.isOpen_ball v hv hw x
      (ρ k) (hρ k) (ball_sub _ (hρR k))
    have has : CoefficientBounds a (Metric.ball x (ρ k)) κ Λ :=
      ⟨fun i j => (ha.measurable i j).mono_measure
        (Measure.restrict_mono_set volume (ball_sub _ (hρR k))),
        fun y hy => ha.coercive y (ball_sub _ (hρR k) hy),
        fun y hy => ha.mixed y (ball_sub _ (hρR k) hy)⟩
    have hh : CoefficientHolder a (Metric.ball x (ρ k)) H α :=
      fun i j => (hah i j).mono (ball_sub _ (hρR k))
    have ho := holder_frozen_oscillation a x (ρ k) (hρ k) H α hh
    have hb := hscale x (ρ k) (hρ k) a has (3 * (H : ℝ) * (ρ k) ^ (α : ℝ))
      (by positivity) ho v hs hws θ hθ hθhalf
    have hfield : hs.weakGrad = G := funext hgs
    rw [hfield, henergy] at hb
    have hδ : ((ρ k) ^ (α : ℝ)) ^ (2 : ℕ) = (ρ k) ^ (2 * (α : ℝ)) := by
      rw [← Real.rpow_mul_natCast (hρ k).le]
      congr 1
      ring
    have ht3 : θ ^ (-(3 : ℝ)) = (θ ^ (3 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hθ.le]
      exact congrArg Inv.inv (Real.rpow_natCast θ 3)
    have hb' : e (k + 1) ≤ A * θ ^ 2 * e k +
        9 * A * (H : ℝ) ^ 2 * θ ^ (-(3 : ℝ)) * (ρ k) ^ (2 * (α : ℝ)) *
          (e k + v₁ * ‖m k‖ ^ 2) := by
      dsimp [e]
      rw [hρsucc]
      apply (div_le_iff₀ (pow_pos (mul_pos hθ (hρ k)) 3)).mpr
      rw [ht3]
      have hid : (A * θ ^ 2 * (excess G x (ρ k) / ρ k ^ 3) +
          9 * A * (H : ℝ) ^ 2 * (θ ^ 3)⁻¹ * (ρ k) ^ (2 * (α : ℝ)) *
            (excess G x (ρ k) / ρ k ^ 3 + v₁ * ‖m k‖ ^ 2)) * (θ * ρ k) ^ 3 =
          A * θ ^ 5 * excess G x (ρ k) +
            A * (3 * (H : ℝ) * (ρ k) ^ (α : ℝ)) ^ 2 *
              (ρ k ^ 3 * (excess G x (ρ k) / ρ k ^ 3 + v₁ * ‖m k‖ ^ 2)) := by
        have hδ' := hδ
        generalize htr : ρ k = t at hδ' ⊢
        have htne : t ≠ 0 := by rw [← htr]; exact (hρ k).ne'
        simp only [mul_pow, hδ']
        field_simp [hθ.ne', htne]
        <;> ring
      rw [hid]
      exact hb
    have hcoef : 9 * A * (H : ℝ) ^ 2 * (e k + v₁ * ‖m k‖ ^ 2) ≤
        D * (e k + ‖m k‖ ^ 2) := by
      have he' := mul_le_mul_of_nonneg_right hDE (he k)
      have hm' := mul_le_mul_of_nonneg_right hDM (sq_nonneg ‖m k‖)
      nlinarith only [he', hm']
    have hc := mul_le_mul_of_nonneg_right hcoef
      (by positivity : 0 ≤ θ ^ (-(3 : ℝ)) * (ρ k) ^ (2 * (α : ℝ)))
    have ha := mul_le_mul_of_nonneg_right hbase (he k)
    change e (k + 1) ≤ _ + D * θ ^ (-(3 : ℝ)) * (ρ k) ^ (2 * (α : ℝ)) * _
    nlinarith only [hb', hc, ha]
  have hmrec (k : ℕ) : ‖m (k + 1) - m k‖ ≤
      D * θ ^ (-(3 : ℝ) / 2) * Real.sqrt (e k) := by
    have hstep : ρ (k + 1) ≤ ρ k := by
      rw [hρsucc]
      exact (mul_le_mul_of_nonneg_right hθone.le (hρ k).le).trans_eq (one_mul _)
    have hb := hmean G x (ρ k) (ρ (k + 1)) (hρ (k + 1)) hstep (hmem k)
    have hpow : Real.sqrt (ρ k ^ 3) = (ρ k) ^ ((3 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (ρ k) 3,
        ← Real.rpow_mul (hρ k).le]
      norm_num
    have heq : (ρ (k + 1)) ^ (-(3 : ℝ) / 2) * Real.sqrt (excess G x (ρ k)) =
        θ ^ (-(3 : ℝ) / 2) * Real.sqrt (e k) := by
      rw [hρsucc, Real.mul_rpow hθ.le (hρ k).le]
      dsimp [e]
      rw [Real.sqrt_div (show 0 ≤ excess G x (ρ k) from integral_nonneg fun _ => sq_nonneg _), hpow]
      rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg (hρ k).le]
      simp only [div_eq_mul_inv]
      ring
    rw [mul_assoc] at hb
    change ‖m (k + 1) - m k‖ ≤ N * ((ρ (k + 1)) ^ (-(3 : ℝ) / 2) *
      Real.sqrt (excess G x (ρ k))) at hb
    rw [heq] at hb
    have hc := mul_le_mul_of_nonneg_right hDN
      (mul_nonneg (Real.rpow_nonneg hθ.le (-(3 : ℝ) / 2)) (Real.sqrt_nonneg (e k)))
    exact hb.trans (by simpa only [mul_assoc] using hc)
  obtain ⟨hdecay, hmbound⟩ := hiterate r₀ hr₀ hsmall e m he herec hmrec
  have htotal : 0 ≤ energy G c R := integral_nonneg fun _ => sq_nonneg _
  have hmono : energy G x r₀ ≤ energy G c R :=
    integral_mono_measure (Measure.restrict_mono_set volume (ball_sub _ hr₀R))
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) hv.weakGrad_memLp.norm.integrable_sq
  have hinit : e 0 + ‖m 0‖ ^ 2 ≤ P * r₀ ^ (-3 : ℝ) * energy G c R := by
    have he0 := he 0
    have hρ0 : ρ 0 = r₀ := by simp [ρ]
    have hE := henergy 0
    rw [hρ0] at hE
    have hscale0 : r₀ ^ (-3 : ℝ) * energy G x r₀ = e 0 + v₁ * ‖m 0‖ ^ 2 := by
      rw [Real.rpow_neg hr₀.le, show r₀ ^ (3 : ℝ) = r₀ ^ (3 : ℕ) from Real.rpow_natCast r₀ 3, hE]
      field_simp [hr₀.ne']
    have hbound0 := mul_le_mul_of_nonneg_left hmono
      (Real.rpow_nonneg hr₀.le (-3))
    rw [hscale0] at hbound0
    have heBound : e 0 ≤ r₀ ^ (-3 : ℝ) * energy G c R := by
      have hp : 0 ≤ v₁ * ‖m 0‖ ^ 2 := by positivity
      linarith
    have hmBound : ‖m 0‖ ^ 2 ≤ v₁⁻¹ * r₀ ^ (-3 : ℝ) * energy G c R := by
      apply (mul_le_mul_iff_right₀ hv₁).mp
      have hid : v₁ * (v₁⁻¹ * r₀ ^ (-3 : ℝ) * energy G c R) =
          r₀ ^ (-3 : ℝ) * energy G c R := by field_simp
      change v₁ * ‖m 0‖ ^ 2 ≤ v₁ * (v₁⁻¹ * r₀ ^ (-3 : ℝ) * energy G c R)
      rw [hid]
      linarith only [hbound0, he0]
    dsimp [P]
    nlinarith only [heBound, hmBound]
  have hgeometric (k : ℕ) : excess G x (ρ k) ≤
      T * P * r₀ ^ (-γ) * energy G c R * (ρ k) ^ γ := by
    have hd := (mul_le_mul_of_nonneg_right (hdecay k) (pow_nonneg (hρ k).le 3)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinit hT.le)
        (Real.rpow_nonneg (pow_nonneg hθ.le _) _)) (pow_nonneg (hρ k).le _))
    have heq : e k * ρ k ^ 3 = excess G x (ρ k) := by dsimp only [e]; field_simp [(hρ k).ne']
    rw [heq] at hd
    have hid : T * (P * r₀ ^ (-3 : ℝ) * energy G c R) *
        (θ ^ k) ^ (2 * (β : ℝ)) * ρ k ^ 3 =
        T * P * r₀ ^ (-γ) * energy G c R * (ρ k) ^ γ := by
      have ha : r₀ ^ (-γ) * (ρ k) ^ γ = (θ ^ k) ^ γ := by
        dsimp only [ρ]
        rw [Real.mul_rpow hr₀.le (pow_nonneg hθ.le _), ← mul_assoc,
          ← Real.rpow_add hr₀, neg_add_cancel, Real.rpow_zero, one_mul]
      have hb : r₀ ^ (-3 : ℝ) * ρ k ^ 3 = (θ ^ k) ^ 3 := by
        dsimp only [ρ]
        rw [mul_pow, Real.rpow_neg hr₀.le]
        rw [show r₀ ^ (3 : ℝ) = r₀ ^ (3 : ℕ) from Real.rpow_natCast r₀ 3]
        change (r₀ ^ (3 : ℕ))⁻¹ * (r₀ ^ 3 * (θ ^ k) ^ 3) = _
        field_simp [hr₀.ne']
      have hc : (θ ^ k) ^ (2 * (β : ℝ)) * (θ ^ k) ^ (3 : ℕ) = (θ ^ k) ^ γ := by
        rw [← Real.rpow_natCast (θ ^ k) 3, ← Real.rpow_add (pow_pos hθ k)]
        congr 1
        dsimp [γ]
        ring
      calc
        _ = T * P * energy G c R * ((θ ^ k) ^ (2 * (β : ℝ)) *
            (r₀ ^ (-3 : ℝ) * ρ k ^ 3)) := by ring
        _ = T * P * energy G c R * (θ ^ k) ^ γ := by rw [hb, hc]
        _ = _ := by rw [← ha]; ring
    exact hd.trans_eq hid
  have hmin (t : ℝ) (ht : 0 < t) (hGt : MemLp G 2 (volume.restrict (Metric.ball x t)))
      (b : V) : excess G x t ≤ energy (fun y => G y - b) x t := by
    let μ := volume.restrict (Metric.ball x t)
    have : IsFiniteMeasure μ :=
      isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
    have htvol : 0 < (volume (Metric.ball x t)).toReal :=
      ENNReal.toReal_pos (Metric.measure_ball_pos volume x ht).ne' measure_ball_lt_top.ne
    have hGi : Integrable G μ := hGt.integrable (by norm_num)
    have hshift : ballMean (fun y => G y - b) x t = ballMean G x t - b := by
      change (volume (Metric.ball x t)).toReal⁻¹ • (∫ y, G y - b ∂μ) = _
      simp only [integral_sub hGi (integrable_const b), integral_const, μ, measureReal_def,
        Measure.restrict_apply_univ, smul_sub, smul_smul, inv_mul_cancel₀ htvol.ne', one_smul]
      rfl
    have hex : excess (fun y => G y - b) x t = excess G x t := by
      unfold excess
      rw [hshift]
      congr 1
      ext y
      rw [show G y - b - (ballMean G x t - b) = G y - ballMean G x t by abel]
    have hh := energy_excess_mean (fun y => G y - b) x t ht (hGt.sub (memLp_const b))
    rw [hex] at hh
    have hp : 0 ≤ (volume (Metric.ball x t)).toReal *
        ‖ballMean (fun y => G y - b) x t‖ ^ 2 := by positivity
    linarith
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hGsmall : MemLp G 2 (volume.restrict (Metric.ball x r)) :=
    hv.weakGrad_memLp.mono_measure (Measure.restrict_mono_set volume (ball_sub _ hrr))
  change excess G x r ≤ C * energy G c R * r ^ γ
  by_cases hrr₀ : r ≤ r₀
  · obtain ⟨k, hkleft, hkright⟩ := exists_nat_pow_near_of_lt_one
      (div_pos hr hr₀) ((div_le_one hr₀).mpr hrr₀) hθ hθone
    have hrk : r ≤ ρ k := by simpa only [ρ, mul_comm] using (div_le_iff₀ hr₀).mp hkright
    have hkr : θ * ρ k ≤ r := by
      have hh := (lt_div_iff₀ hr₀).mp hkleft
      rw [pow_succ] at hh
      dsimp [ρ]
      nlinarith only [hh.le]
    have hnest : excess G x r ≤ excess G x (ρ k) := by
      have hsub := Metric.ball_subset_ball (x := x) hrk
      have hs := (hmem k).sub (memLp_const (ballMean G x (ρ k)))
      exact (hmin r hr hGsmall (ballMean G x (ρ k))).trans
        (integral_mono_measure (Measure.restrict_mono_set volume hsub)
          (Filter.Eventually.of_forall fun y => sq_nonneg _) hs.norm.integrable_sq)
    have hp : (ρ k) ^ γ ≤ θ ^ (-γ) * r ^ γ := by
      have hquot : ρ k ≤ r / θ := (le_div_iff₀ hθ).mpr (by simpa [mul_comm] using hkr)
      have hb := Real.rpow_le_rpow (hρ k).le hquot hγ.le
      rw [Real.div_rpow hr.le hθ.le, div_eq_mul_inv, ← Real.rpow_neg hθ.le] at hb
      simpa only [mul_comm] using hb
    have hco : T * P * r₀ ^ (-γ) * θ ^ (-γ) ≤ C := by
      have hh : 0 ≤ T * P * r₀ ^ (-γ) * θ ^ (-γ) := by dsimp [P]; positivity
      have hz : 0 ≤ r₀ ^ (-γ) := Real.rpow_nonneg hr₀.le _
      dsimp only [C]
      nlinarith only [hh, hz]
    calc
      _ ≤ excess G x (ρ k) := hnest
      _ ≤ T * P * r₀ ^ (-γ) * energy G c R * (ρ k) ^ γ := hgeometric k
      _ ≤ T * P * r₀ ^ (-γ) * energy G c R * (θ ^ (-γ) * r ^ γ) :=
        mul_le_mul_of_nonneg_left hp (by dsimp [P]; positivity)
      _ = (T * P * r₀ ^ (-γ) * θ ^ (-γ)) * energy G c R * r ^ γ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hco htotal) (Real.rpow_nonneg hr.le _)
  · have hh := energy_excess_mean G x r hr hGsmall
    have hn : 0 ≤ (volume (Metric.ball x r)).toReal * ‖ballMean G x r‖ ^ 2 := by positivity
    have he : excess G x r ≤ energy G c R := by
      have he' : excess G x r ≤ energy G x r := by linarith
      exact he'.trans (integral_mono_measure (Measure.restrict_mono_set volume (ball_sub _ hrr))
        (Filter.Eventually.of_forall fun y => sq_nonneg _) hv.weakGrad_memLp.norm.integrable_sq)
    have hp : 1 ≤ r₀ ^ (-γ) * r ^ γ := by
      have hb := Real.rpow_le_rpow hr₀.le (le_of_not_ge hrr₀) hγ.le
      have ht := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hr₀.le (-γ))
      rw [← Real.rpow_add hr₀, neg_add_cancel, Real.rpow_zero] at ht
      exact ht
    have hc : r₀ ^ (-γ) ≤ C := by
      have hh : 0 ≤ 4 * T * P * r₀ ^ (-γ) * θ ^ (-γ) := by dsimp [P]; positivity
      dsimp only [C]
      linarith
    have hp' : 1 ≤ C * r ^ γ := hp.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hr.le _))
    exact he.trans (by nlinarith only [mul_le_mul_of_nonneg_right hp' htotal])


end SeifertSurfaces.WeakSchauder
