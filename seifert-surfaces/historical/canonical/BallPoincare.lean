import H01Membership
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff NNReal ENNReal
namespace SeifertSurfaces.WeakSchauder

set_option maxHeartbeats 3000000

lemma classicalGradient_norm (v : V → ℝ) (x : V) :
    ‖classicalGradient v x‖ = ‖fderiv ℝ v x‖ := by
  let L := fderiv ℝ v x
  let g := (InnerProductSpace.toDual ℝ V).symm L
  have hg : g = classicalGradient v x := by
    have hL : (InnerProductSpace.toDual ℝ V) g = L := by simp [g]
    ext i
    change g i = L (EuclideanSpace.single i 1)
    rw [← hL, InnerProductSpace.toDual_apply_apply]
    simpa using (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) g).symm
  rw [← hg]
  exact (InnerProductSpace.toDual ℝ V).symm.norm_map L

lemma ball_sobolev_constant_scale (center : V) (R : ℝ) (hR : 0 < R) :
    (eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure V) (Metric.ball center R) 2 2 : ℝ) =
      R * (eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure V) (Metric.ball (0 : V) 1) 2 2 : ℝ) := by
  have hvol : (volume (Metric.ball center R)).toReal =
      R ^ (3 : ℕ) * (volume (Metric.ball (0 : V) 1)).toReal := by
    have hscale := Measure.addHaar_ball_of_pos (volume : Measure V) center hR
    simp only [finrank_euclideanSpace, Fintype.card_fin] at hscale
    rw [hscale, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [eLpNormLESNormFDerivOfLeConst]
  have hdim : Module.finrank ℝ V = 3 := by simp [V]
  change (volume (Metric.ball center R)).toReal ^
      (1 / (2 : ℝ) - 1 / (↑(((2 : ℝ≥0)⁻¹ - (Module.finrank ℝ V : ℝ≥0)⁻¹)⁻¹) : ℝ)) *
      (SNormLESNormFDerivOfEqConst ℝ volume 2 : ℝ) = _
  have hexp : (1 / (2 : ℝ) - 1 / (↑(((2 : ℝ≥0)⁻¹ - (Module.finrank ℝ V : ℝ≥0)⁻¹)⁻¹) : ℝ)) = 1 / 3 := by
    rw [hdim]
    have hnum : ((2 : ℝ≥0)⁻¹ - (3 : ℝ≥0)⁻¹) = (1 / 6 : ℝ≥0) := by
      apply NNReal.eq
      rw [NNReal.coe_sub]
      · norm_num
      · exact (inv_le_inv₀ (by norm_num : (0 : ℝ≥0) < 3) (by norm_num : (0 : ℝ≥0) < 2)).mpr (by norm_num)
    change 1 / (2 : ℝ) - 1 / (↑(((2 : ℝ≥0)⁻¹ - (3 : ℝ≥0)⁻¹)⁻¹) : ℝ) = 1 / 3
    rw [hnum]
    norm_num
  simp only [NNReal.coe_mul, NNReal.coe_rpow]
  rw [hexp]
  rw [hdim]
  change _ = R * ((volume (Metric.ball (0 : V) 1)).toReal ^
    (1 / (2 : ℝ) - 1 / (↑(((2 : ℝ≥0)⁻¹ - (3 : ℝ≥0)⁻¹)⁻¹) : ℝ)) * _)
  have hexp' : (1 / (2 : ℝ) - 1 / (↑(((2 : ℝ≥0)⁻¹ - (3 : ℝ≥0)⁻¹)⁻¹) : ℝ)) = 1 / 3 := by
    simpa only [hdim, Nat.cast_ofNat] using hexp
  rw [hexp']
  rw [hvol, Real.mul_rpow (by positivity) ENNReal.toReal_nonneg]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
  norm_num
  ring

lemma smooth_ball_norm_poincare (center : V) (R : ℝ) (hR : 0 < R)
    (v : V → ℝ) (hv : H1Witness v (Metric.ball center R))
    (hs : ContDiff ℝ (⊤ : ℕ∞) v) (hc : HasCompactSupport v)
    (ht : tsupport v ⊆ Metric.ball center R) :
    ‖(witnessPair hv).ofLp.1‖ ≤
      R * (eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure V) (Metric.ball (0 : V) 1) 2 2 : ℝ) *
        ‖(witnessPair hv).ofLp.2‖ := by
  let Ω := Metric.ball center R
  have hbound := eLpNorm_le_eLpNorm_fderiv (volume : Measure V)
    (hs.of_le (by simp))
    ((subset_tsupport v).trans ht) (by norm_num : (1 : ℝ≥0) ≤ 2)
    (by norm_num [V] : (2 : ℝ≥0) < Module.finrank ℝ V) (Metric.isBounded_ball)
  norm_num only [ENNReal.coe_ofNat] at hbound
  have heq : eLpNorm (fderiv ℝ v) 2 volume =
      eLpNorm hv.weakGrad 2 (volume.restrict Ω) := by
    rw [← eLpNorm_restrict_eq_of_support_subset
      (hs.continuous_fderiv (by simp)).aestronglyMeasurable
      ((support_fderiv_subset ℝ).trans ht)]
    apply eLpNorm_congr_norm_ae
      (hs.continuous_fderiv (by simp)).aestronglyMeasurable
      (weak_gradient_memLp Ω v hv).aestronglyMeasurable
    filter_upwards [witnessPair_smooth_grad Metric.isOpen_ball hv hs hc] with x hx
    rw [hx, classicalGradient_norm]
  rw [heq, ← eLpNorm_restrict_eq_of_support_subset hs.continuous.aestronglyMeasurable
    ((subset_tsupport v).trans ht)] at hbound
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.coe_ne_top) (weak_gradient_memLp Ω v hv).eLpNorm_ne_top) hbound
  simpa only [witnessPair, WithLp.ofLp_toLp, Lp.norm_toLp, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ball_sobolev_constant_scale center R hR] using hreal

lemma H01_pair_norm_poincare (center : V) (R : ℝ) (hR : 0 < R)
    (p : H01Space (Metric.ball center R)) :
    ‖p.val.ofLp.1‖ ≤
      R * (eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure V) (Metric.ball (0 : V) 1) 2 2 : ℝ) *
        ‖p.val.ofLp.2‖ := by
  let Ω := Metric.ball center R
  let C := R * (eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure V) (Metric.ball (0 : V) 1) 2 2 : ℝ)
  have hclosed : IsClosed {q : SobolevPair Ω | ‖q.ofLp.1‖ ≤ C * ‖q.ofLp.2‖} :=
    isClosed_le (WithLp.fstL 2 ℝ (Lp ℝ 2 (volume.restrict Ω)) (Lp V 2 (volume.restrict Ω))).continuous.norm
      (continuous_const.mul (WithLp.sndL 2 ℝ (Lp ℝ 2 (volume.restrict Ω))
        (Lp V 2 (volume.restrict Ω))).continuous.norm)
  apply (closure_minimal (s := smoothPairs Ω) ?_ hclosed)
  · rw [← H01Space_eq_closure_smoothPairs Ω Metric.isOpen_ball]
    exact p.property
  · rintro q ⟨v, hv, hs, hc, ht, rfl⟩
    exact smooth_ball_norm_poincare center R hR v hv hs hc ht

lemma toLp_norm_sq_eq_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Ω : Set V} {f : V → E} (hf : MemLp f 2 (volume.restrict Ω)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x in Ω, ‖f x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem H01_ball_poincare :
    ∃ C : ℝ, 0 < C ∧ ∀ (center : V) (R : ℝ), 0 < R →
      ∀ (v : V → ℝ) (hv : H1Witness v (Metric.ball center R)),
        DeGiorgi.MemH01 v (Metric.ball center R) →
        (∫ x in Metric.ball center R, |v x| ^ 2) ≤ C * R ^ 2 * energy hv.weakGrad center R := by
  let K : ℝ := eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure V) (Metric.ball (0 : V) 1) 2 2
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  refine ⟨1 + K ^ 2, by positivity, ?_⟩
  intro center R hR v hv hv0
  let p : H01Space (Metric.ball center R) :=
    ⟨witnessPair hv, (H01Space_mem_iff _ Metric.isOpen_ball v hv).mpr hv0⟩
  have hbound := H01_pair_norm_poincare center R hR p
  have hsq : ‖p.val.ofLp.1‖ ^ 2 ≤ R ^ 2 * K ^ 2 * ‖p.val.ofLp.2‖ ^ 2 := by
    have h := mul_self_le_mul_self (norm_nonneg p.val.ofLp.1) hbound
    dsimp [K] at *
    nlinarith
  have hfun : ‖p.val.ofLp.1‖ ^ 2 = ∫ x in Metric.ball center R, |v x| ^ 2 := by
    exact toLp_norm_sq_eq_integral hv.memLp
  have hgrad : ‖p.val.ofLp.2‖ ^ 2 = energy hv.weakGrad center R :=
    toLp_norm_sq_eq_integral (weak_gradient_memLp _ v hv)
  rw [← hfun, ← hgrad]
  nlinarith [sq_nonneg R, sq_nonneg ‖p.val.ofLp.2‖]

end SeifertSurfaces.WeakSchauder
