import NativeSubcriticalSobolev
import NativeOriginalCaccioppoli
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Covering.DensityTheorem

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem gehring_truncation_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (h : α → ℝ) (hm : AEMeasurable h μ) (hn : ∀ x, 0 ≤ h x)
    (s δ T : ℝ) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (hi : Integrable (fun x => h x ^ s) μ) :
    Integrable (fun x => h x ^ s * (min (h x) T) ^ δ) μ := by
  apply hi.mul_bdd ((hm.min aemeasurable_const).pow_const δ).aestronglyMeasurable
    (c := T ^ δ)
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_min (hn x) hT) _)]
    exact Real.rpow_le_rpow (le_min (hn x) hT) (min_le_right _ _) hδ)

/-- The finite truncations are established before taking their monotone limit. -/
private theorem gehring_integrable_of_uniform_truncation
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (h : α → ℝ) (hm : AEMeasurable h μ) (hn : ∀ x, 0 ≤ h x)
    (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ)
    (hi : Integrable (fun x => h x ^ s) μ)
    (B : ℝ) (hbound : ∀ T : ℝ, 0 ≤ T →
      (∫ x, h x ^ s * (min (h x) T) ^ δ ∂μ) ≤ B) :
    Integrable (fun x => h x ^ (s + δ)) μ := by
  let F : ℕ → α → ℝ≥0∞ := fun n x => ENNReal.ofReal (h x ^ s * (min (h x) (n : ℝ)) ^ δ)
  have hF (n : ℕ) : AEMeasurable (F n) μ :=
    ((hm.pow_const s).mul ((hm.min aemeasurable_const).pow_const δ)).ennreal_ofReal
  have hmono : ∀ᵐ x ∂μ, Monotone (fun n => F n x) := by
    exact Eventually.of_forall (fun x n m hnm => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (le_min (hn x) (Nat.cast_nonneg n))
          (min_le_min_left _ (Nat.cast_le.mpr hnm)) hδ.le)
        (Real.rpow_nonneg (hn x) s)))
  have ht : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop
      (𝓝 (ENNReal.ofReal (h x ^ (s + δ)))) := by
    apply Eventually.of_forall
    intro x
    have hev : ∀ᶠ n : ℕ in atTop, h x ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop (h x))
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn'
    dsimp only [F]
    rw [min_eq_left hn', Real.rpow_add_of_nonneg (hn x) hs.le hδ.le]
  have hlim := lintegral_tendsto_of_tendsto_of_monotone hF hmono ht
  have hlin : ∀ n, (∫⁻ x, F n x ∂μ) ≤ ENNReal.ofReal B := by
    intro n
    rw [show (∫⁻ x, F n x ∂μ) = ENNReal.ofReal
      (∫ x, h x ^ s * (min (h x) (n : ℝ)) ^ δ ∂μ) from
      (ofReal_integral_eq_lintegral_ofReal
        (gehring_truncation_integrable h hm hn s δ n hδ.le (Nat.cast_nonneg n) hi)
        (Eventually.of_forall (fun x => mul_nonneg (Real.rpow_nonneg (hn x) _)
          (Real.rpow_nonneg (le_min (hn x) (Nat.cast_nonneg n)) _)))).symm]
    exact ENNReal.ofReal_le_ofReal (hbound n (Nat.cast_nonneg n))
  have hfinite : (∫⁻ x, ENNReal.ofReal (h x ^ (s + δ)) ∂μ) < ⊤ :=
    (le_of_tendsto hlim (Eventually.of_forall hlin)).trans_lt ENNReal.ofReal_lt_top
  refine ⟨(hm.pow_const (s + δ)).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun x => Real.rpow_nonneg (hn x) _))).mpr hfinite

private theorem gehring_memLp_of_uniform_truncation
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (h : α → ℝ) (hm : AEMeasurable h μ) (hn : ∀ x, 0 ≤ h x)
    (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ)
    (hi : Integrable (fun x => h x ^ s) μ)
    (B : ℝ) (hbound : ∀ T : ℝ, 0 ≤ T →
      (∫ x, h x ^ s * (min (h x) T) ^ δ ∂μ) ≤ B) :
    MemLp h (ENNReal.ofReal (s + δ)) μ := by
  have hp : 0 < s + δ := add_pos hs hδ
  apply (integrable_norm_rpow_iff hm.aestronglyMeasurable
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (hn _)] using
    gehring_integrable_of_uniform_truncation h hm hn s δ hs hδ hi B hbound

private theorem gehring_truncated_layercake
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (h : α → ℝ) (hm : Measurable h) (hn : ∀ x, 0 ≤ h x)
    (s δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) :
    (∫⁻ x, ENNReal.ofReal (h x ^ s * min (h x) T ^ δ) ∂μ) =
      ENNReal.ofReal δ * ∫⁻ t in Ioo 0 T,
        (∫⁻ x in {x | t < h x}, ENNReal.ofReal (h x ^ s) ∂μ) *
          ENNReal.ofReal (t ^ (δ - 1)) := by
  let w : α → ℝ≥0∞ := fun x => ENNReal.ofReal (h x ^ s)
  let ν : Measure α := μ.withDensity w
  have hweight : Measurable w := (hm.pow_const s).ennreal_ofReal
  have hclip : Measurable (fun x => min (h x) T) := hm.min measurable_const
  have hl := lintegral_rpow_eq_lintegral_meas_lt_mul ν
    (f := fun x => min (h x) T)
    (Eventually.of_forall (fun x => le_min (hn x) hT)) hclip.aemeasurable hδ
  have hleft : (∫⁻ x, ENNReal.ofReal (min (h x) T ^ δ) ∂ν) =
      ∫⁻ x, ENNReal.ofReal (h x ^ s * min (h x) T ^ δ) ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul μ hweight (hclip.pow_const δ).ennreal_ofReal]
    apply lintegral_congr
    intro x
    exact (ENNReal.ofReal_mul (Real.rpow_nonneg (hn x) _)).symm
  rw [hleft] at hl
  rw [hl]
  congr 1
  have hsets (t : ℝ) : {x | t < min (h x) T} =
      if t < T then {x | t < h x} else ∅ := by
    split_ifs with ht
    · ext x; simp [lt_min_iff, ht]
    · ext x; simp [lt_min_iff, ht]
  simp_rw [hsets]
  have hfun : (fun t => ν (if t < T then {x | t < h x} else ∅) * ENNReal.ofReal (t ^ (δ - 1))) =
      (Iio T).indicator (fun t => ν {x | t < h x} * ENNReal.ofReal (t ^ (δ - 1))) := by
    funext t
    by_cases ht : t < T <;> simp [ht, Set.indicator, mem_Iio]
  rw [hfun, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  rw [show Iio T ∩ Ioi (0 : ℝ) = Ioo 0 T by ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]; tauto]
  apply lintegral_congr
  intro t
  rw [withDensity_apply w (measurableSet_lt measurable_const hm)]

private theorem gehring_weighted_truncated_layercake
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (h : α → ℝ) (hm : Measurable h) (hn : ∀ x, 0 ≤ h x)
    (w : α → ℝ≥0∞) (hw : Measurable w)
    (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) :
    (∫⁻ x, w x * ENNReal.ofReal (min (h x) T ^ δ) ∂μ) =
      ENNReal.ofReal δ * ∫⁻ t in Ioo 0 T,
        (∫⁻ x in {x | t < h x}, w x ∂μ) * ENNReal.ofReal (t ^ (δ - 1)) := by
  let ν : Measure α := μ.withDensity w
  have hclip : Measurable (fun x => min (h x) T) := hm.min measurable_const
  have hl := lintegral_rpow_eq_lintegral_meas_lt_mul ν
    (f := fun x => min (h x) T)
    (Eventually.of_forall (fun x => le_min (hn x) hT)) hclip.aemeasurable hδ
  rw [lintegral_withDensity_eq_lintegral_mul μ hw (hclip.pow_const δ).ennreal_ofReal] at hl
  change (∫⁻ x, (w * fun x => ENNReal.ofReal (min (h x) T ^ δ)) x ∂μ) = _
  rw [hl]
  congr 1
  have hsets (t : ℝ) : {x | t < min (h x) T} =
      if t < T then {x | t < h x} else ∅ := by
    split_ifs with ht
    · ext x; simp [lt_min_iff, ht]
    · ext x; simp [lt_min_iff, ht]
  simp_rw [hsets]
  have hfun : (fun t => ν (if t < T then {x | t < h x} else ∅) * ENNReal.ofReal (t ^ (δ - 1))) =
      (Iio T).indicator (fun t => ν {x | t < h x} * ENNReal.ofReal (t ^ (δ - 1))) := by
    funext t
    by_cases ht : t < T <;> simp [ht, Set.indicator, mem_Iio]
  rw [hfun, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  rw [show Iio T ∩ Ioi (0 : ℝ) = Ioo 0 T by ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]; tauto]
  apply lintegral_congr
  intro t
  rw [withDensity_apply w (measurableSet_lt measurable_const hm)]

private theorem gehring_truncation_power_bound
    (h T s δ : ℝ) (hh : 0 ≤ h) (hT : 0 ≤ T) (hs : 1 < s) (hδ : 0 < δ) :
    h * min (2 * h) T ^ (s + δ - 1) ≤
      2 ^ (s + δ - 1) * (h ^ s * min h T ^ δ) := by
  have hm : 0 ≤ min (2 * h) T := le_min (by positivity) hT
  have hm2 : min (2 * h) T ≤ 2 * min h T := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact min_le_min (le_refl _) (by linarith)
  have hs0 : 0 < s - 1 := by linarith
  have hsplit : s + δ - 1 = (s - 1) + δ := by ring
  rw [hsplit, Real.rpow_add_of_nonneg hm hs0.le hδ.le]
  have hp : min (2 * h) T ^ (s - 1) * min (2 * h) T ^ δ ≤
      (2 * h) ^ (s - 1) * (2 * min h T) ^ δ := by
    exact mul_le_mul (Real.rpow_le_rpow hm (min_le_left _ _) hs0.le)
      (Real.rpow_le_rpow hm hm2 hδ.le) (Real.rpow_nonneg hm _)
      (Real.rpow_nonneg (by positivity) _)
  calc
    h * (min (2 * h) T ^ (s - 1) * min (2 * h) T ^ δ)
        ≤ h * ((2 * h) ^ (s - 1) * (2 * min h T) ^ δ) := mul_le_mul_of_nonneg_left hp hh
    _ = 2 ^ ((s - 1) + δ) * (h ^ s * min h T ^ δ) := by
      rw [Real.mul_rpow (by norm_num) hh,
        Real.mul_rpow (by norm_num) (le_min hh hT),
        Real.rpow_add_of_nonneg (by norm_num) hs0.le hδ.le]
      have hhpow : h * h ^ (s - 1) = h ^ s := by
        calc
          h * h ^ (s - 1) = h ^ (1 : ℝ) * h ^ (s - 1) := by rw [Real.rpow_one]
          _ = h ^ (1 + (s - 1)) := (Real.rpow_add_of_nonneg hh (by norm_num) hs0.le).symm
          _ = h ^ s := by congr 1; ring
      rw [← hhpow]
      ring

private theorem gehring_truncated_distribution_bound
    {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    (h : α → ℝ) (hm : Measurable h) (hn : ∀ x, 0 ≤ h x)
    (s δ T L C : ℝ) (hs : 1 < s) (hδ : 0 < δ) (hT : 0 ≤ T)
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (htail : ∀ t : ℝ, 0 < t → L ≤ t →
      (∫⁻ x in {x | t < h x}, ENNReal.ofReal (h x ^ s) ∂μ) ≤
        ENNReal.ofReal C * ENNReal.ofReal (t ^ (s - 1)) *
          ∫⁻ x in {x | t < 2 * h x}, ENNReal.ofReal (h x) ∂ν) :
    (∫⁻ x, ENNReal.ofReal (h x ^ s * min (h x) T ^ δ) ∂μ) ≤
      ENNReal.ofReal (L ^ δ) * (∫⁻ x, ENNReal.ofReal (h x ^ s) ∂μ) +
        (ENNReal.ofReal δ * ENNReal.ofReal C *
          (ENNReal.ofReal (s + δ - 1))⁻¹ * ENNReal.ofReal (2 ^ (s + δ - 1))) *
          ∫⁻ x, ENNReal.ofReal (h x ^ s * min (h x) T ^ δ) ∂ν := by
  let β := s + δ - 1
  have hβ : 0 < β := by dsimp only [β]; linarith
  let A : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in {x | t < h x}, ENNReal.ofReal (h x ^ s) ∂μ
  let B : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in {x | t < 2 * h x}, ENNReal.ofReal (h x) ∂ν
  let D : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in {x : α | t < L}, ENNReal.ofReal (h x ^ s) ∂μ
  have hAm : Measurable A :=
    (show Antitone A from fun a b hab => lintegral_mono_set (fun x hx => hab.trans_lt hx)).measurable
  have hBm : Measurable B :=
    (show Antitone B from fun a b hab => lintegral_mono_set (fun x hx => hab.trans_lt hx)).measurable
  have hDm : Measurable D :=
    (show Antitone D from fun a b hab => lintegral_mono_set (fun x hx => hab.trans_lt hx)).measurable
  have hp (t : ℝ) (ht : 0 < t) :
      A t * ENNReal.ofReal (t ^ (δ - 1)) ≤
        D t * ENNReal.ofReal (t ^ (δ - 1)) +
          ENNReal.ofReal C * (B t * ENNReal.ofReal (t ^ (β - 1))) := by
    have hab : A t ≤ D t + ENNReal.ofReal C * ENNReal.ofReal (t ^ (s - 1)) * B t := by
      by_cases htL : t < L
      · have hd : D t = ∫⁻ x, ENNReal.ofReal (h x ^ s) ∂μ := by simp [D, htL]
        exact (show A t ≤ D t by rw [hd]; exact setLIntegral_le_lintegral _ _).trans (le_self_add)
      · exact (htail t ht (le_of_not_gt htL)).trans le_add_self
    have hpow : ENNReal.ofReal (t ^ (s - 1)) * ENNReal.ofReal (t ^ (δ - 1)) =
        ENNReal.ofReal (t ^ (β - 1)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht]
      congr 2
      dsimp only [β]
      ring
    calc
      _ ≤ (D t + ENNReal.ofReal C * ENNReal.ofReal (t ^ (s - 1)) * B t) *
          ENNReal.ofReal (t ^ (δ - 1)) := mul_le_mul_left hab _
      _ = _ := by rw [add_mul]; rw [show ENNReal.ofReal C * ENNReal.ofReal (t ^ (s - 1)) * B t *
          ENNReal.ofReal (t ^ (δ - 1)) =
          ENNReal.ofReal C * (B t * (ENNReal.ofReal (t ^ (s - 1)) * ENNReal.ofReal (t ^ (δ - 1)))) by ring, hpow]
  have hpoint : (∫⁻ t in Ioo 0 T, A t * ENNReal.ofReal (t ^ (δ - 1))) ≤
      (∫⁻ t in Ioo 0 T, D t * ENNReal.ofReal (t ^ (δ - 1))) +
      ENNReal.ofReal C * (∫⁻ t in Ioo 0 T, B t * ENNReal.ofReal (t ^ (β - 1))) := by
    calc
      _ ≤ ∫⁻ t in Ioo 0 T, D t * ENNReal.ofReal (t ^ (δ - 1)) +
          ENNReal.ofReal C * (B t * ENNReal.ofReal (t ^ (β - 1))) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hp t ht.1
      _ = _ := by
        rw [lintegral_add_left (f := fun t => D t * ENNReal.ofReal (t ^ (δ - 1)))
          (hDm.mul (measurable_id.pow_const (δ - 1)).ennreal_ofReal),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hlow : ENNReal.ofReal δ * (∫⁻ t in Ioo 0 T, D t * ENNReal.ofReal (t ^ (δ - 1))) ≤
      ENNReal.ofReal (L ^ δ) * (∫⁻ x, ENNReal.ofReal (h x ^ s) ∂μ) := by
    rw [← gehring_weighted_truncated_layercake μ (fun _ => L) measurable_const (fun _ => hL)
      (fun x => ENNReal.ofReal (h x ^ s)) (hm.pow_const s).ennreal_ofReal δ T hδ hT]
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (h x ^ s) * ENNReal.ofReal (L ^ δ) ∂μ := by
        apply lintegral_mono
        intro x
        apply mul_le_mul_right
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (le_min hL hT) (min_le_left _ _) hδ.le)
      _ = _ := by rw [lintegral_mul_const _ (hm.pow_const s).ennreal_ofReal, mul_comm]
  have hhighEq : ENNReal.ofReal β * (∫⁻ t in Ioo 0 T, B t * ENNReal.ofReal (t ^ (β - 1))) =
      ∫⁻ x, ENNReal.ofReal (h x * min (2 * h x) T ^ β) ∂ν := by
    rw [← gehring_weighted_truncated_layercake ν (fun x => 2 * h x) (hm.const_mul 2)
      (fun x => mul_nonneg (by norm_num) (hn x)) (fun x => ENNReal.ofReal (h x)) hm.ennreal_ofReal β T hβ hT]
    apply lintegral_congr
    intro x
    exact (ENNReal.ofReal_mul (hn x)).symm
  have hhigh : ENNReal.ofReal β * (∫⁻ t in Ioo 0 T, B t * ENNReal.ofReal (t ^ (β - 1))) ≤
      ENNReal.ofReal (2 ^ β) * (∫⁻ x, ENNReal.ofReal (h x ^ s * min (h x) T ^ δ) ∂ν) := by
    rw [hhighEq]
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (2 ^ β) * ENNReal.ofReal (h x ^ s * min (h x) T ^ δ) ∂ν := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) β)]
        exact ENNReal.ofReal_le_ofReal (gehring_truncation_power_bound (h x) T s δ (hn x) hT hs hδ)
      _ = _ := lintegral_const_mul _ (((hm.pow_const s).mul ((hm.min measurable_const).pow_const δ)).ennreal_ofReal)
  have hhigh' : (∫⁻ t in Ioo 0 T, B t * ENNReal.ofReal (t ^ (β - 1))) ≤
      (ENNReal.ofReal β)⁻¹ * ENNReal.ofReal (2 ^ β) *
        (∫⁻ x, ENNReal.ofReal (h x ^ s * min (h x) T ^ δ) ∂ν) := by
    have hh := mul_le_mul_right hhigh (ENNReal.ofReal β)⁻¹
    simpa only [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hβ).ne' ENNReal.ofReal_ne_top, one_mul] using hh
  rw [gehring_truncated_layercake μ h hm hn s δ T hδ hT]
  calc
    _ ≤ ENNReal.ofReal δ * ((∫⁻ t in Ioo 0 T, D t * ENNReal.ofReal (t ^ (δ - 1))) +
        ENNReal.ofReal C * (∫⁻ t in Ioo 0 T, B t * ENNReal.ofReal (t ^ (β - 1)))) :=
      mul_le_mul_right hpoint _
    _ ≤ ENNReal.ofReal (L ^ δ) * (∫⁻ x, ENNReal.ofReal (h x ^ s) ∂μ) +
        ENNReal.ofReal δ * ENNReal.ofReal C *
          ((ENNReal.ofReal β)⁻¹ * ENNReal.ofReal (2 ^ β) *
            (∫⁻ x, ENNReal.ofReal (h x ^ s * min (h x) T ^ δ) ∂ν)) := by
      rw [mul_add, ← mul_assoc]
      exact add_le_add hlow (mul_le_mul_right hhigh' _)
    _ = _ := by dsimp only [β]; ring

private theorem gehring_coefficient_small (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      δ * C * (3 / 2 + δ - 1)⁻¹ * 2 ^ (3 / 2 + δ - 1) ≤ 1 / 16 := by
  let δ := min (1 / 2 : ℝ) (1 / (64 * (C + 1)))
  have hd : 0 < δ := lt_min (by norm_num) (by positivity)
  have hd1 : δ ≤ 1 / 2 := min_le_left _ _
  have hd2 : δ * (64 * (C + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨δ, hd, hd1, ?_⟩
  have hb : 0 < (3 / 2 : ℝ) + δ - 1 := by linarith
  have hb1 : (3 / 2 : ℝ) + δ - 1 ≤ 1 := by linarith
  have hp : (2 : ℝ) ^ ((3 / 2 : ℝ) + δ - 1) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hb1
  have hi : ((3 / 2 : ℝ) + δ - 1)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hb]; linarith
  have hc : δ * C * ((3 / 2 : ℝ) + δ - 1)⁻¹ * (2 : ℝ) ^ ((3 / 2 : ℝ) + δ - 1) ≤
      δ * C * 2 * 2 := by gcongr
  nlinarith

private theorem gehring_discrete_hole_filling
    (F : ℕ → ℝ) (A M : ℝ) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hbound : ∀ n, F n ≤ M)
    (hstep : ∀ n, F n ≤ A * (4 : ℝ) ^ n + (1 / 8 : ℝ) * F (n + 1)) :
    F 0 ≤ 2 * A := by
  have hlimit : ∀ (F : ℕ → ℝ) (B a b T : ℝ),
      0 ≤ B → 0 ≤ a → a < 1 → 0 ≤ b → a * b < 1 → 0 ≤ T →
      (∀ n, F n ≤ a * F (n + 1) + B * b ^ n) →
      (∀ n, F n ≤ T) → F 0 ≤ B / (1 - a * b) := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeHoleFilling 0).str "native_hole_filling_limit"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent pn)))
  have hh := hlimit F A (1 / 8) 4 M hA (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hM (fun n => by simpa [add_comm] using hstep n) hbound
  norm_num at hh
  linarith

private theorem gehring_truncated_distribution_bound_real
    {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    (h : α → ℝ) (hm : Measurable h) (hn : ∀ x, 0 ≤ h x)
    (s δ T L C : ℝ) (hs : 1 < s) (hδ : 0 < δ) (hT : 0 ≤ T)
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hμ : Integrable (fun x => h x ^ s) μ) (hν : Integrable (fun x => h x ^ s) ν)
    (htail : ∀ t : ℝ, 0 < t → L ≤ t →
      (∫⁻ x in {x | t < h x}, ENNReal.ofReal (h x ^ s) ∂μ) ≤
        ENNReal.ofReal C * ENNReal.ofReal (t ^ (s - 1)) *
          ∫⁻ x in {x | t < 2 * h x}, ENNReal.ofReal (h x) ∂ν) :
    (∫ x, h x ^ s * min (h x) T ^ δ ∂μ) ≤
      L ^ δ * (∫ x, h x ^ s ∂μ) +
        (δ * C * (s + δ - 1)⁻¹ * 2 ^ (s + δ - 1)) *
          ∫ x, h x ^ s * min (h x) T ^ δ ∂ν := by
  have hnclip (x : α) : 0 ≤ h x ^ s * min (h x) T ^ δ :=
    mul_nonneg (Real.rpow_nonneg (hn x) _) (Real.rpow_nonneg (le_min (hn x) hT) _)
  have hni (ρ : Measure α) : 0 ≤ ∫ x, h x ^ s * min (h x) T ^ δ ∂ρ := integral_nonneg hnclip
  have hni' (ρ : Measure α) : 0 ≤ ∫ x, h x ^ s ∂ρ :=
    integral_nonneg (fun x => Real.rpow_nonneg (hn x) _)
  have hβ : 0 < s + δ - 1 := by linarith
  have hh := gehring_truncated_distribution_bound μ ν h hm hn s δ T L C hs hδ hT hL hC htail
  rw [← ofReal_integral_eq_lintegral_ofReal
      (gehring_truncation_integrable h hm.aemeasurable hn s δ T hδ.le hT hμ)
      (Eventually.of_forall hnclip),
    ← ofReal_integral_eq_lintegral_ofReal hμ
      (Eventually.of_forall (fun x => Real.rpow_nonneg (hn x) _)),
    ← ofReal_integral_eq_lintegral_ofReal
      (gehring_truncation_integrable h hm.aemeasurable hn s δ T hδ.le hT hν)
      (Eventually.of_forall hnclip)] at hh
  have hcoef : ENNReal.ofReal δ * ENNReal.ofReal C *
      (ENNReal.ofReal (s + δ - 1))⁻¹ * ENNReal.ofReal ((2 : ℝ) ^ (s + δ - 1)) =
      ENNReal.ofReal (δ * C * (s + δ - 1)⁻¹ * (2 : ℝ) ^ (s + δ - 1)) := by
    rw [← ENNReal.ofReal_inv_of_pos hβ]
    rw [← ENNReal.ofReal_mul hδ.le, ← ENNReal.ofReal_mul (mul_nonneg hδ.le hC),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hδ.le hC) (inv_nonneg.mpr hβ.le))]
  have hniμ := hni μ
  have hniν := hni ν
  have hnis := hni' μ
  rw [hcoef, ← ENNReal.ofReal_mul (Real.rpow_nonneg hL _),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency

/-- The local tail inequality is the geometric stopping obligation; the conclusion here
uses the finite truncated integrals and a radius iteration before taking the limit. -/
private theorem gehring_local_from_tail
    (h : E2 → ℝ) (hm : Measurable h) (hn : ∀ x, 0 ≤ h x)
    (hi : IntegrableOn (fun x => h x ^ (3 / (2 : ℝ))) (disc 1))
    (C K : ℝ) (hC : 0 ≤ C) (hK : 1 ≤ K)
    (htail : ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      ∀ t : ℝ, 0 < t → K / (b - a) ^ 2 ≤ t →
        (∫⁻ x in {x | t < h x}, ENNReal.ofReal (h x ^ (3 / (2 : ℝ)))
          ∂volume.restrict (disc a)) ≤
        ENNReal.ofReal C * ENNReal.ofReal (t ^ ((3 / (2 : ℝ)) - 1)) *
          ∫⁻ x in {x | t < 2 * h x}, ENNReal.ofReal (h x)
            ∂volume.restrict (disc b)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → t < 1 →
      MemLp h (ENNReal.ofReal ((3 / (2 : ℝ)) + δ)) (volume.restrict (disc t)) := by
  obtain ⟨δ, hδ, hδ1, hsmall⟩ := gehring_coefficient_small C hC
  have hiter : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (E : ℝ → ℝ) (K I r R T : ℝ),
      0 ≤ K → 0 ≤ I → 0 < r → r < R → 0 ≤ T →
      (∀ t, r ≤ t → t < R → E t ≤ T) →
      (∀ s t, r ≤ s → s < t → t < R →
        E s ≤ (1 / 8 : ℝ) * E t + K * I / (t - s)^2) →
      E r ≤ C0 * K * I / (R - r)^2 := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeHoleFilling 0).str "native_hole_filling_radii"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent pn) (1 / 8) (by norm_num) (by norm_num)))
  obtain ⟨C0, hC0, hiter⟩ := hiter
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro t ht ht1
  let R : ℝ := (t + 1) / 2
  have htR : t < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  let H : ℝ := ∫ x in disc 1, h x ^ (3 / (2 : ℝ))
  have hH : 0 ≤ H := integral_nonneg (fun x => Real.rpow_nonneg (hn x) _)
  let B : ℝ := C0 * K * H / (R - t)^2
  have hinside (a : ℝ) (ha : a < 1) : disc a ⊆ disc 1 := Metric.ball_subset_ball ha.le
  have hi' (a : ℝ) (ha : a < 1) : IntegrableOn (fun x => h x ^ (3 / (2 : ℝ))) (disc a) :=
    hi.mono_set (hinside a ha)
  have hbound : ∀ T : ℝ, 0 ≤ T →
      (∫ x in disc t, h x ^ (3 / (2 : ℝ)) * min (h x) T ^ δ) ≤ B := by
    intro T hT
    let e : E2 → ℝ := fun x => h x ^ (3 / (2 : ℝ)) * min (h x) T ^ δ
    let E : ℝ → ℝ := fun a => ∫ x in disc a, e x
    let MT : ℝ := ∫ x in disc 1, e x
    have he : IntegrableOn e (disc 1) :=
      gehring_truncation_integrable h hm.aemeasurable hn (3 / 2) δ T hδ.le hT hi
    have hen (x : E2) : 0 ≤ e x :=
      mul_nonneg (Real.rpow_nonneg (hn x) _) (Real.rpow_nonneg (le_min (hn x) hT) _)
    have hMT : 0 ≤ MT := integral_nonneg hen
    have hmax (a : ℝ) (_hat : t ≤ a) (haR : a < R) : E a ≤ MT :=
      setIntegral_mono_set he (Eventually.of_forall hen) (hinside a (haR.trans hR1)).eventuallyLE
    have hstep (a b : ℝ) (hta : t ≤ a) (hab : a < b) (hbR : b < R) :
        E a ≤ (1 / 8 : ℝ) * E b + K * H / (b - a)^2 := by
      have ha : 0 < a := ht.trans_le hta
      have hb1 : b < 1 := hbR.trans hR1
      have ha1 : a < 1 := hab.trans hb1
      let L : ℝ := K / (b - a)^2
      have hL : 1 ≤ L := by
        apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hab))).mpr
        have hgap : b - a < 1 := by linarith
        nlinarith [sq_nonneg (b - a), sub_pos.mpr hab]
      have hbd := gehring_truncated_distribution_bound_real
        (volume.restrict (disc a)) (volume.restrict (disc b))
        h hm hn (3 / 2) δ T L C (by norm_num) hδ hT (by linarith) hC
        (hi' a ha1) (hi' b hb1) (htail a b ha hab hb1)
      have hmass : (∫ x in disc a, h x ^ (3 / (2 : ℝ))) ≤ H :=
        setIntegral_mono_set hi
          (Eventually.of_forall (fun x => Real.rpow_nonneg (hn x) _))
          (hinside a ha1).eventuallyLE
      have hmass0 : 0 ≤ ∫ x in disc a, h x ^ (3 / (2 : ℝ)) :=
        integral_nonneg (fun x => Real.rpow_nonneg (hn x) _)
      have hEb : 0 ≤ E b := integral_nonneg hen
      have hLpow : L ^ δ ≤ L := by
        simpa using Real.rpow_le_rpow_of_exponent_le hL (show δ ≤ 1 by linarith)
      have hfirst : L ^ δ * (∫ x in disc a, h x ^ (3 / (2 : ℝ))) ≤ K * H / (b - a)^2 := by
        calc
          _ ≤ L * H := mul_le_mul hLpow hmass hmass0 (by linarith)
          _ = _ := by dsimp only [L]; ring
      have hsecond : (δ * C * (3 / 2 + δ - 1)⁻¹ * (2 : ℝ) ^ (3 / 2 + δ - 1)) * E b ≤
          (1 / 8 : ℝ) * E b := mul_le_mul_of_nonneg_right (hsmall.trans (by norm_num)) hEb
      exact hbd.trans (by simpa only [add_comm] using add_le_add hfirst hsecond)
    exact hiter E K H t R MT (by linarith) hH ht htR hMT hmax hstep
  exact gehring_memLp_of_uniform_truncation h hm.aemeasurable hn (3 / 2) δ
    (by norm_num) hδ (hi' t ht1) B hbound
