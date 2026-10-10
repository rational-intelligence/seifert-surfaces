import LocalGehring
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem gehring_trim_high_average
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (h : α → ℝ) (hm : Measurable h) (hi : Integrable h μ)
    (t : ℝ) (ht : 0 ≤ t) (hh : t * μ.real univ ≤ ∫ x, h x ∂μ) :
    (∫ x, h x ∂μ) ≤ 2 * ∫ x in {x | t < 2 * h x}, h x ∂μ := by
  let S := {x | t < 2 * h x}
  have hs : MeasurableSet S := measurableSet_lt measurable_const (measurable_const.mul hm)
  have hc : (∫ x in Sᶜ, h x ∂μ) ≤ (t / 2) * μ.real univ := by
    calc
      _ ≤ ∫ x in Sᶜ, (t / 2 : ℝ) ∂μ := by
        apply integral_mono_ae hi.integrableOn (integrable_const _)
        filter_upwards [ae_restrict_mem hs.compl] with x hx
        change ¬ t < 2 * h x at hx
        linarith
      _ ≤ (t / 2) * μ.real univ := by
        rw [integral_const, smul_eq_mul, mul_comm]
        simpa only [Measure.real, Measure.restrict_apply_univ] using
          mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) (subset_univ Sᶜ)) (by linarith : 0 ≤ t / 2)
  have heq := integral_add_compl hs hi
  linarith

private theorem gehring_tail_of_stopping
    (h : E2 → ℝ) (a b t R D : ℝ) (hR : 0 < R)
    (hstop : ∀ᵐ x ∂volume, x ∈ disc a → t < h x →
      ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ Metric.ball x r ⊆ disc b ∧
        (∫⁻ y in Metric.ball x (5 * r), ENNReal.ofReal (h y ^ (3 / (2 : ℝ)))) ≤
          ENNReal.ofReal D * ENNReal.ofReal (t ^ (1 / (2 : ℝ))) *
            ∫⁻ y in Metric.ball x r ∩ {y | t < 2 * h y}, ENNReal.ofReal (h y)) :
    (∫⁻ x in {x | t < h x}, ENNReal.ofReal (h x ^ (3 / (2 : ℝ)))
        ∂volume.restrict (disc a)) ≤
      ENNReal.ofReal D * ENNReal.ofReal (t ^ (1 / (2 : ℝ))) *
        ∫⁻ x in {x | t < 2 * h x}, ENNReal.ofReal (h x) ∂volume.restrict (disc b) := by
  classical
  let S := {x : E2 | x ∈ disc a ∧ t < h x ∧ ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
    Metric.ball x r ⊆ disc b ∧
      (∫⁻ y in Metric.ball x (5 * r), ENNReal.ofReal (h y ^ (3 / (2 : ℝ)))) ≤
        ENNReal.ofReal D * ENNReal.ofReal (t ^ (1 / (2 : ℝ))) *
          ∫⁻ y in Metric.ball x r ∩ {y | t < 2 * h y}, ENNReal.ofReal (h y)}
  have hs : ∀ x : S, ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ Metric.ball (x : E2) r ⊆ disc b ∧
      (∫⁻ y in Metric.ball (x : E2) (5 * r), ENNReal.ofReal (h y ^ (3 / (2 : ℝ)))) ≤
        ENNReal.ofReal D * ENNReal.ofReal (t ^ (1 / (2 : ℝ))) *
          ∫⁻ y in Metric.ball (x : E2) r ∩ {y | t < 2 * h y}, ENNReal.ofReal (h y) :=
    fun x => x.property.2.2
  choose r hr hbound hinside hmass using hs
  obtain ⟨V, _, hdisj, hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    (univ : Set S) (fun x => (x : E2)) r R (fun x _ => hbound x) 5 (by norm_num)
  have hcount : V.Countable := hdisj.countable_of_isOpen
    (fun _ _ => Metric.isOpen_ball) (fun x _ => ⟨x, Metric.mem_ball_self (hr x)⟩)
  letI : Countable V := hcount.to_subtype
  let B (v : V) := Metric.ball ((v : S) : E2) (r v)
  let B5 (v : V) := Metric.ball ((v : S) : E2) (5 * r v)
  have hcov : (disc a ∩ {x | t < h x}) ≤ᵐ[volume] ⋃ v : V, B5 v := by
    filter_upwards [hstop] with x hx hxS
    have hx' : x ∈ S := ⟨hxS.1, hxS.2, hx hxS.1 hxS.2⟩
    obtain ⟨v, hv, hsub⟩ := hcover ⟨x, hx'⟩ (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨v, hv⟩, hsub (Metric.mem_ball_self (hr ⟨x, hx'⟩))⟩
  have hd : Pairwise (fun v w : V => Disjoint
      (B v ∩ {x | t < 2 * h x}) (B w ∩ {x | t < 2 * h x})) := by
    intro v w hvw
    exact (hdisj v.property w.property (Subtype.coe_ne_coe.mpr hvw)).mono inter_subset_left inter_subset_left
  have hsum : (∑' v : V, ∫⁻ x in B v ∩ {x | t < 2 * h x}, ENNReal.ofReal (h x)) ≤
      ∫⁻ x in disc b ∩ {x | t < 2 * h x}, ENNReal.ofReal (h x) := by
    -- Disjointness is measured for the original open balls, so no level-set measurability is needed here.
    have hdb : Pairwise (fun v w : V => Disjoint (B v) (B w)) := hdisj.subtype _ _
    have heq := lintegral_iUnion (μ := volume.restrict {x | t < 2 * h x})
      (fun v : V => Metric.isOpen_ball.measurableSet) hdb (fun x => ENNReal.ofReal (h x))
    simp only [Measure.restrict_restrict Metric.isOpen_ball.measurableSet] at heq
    rw [← heq, Measure.restrict_restrict (isOpen_iUnion (fun _ => Metric.isOpen_ball)).measurableSet]
    apply lintegral_mono_set
    exact fun x hx => ⟨by rcases mem_iUnion.mp hx.1 with ⟨v, hv⟩; exact hinside v hv, hx.2⟩
  rw [Measure.restrict_restrict' (show MeasurableSet (disc a) from Metric.isOpen_ball.measurableSet),
    Measure.restrict_restrict' (show MeasurableSet (disc b) from Metric.isOpen_ball.measurableSet)]
  rw [inter_comm {x | t < h x}, inter_comm {x | t < 2 * h x}]
  calc
    _ ≤ ∫⁻ x in ⋃ v : V, B5 v, ENNReal.ofReal (h x ^ (3 / (2 : ℝ))) := lintegral_mono_set' hcov
    _ ≤ ∑' v : V, ∫⁻ x in B5 v, ENNReal.ofReal (h x ^ (3 / (2 : ℝ))) := lintegral_iUnion_le _ _
    _ ≤ ∑' v : V, ENNReal.ofReal D * ENNReal.ofReal (t ^ (1 / (2 : ℝ))) *
        ∫⁻ x in B v ∩ {x | t < 2 * h x}, ENNReal.ofReal (h x) := ENNReal.tsum_le_tsum (fun v => hmass v)
    _ = ENNReal.ofReal D * ENNReal.ofReal (t ^ (1 / (2 : ℝ))) *
        ∑' v : V, ∫⁻ x in B v ∩ {x | t < 2 * h x}, ENNReal.ofReal (h x) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul_right hsum _

private theorem planar_ball_closedBall_ae (x : E2) (r : ℝ) :
    Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
  apply ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
    (by simp) Metric.isOpen_ball.measurableSet.nullMeasurableSet (isCompact_closedBall x r).measure_ne_top

private theorem gehring_stopping_radius
    (h : E2 → ℝ) (hi : Integrable h) (hn : ∀ x, 0 ≤ h x)
    (R t : ℝ) (hR : 0 < R)
    (hlarge : (∫ x, h x) ≤ t * (R ^ 2 * Real.pi)) :
    ∀ᵐ x ∂volume, t < h x → ∃ r : ℝ, 0 < r ∧ r ≤ R / 10 ∧
      t * volume.real (Metric.ball x r) < ∫ y in Metric.ball x r, h y ∧
      (∫ y in Metric.ball x (10 * r), h y) ≤
        t * volume.real (Metric.ball x (10 * r)) := by
  let ρ : ℕ → ℝ := fun n => R * (1 / 10 : ℝ)^n
  have hρ (n : ℕ) : 0 < ρ n := mul_pos hR (pow_pos (by norm_num) n)
  have hlim : Tendsto ρ atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 10) (by norm_num : (1 / (10 : ℝ)) < 1)).const_mul R
    · exact Eventually.of_forall hρ
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hi.locallyIntegrable 1] with x hx
  intro hxt
  have hcon := hx (fun _ : ℕ => x) ρ hlim
    (Eventually.of_forall (fun n => Metric.mem_closedBall_self (by simpa using (hρ n).le)))
  have hav : Tendsto (fun n => ⨍ y in Metric.ball x (ρ n), h y) atTop (𝓝 (h x)) := by
    convert hcon using 1
    ext n
    rw [Measure.restrict_congr_set (planar_ball_closedBall_ae x (ρ n))]
  have hvol (r : ℝ) (hr : 0 ≤ r) : volume.real (Metric.ball x r) = r ^ 2 * Real.pi := by
    simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_pos.le]
  have hex : ∃ n : ℕ, t * volume.real (Metric.ball x (ρ n)) < ∫ y in Metric.ball x (ρ n), h y := by
    obtain ⟨n, hn⟩ := (hav.eventually (Ioi_mem_nhds hxt)).exists
    use n
    rw [setAverage_eq, smul_eq_mul, ← div_eq_inv_mul] at hn
    exact (lt_div_iff₀ (by rw [hvol _ (hρ n).le]; positivity)).mp hn
  let n : ℕ := Nat.find hex
  have hh : t * volume.real (Metric.ball x (ρ n)) < ∫ y in Metric.ball x (ρ n), h y := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro heq
    have hh0 : t * (R ^ 2 * Real.pi) < ∫ y in Metric.ball x R, h y := by
      simpa only [heq, ρ, pow_zero, mul_one, hvol R hR.le] using hh
    have hmass := setIntegral_le_integral hi (Eventually.of_forall hn) (s := Metric.ball x R)
    linarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hprev : (∫ y in Metric.ball x (ρ m), h y) ≤ t * volume.real (Metric.ball x (ρ m)) :=
    le_of_not_gt (Nat.find_min hex (by simpa [n, hm] using Nat.lt_succ_self m))
  have hρstep : 10 * ρ n = ρ m := by rw [hm]; dsimp only [ρ]; rw [pow_succ]; ring
  refine ⟨ρ n, hρ n, ?_, hh, ?_⟩
  · rw [hm]
    dsimp only [ρ]
    rw [pow_succ]
    have hpow : (1 / 10 : ℝ)^m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  · simpa only [hρstep] using hprev

private theorem gehring_stop_mass
    (h : E2 → ℝ) (hm : Measurable h) (hi : Integrable h)
    (hn : ∀ x, 0 ≤ h x)
    (hs : Integrable (fun x => h x ^ (3 / (2 : ℝ))))
    (A t r : ℝ) (hA : 0 ≤ A) (ht : 0 < t) (hr : 0 < r) (x : E2)
    (hlo : t * volume.real (Metric.ball x r) < ∫ y in Metric.ball x r, h y)
    (hup : (∫ y in Metric.ball x (10 * r), h y) ≤
      t * volume.real (Metric.ball x (10 * r)))
    (hrev : (∫ y in Metric.ball x (5 * r), h y ^ (3 / (2 : ℝ))) ≤
      A / (5 * r) * (∫ y in Metric.ball x (10 * r), h y) ^ (3 / (2 : ℝ))) :
    (∫⁻ y in Metric.ball x (5 * r), ENNReal.ofReal (h y ^ (3 / (2 : ℝ)))) ≤
      ENNReal.ofReal (2 * A * ((100 * Real.pi) ^ (3 / (2 : ℝ))) / (5 * Real.pi)) *
        ENNReal.ofReal (t ^ (1 / (2 : ℝ))) *
          ∫⁻ y in Metric.ball x r ∩ {y | t < 2 * h y}, ENNReal.ofReal (h y) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball x r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have htrim := gehring_trim_high_average (volume.restrict (Metric.ball x r))
    h hm hi.integrableOn t ht.le (by simpa using hlo.le)
  have htrim' : (∫ y in Metric.ball x r, h y) ≤
      2 * ∫ y in Metric.ball x r ∩ {y | t < 2 * h y}, h y := by
    calc
      _ ≤ 2 * ∫ y in {y | t < 2 * h y}, h y ∂(volume.restrict (Metric.ball x r)) := htrim
      _ = _ := by
        change 2 * ∫ y, h y ∂((volume.restrict (Metric.ball x r)).restrict {y | t < 2 * h y}) = _
        rw [Measure.restrict_restrict' Metric.isOpen_ball.measurableSet, inter_comm]
  have hvol (R : ℝ) (hR : 0 ≤ R) : volume.real (Metric.ball x R) = R ^ 2 * Real.pi := by
    simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hR, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [hvol r hr.le] at hlo
  rw [hvol (10 * r) (by positivity)] at hup
  have hpow : (t * ((10 * r)^2 * Real.pi)) ^ (3 / (2 : ℝ)) =
      (100 * Real.pi) ^ (3 / (2 : ℝ)) * (t * t ^ (1 / (2 : ℝ))) * (r^2 * r) := by
    have htp : t ^ (3 / (2 : ℝ)) = t * t ^ (1 / (2 : ℝ)) := by
      rw [show (3 / (2 : ℝ)) = 1 + 1 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one]
    have hrp : (r^2) ^ (3 / (2 : ℝ)) = r^2 * r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      norm_num [pow_succ]
    rw [show t * ((10 * r)^2 * Real.pi) = (100 * Real.pi) * t * r^2 by ring]
    rw [Real.mul_rpow (mul_nonneg (by positivity) ht.le) (sq_nonneg _),
      Real.mul_rpow (by positivity) ht.le, htp, hrp]
  have hbd : (∫ y in Metric.ball x (5 * r), h y ^ (3 / (2 : ℝ))) ≤
      (2 * A * ((100 * Real.pi) ^ (3 / (2 : ℝ))) / (5 * Real.pi)) *
        t ^ (1 / (2 : ℝ)) * ∫ y in Metric.ball x r ∩ {y | t < 2 * h y}, h y := by
    calc
      _ ≤ A / (5 * r) * (t * ((10 * r)^2 * Real.pi)) ^ (3 / (2 : ℝ)) :=
        hrev.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (integral_nonneg hn) hup (by norm_num)) (by positivity))
      _ = (A * ((100 * Real.pi) ^ (3 / (2 : ℝ))) / (5 * Real.pi)) *
          t ^ (1 / (2 : ℝ)) * (t * (r^2 * Real.pi)) := by
        rw [hpow]
        field_simp
      _ ≤ (A * ((100 * Real.pi) ^ (3 / (2 : ℝ))) / (5 * Real.pi)) *
          t ^ (1 / (2 : ℝ)) *
          (2 * ∫ y in Metric.ball x r ∩ {y | t < 2 * h y}, h y) :=
        mul_le_mul_of_nonneg_left (hlo.le.trans htrim') (by positivity)
      _ = _ := by ring
  rw [← ofReal_integral_eq_lintegral_ofReal hs.integrableOn
    (Eventually.of_forall (fun y => Real.rpow_nonneg (hn y) _)),
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (Eventually.of_forall hn)]
  simpa only [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * A * ((100 * Real.pi) ^ (3 / (2 : ℝ))) / (5 * Real.pi)),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * A * ((100 * Real.pi) ^ (3 / (2 : ℝ))) / (5 * Real.pi)) * t ^ (1 / (2 : ℝ)))] using
    ENNReal.ofReal_le_ofReal hbd

private theorem gehring_local_reverse_holder
    (h : E2 → ℝ) (hm : Measurable h) (hn : ∀ x, 0 ≤ h x)
    (hi : Integrable h) (hs : Integrable (fun x => h x ^ (3 / (2 : ℝ))))
    (A : ℝ) (hA : 0 ≤ A)
    (hrev : ∀ (x : E2) (r : ℝ), 0 < r → Metric.closedBall x (2 * r) ⊆ disc 1 →
      (∫ y in Metric.ball x r, h y ^ (3 / (2 : ℝ))) ≤
        A / r * (∫ y in Metric.ball x (2 * r), h y) ^ (3 / (2 : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → t < 1 →
      MemLp h (ENNReal.ofReal ((3 / (2 : ℝ)) + δ)) (volume.restrict (disc t)) := by
  let D := 2 * A * ((100 * Real.pi) ^ (3 / (2 : ℝ))) / (5 * Real.pi)
  let K := 1 + 4 * (∫ x, h x) / Real.pi
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hK : 1 ≤ K := by
    dsimp only [K]
    have hmass : 0 ≤ ∫ x, h x := integral_nonneg hn
    have hq : 0 ≤ 4 * (∫ x, h x) / Real.pi := by positivity
    linarith
  have htail : ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      ∀ t : ℝ, 0 < t → K / (b - a) ^ 2 ≤ t →
        (∫⁻ x in {x | t < h x}, ENNReal.ofReal (h x ^ (3 / (2 : ℝ)))
          ∂volume.restrict (disc a)) ≤
        ENNReal.ofReal D * ENNReal.ofReal (t ^ ((3 / (2 : ℝ)) - 1)) *
          ∫⁻ x in {x | t < 2 * h x}, ENNReal.ofReal (h x)
            ∂volume.restrict (disc b) := by
    intro a b ha hab hb t ht hthr
    let R := (b - a) / 2
    have hR : 0 < R := by dsimp [R]; linarith
    have hlarge : (∫ x, h x) ≤ t * (R ^ 2 * Real.pi) := by
      have hthr' := (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hab))).mp hthr
      have hpi := Real.pi_pos
      dsimp only [K] at hthr'
      have hmass : 0 ≤ ∫ x, h x := integral_nonneg hn
      have haux : 4 * (∫ x, h x) ≤ t * (b - a)^2 * Real.pi := by
        have hdiv : 4 * (∫ x, h x) / Real.pi ≤ t * (b - a)^2 := by linarith
        exact (div_le_iff₀ hpi).mp hdiv
      dsimp only [R]
      nlinarith
    have hstop := gehring_stopping_radius h hi hn R t hR hlarge
    have hstop' : ∀ᵐ x ∂volume, x ∈ disc a → t < h x →
      ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ Metric.ball x r ⊆ disc b ∧
        (∫⁻ y in Metric.ball x (5 * r), ENNReal.ofReal (h y ^ (3 / (2 : ℝ)))) ≤
          ENNReal.ofReal D * ENNReal.ofReal (t ^ (1 / (2 : ℝ))) *
            ∫⁻ y in Metric.ball x r ∩ {y | t < 2 * h y}, ENNReal.ofReal (h y) := by
      filter_upwards [hstop] with x hx hxa hxt
      obtain ⟨r, hr, hrR, hlo, hup⟩ := hx hxt
      have hinside : Metric.closedBall x (10 * r) ⊆ disc b := by
        intro y hy
        have hxnorm : ‖x‖ < a := by simpa only [disc, Metric.mem_ball, dist_zero_right] using hxa
        have hydist : ‖y - x‖ ≤ 10 * r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
        have hynorm := norm_add_le (y - x) x
        rw [sub_add_cancel] at hynorm
        change dist y 0 < b
        rw [dist_zero_right]
        dsimp only [R] at hrR
        linarith
      refine ⟨r, hr, by linarith, (Metric.ball_subset_closedBall.trans
        ((Metric.closedBall_subset_closedBall (by linarith : r ≤ 10 * r)).trans hinside)), ?_⟩
      have hrev' : (∫ y in Metric.ball x (5 * r), h y ^ (3 / (2 : ℝ))) ≤
          A / (5 * r) * (∫ y in Metric.ball x (10 * r), h y) ^ (3 / (2 : ℝ)) := by
        have hh := hrev x (5 * r) (by positivity)
          (by convert hinside.trans (Metric.ball_subset_ball hb.le) using 1 <;> congr 1 <;> ring)
        simpa only [show 2 * (5 * r) = 10 * r by ring] using hh
      exact gehring_stop_mass h hm hi hn hs A t r hA ht hr x hlo hup hrev'
    simpa only [show (3 / (2 : ℝ)) - 1 = 1 / 2 by norm_num] using
      gehring_tail_of_stopping h a b t R D hR hstop'
  run_tac do
    let pn := (Lean.Name.num `_private.LocalGehring 0).str "gehring_local_from_tail"
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact $(Lean.mkIdent pn) $(Lean.mkIdent `h) $(Lean.mkIdent `hm) $(Lean.mkIdent `hn)
        ($(Lean.mkIdent `hs)).integrableOn $(Lean.mkIdent `D) $(Lean.mkIdent `K)
        $(Lean.mkIdent `hD) $(Lean.mkIdent `hK) $(Lean.mkIdent `htail)))
