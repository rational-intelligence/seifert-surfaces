import CampanatoIteration
import ClassicalDerivative
import BallPoincare
import BridgeHelpers
import DifferentialGeometry.External.DeGiorgi.UnitBallApproximationCore.Profiles
import CampanatoVector.Bound

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder
open CampanatoVector

theorem campanato_holder_representative (R : ℝ) (hR : 0 < R)
    (β : NNReal) (hβ : 0 < β) (hβone : β < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (center : V) (G : V → V),
      MemLp G 2 (volume.restrict (Metric.ball center R)) →
      ∀ M : ℝ, 0 ≤ M →
      CampanatoBound G (Metric.ball center (3 * R / 4)) (R / 8) β M →
      ∃ (G' : V → V) (K : NNReal),
        G' =ᵐ[volume.restrict (Metric.ball center (R / 2))] G ∧
        (K : ℝ) ≤ C * Real.sqrt M ∧
        HolderOnWith K β G' (Metric.ball center (R / 2)) ∧
        (∀ x ∈ Metric.ball center (R / 2),
          ‖G' x‖ ≤ C * (Real.sqrt (energy G center R) + Real.sqrt M)) := by
  let A := ((R / 16) ^ 3 * unitBallVolume 3)⁻¹ *
    Real.sqrt ((R / 16) ^ 3 * unitBallVolume 3)
  let B := campanatoLimitConst 3 β * (R / 16) ^ (β : ℝ)
  let H := 32 * campanatoHolderConst 3 β
  have hβr : (0 : ℝ) < β := by exact_mod_cast hβ
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (by positivity) unitBallVolume_pos.le))
      (Real.sqrt_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (campanatoLimitConst_nonneg hβr)
    (Real.rpow_nonneg (by positivity) _)
  have hH : 0 ≤ H := mul_nonneg (by norm_num) (campanatoHolderConst_nonneg hβr)
  refine ⟨1 + A + B + H, by linarith, ?_⟩
  intro center G hG M hM hcamp
  let K : NNReal := Real.toNNReal (H * Real.sqrt M)
  have hK : (K : ℝ) = H * Real.sqrt M := Real.coe_toNNReal _
    (mul_nonneg hH (Real.sqrt_nonneg M))
  refine ⟨campanatoLimit G, K, limit_ae_eq_local hR hβ hM hG hcamp, ?_, ?_, ?_⟩
  · rw [hK]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg M)
  · intro x hx y hy
    have hb := limit_pair_global hR hβ hM hG hcamp hx hy
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg β.coe_nonneg,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_eq_norm, hK]
    exact hb
  · intro x hx
    have hb := limit_sup_bound hR hβ hM hG hcamp hx
    change ‖campanatoLimit G x‖ ≤ A * Real.sqrt (energy G center R) + B * Real.sqrt M at hb
    calc ‖campanatoLimit G x‖ ≤ A * Real.sqrt (energy G center R) + B * Real.sqrt M := hb
      _ ≤ (1 + A + B + H) * Real.sqrt (energy G center R) +
          (1 + A + B + H) * Real.sqrt M :=
        add_le_add (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
          (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
      _ = _ := by ring

end SeifertSurfaces.WeakSchauder

namespace SeifertSurfaces.WeakSchauder
open Filter
set_option maxHeartbeats 3000000
theorem caccioppoli_from_weak_equation (κ Λ : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (center : V) (R r : ℝ), 0 < r → r < R →
      ∀ (a : V → Mat), CoefficientBounds a (Metric.ball center R) κ Λ →
      ∀ (v : V → ℝ) (hv : H1Witness v (Metric.ball center R)),
      WeakEquation a hv →
      energy hv.weakGrad center r ≤ C / (R - r) ^ 2 *
        (∫ y in Metric.ball center R, |v y| ^ 2) := by
  let C := 16 * Λ ^ 2 * (DeGiorgi.Mst : ℝ) ^ 2 / κ ^ 2 + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro c R r hr hrR a ha v hv hw
  let μ := volume.restrict (Metric.ball c R)
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  obtain ⟨ηc, -⟩ := DeGiorgi.Cutoff.exists c hr hrs
  let η := ηc.toFun
  let B := 2 * (DeGiorgi.Mst : ℝ) * (R - r)⁻¹
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := ηc.smooth
  have hηb : ∀ x, |η x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (ηc.nonneg x)]
    exact ηc.le_one x
  have hηgrad : ∀ x, ‖fderiv ℝ η x‖ ≤ B := by
    intro x
    have hm : s - r = (R - r) / 2 := by dsimp [s]; ring
    calc
      _ ≤ (DeGiorgi.Mst : ℝ) * (s - r)⁻¹ := ηc.grad_bound x
      _ = B := by rw [hm]; dsimp [B]; field_simp
  let hηv := hv.mulSmoothBoundedP (by norm_num) Metric.isOpen_ball hη
    (by norm_num : (0 : ℝ) ≤ 1) hB hηb hηgrad
  let ht := hηv.mulSmoothBoundedP (by norm_num) Metric.isOpen_ball hη
    (by norm_num : (0 : ℝ) ≤ 1) hB hηb hηgrad
  have hts : tsupport (fun x => η x * (η x * v x)) ⊆ Metric.ball c R :=
    (tsupport_mul_subset_left (f := η) (g := fun x => η x * v x)).trans
      (ηc.support_subset.trans (Metric.closedBall_subset_ball hsR))
  have htc : HasCompactSupport (fun x => η x * (η x * v x)) :=
    (isCompact_closedBall c s).of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_mul_subset_left (f := η) (g := fun x => η x * v x)).trans ηc.support_subset)
  have ht0 : DeGiorgi.MemH01 (fun x => η x * (η x * v x)) (Metric.ball c R) := by
    simpa using DeGiorgi.memW01p_of_memW1p_of_tsupport_subset Metric.isOpen_ball
      (by norm_num : (1 : ℝ) < 2) (by simpa using ht.memW1p) htc hts
  have hgrad (x : V) : ht.weakGrad x =
      η x ^ 2 • hv.weakGrad x + (2 * η x * v x) • classicalGradient η x := by
    ext i
    simp [ht, hηv, DeGiorgi.MemW1pWitness.mulSmoothBoundedP, classicalGradient,
      PiLp.toLp_apply, smul_eq_mul]
    ring
  let G := fun x => η x • hv.weakGrad x
  have hG : MemLp G 2 μ := by
    apply MemLp.of_le_mul (g := hv.weakGrad) (c := 1) hv.weakGrad_memLp
    · exact hη.continuous.aestronglyMeasurable.smul hv.weakGrad_memLp.aestronglyMeasurable
    · exact Eventually.of_forall fun x => by
        simpa [G, norm_smul, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_right (hηb x) (norm_nonneg (hv.weakGrad x))
  have hW : Integrable (fun x => ‖G x‖ ^ 2) μ := hG.norm.integrable_sq
  have hV : Integrable (fun x => |v x| ^ 2) μ := by
    simpa only [Real.norm_eq_abs] using hv.memLp.norm.integrable_sq
  have hweak := hw _ ht0 ht
  let F := fun x => DeGiorgi.matMulE (a x) (hv.weakGrad x)
  let Q := fun x => inner ℝ (F x) (ht.weakGrad x)
  have hQi : Integrable Q μ := hweak.1
  have hQz : (∫ x, Q x ∂μ) = 0 := hweak.2
  have hpoint : ∀ᵐ x ∂μ,
      (κ ^ 2 / 2) * ‖G x‖ ^ 2 ≤ κ * Q x + 2 * Λ ^ 2 * B ^ 2 * |v x| ^ 2 := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hn : 0 ≤ η x := ηc.nonneg x
    have hc := ha.coercive x hx (hv.weakGrad x)
    rw [real_inner_comm] at hc
    have hcm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ κ * η x ^ 2)
    have hm := ha.mixed x hx (hv.weakGrad x) (classicalGradient η x)
    have hgη : ‖classicalGradient η x‖ ≤ B := by
      rw [classicalGradient_norm]
      exact hηgrad x
    have hΛ0 : 0 ≤ Λ := (hκ.trans_le hΛ).le
    have hb : |inner ℝ (F x) (classicalGradient η x)| ≤ Λ * ‖hv.weakGrad x‖ * B :=
      hm.trans (mul_le_mul_of_nonneg_left hgη (mul_nonneg hΛ0 (norm_nonneg _)))
    have habs : |(2 * η x * v x) * inner ℝ (F x) (classicalGradient η x)| ≤
        2 * η x * |v x| * (Λ * ‖hv.weakGrad x‖ * B) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
        abs_of_nonneg hn]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    have hcross := neg_le_of_abs_le habs
    have hcrossκ := mul_le_mul_of_nonneg_left hcross hκ.le
    have hqe : Q x = η x ^ 2 * inner ℝ (F x) (hv.weakGrad x) +
        (2 * η x * v x) * inner ℝ (F x) (classicalGradient η x) := by
      dsimp [Q]
      rw [hgrad, inner_add_right, inner_smul_right, inner_smul_right]
    have hge : ‖G x‖ ^ 2 = η x ^ 2 * ‖hv.weakGrad x‖ ^ 2 := by
      simp [G, norm_smul, Real.norm_eq_abs, abs_of_nonneg hn, mul_pow]
    rw [hge, hqe]
    nlinarith only [hcm, hcrossκ,
      sq_nonneg (κ * η x * ‖hv.weakGrad x‖ - 2 * Λ * B * |v x|)]
  have hi := integral_mono_ae (hW.const_mul (κ ^ 2 / 2))
    ((hQi.const_mul κ).add (hV.const_mul (2 * Λ ^ 2 * B ^ 2))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (hQi.const_mul κ)
    (hV.const_mul (2 * Λ ^ 2 * B ^ 2)), integral_const_mul, integral_const_mul, hQz,
    mul_zero, zero_add] at hi
  have hbound : (∫ x, ‖G x‖ ^ 2 ∂μ) ≤ 4 * Λ ^ 2 * B ^ 2 / κ ^ 2 *
      (∫ x, |v x| ^ 2 ∂μ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hκ)).mpr
    nlinarith only [hi]
  have hsub := Metric.ball_subset_ball (x := c) hrR.le
  have hloc : energy hv.weakGrad c r ≤ (∫ x, ‖G x‖ ^ 2 ∂μ) := by
    calc
      _ = ∫ x in Metric.ball c r, ‖G x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
        simp [G, η, ηc.eq_one x hx]
      _ ≤ _ := integral_mono_measure (Measure.restrict_mono_set volume hsub)
        (Eventually.of_forall fun x => sq_nonneg _) hW
  have hcoeff : 4 * Λ ^ 2 * B ^ 2 / κ ^ 2 ≤ C / (R - r) ^ 2 := by
    dsimp [B, C]
    have hpos : 0 < (R - r) ^ 2 := sq_pos_of_pos (sub_pos.mpr hrR)
    apply (le_div_iff₀ hpos).mpr
    have he : 4 * Λ ^ 2 * (2 * (DeGiorgi.Mst : ℝ) * (R - r)⁻¹) ^ 2 /
        κ ^ 2 * (R - r) ^ 2 = 16 * Λ ^ 2 * (DeGiorgi.Mst : ℝ) ^ 2 / κ ^ 2 := by
      field_simp [(sub_pos.mpr hrR).ne']
      <;> ring
    rw [he]
    linarith
  exact hloc.trans (hbound.trans (mul_le_mul_of_nonneg_right hcoeff
    (integral_nonneg fun x => sq_nonneg _)))


theorem weak_divergence_schauder_gain
    (κ Λ R : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (hR : 0 < R)
    (H α : NNReal) (hα : 0 < α) (hαone : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (center : V) (a : V → Mat),
      CoefficientBounds a (Metric.ball center R) κ Λ →
      CoefficientHolder a (Metric.ball center R) H α →
      ∀ (v : V → ℝ) (hv : H1Witness v (Metric.ball center R)),
      ContinuousOn v (Metric.ball center R) → WeakEquation a hv →
      ContDiffOn ℝ 1 v (Metric.ball center (R / 2)) ∧
      (∀ x ∈ Metric.ball center (R / 2),
        ‖fderiv ℝ v x‖ ≤ C * Real.sqrt (energy hv.weakGrad center R)) ∧
      ∃ K : NNReal, (K : ℝ) ≤ C * Real.sqrt (energy hv.weakGrad center R) ∧
        HolderOnWith K (α / 2) (fderiv ℝ v) (Metric.ball center (R / 2)) := by
  have hβ : 0 < α / 2 := by positivity
  have hβone : α / 2 < 1 := by
    have ha : (α : ℝ) < 1 := hαone
    have hb : ((α / 2 : NNReal) : ℝ) < 1 := by
      simp only [NNReal.coe_div, NNReal.coe_ofNat]
      linarith
    exact hb
  obtain ⟨A, hA, hcamp⟩ := gradient_campanato_from_weak_equation κ Λ R hκ hΛ hR H α hα hαone
  obtain ⟨B, hB, hrep⟩ := campanato_holder_representative R hR (α / 2) hβ hβone
  refine ⟨B * (1 + Real.sqrt A), by positivity, ?_⟩
  intro center a ha hah v hv hcont hw
  have hE : 0 ≤ energy hv.weakGrad center R := integral_nonneg fun _ => sq_nonneg _
  have hM : 0 ≤ A * energy hv.weakGrad center R := mul_nonneg hA.le hE
  obtain ⟨G, K, hGae, hK, hholder, hsup⟩ :=
    hrep center hv.weakGrad hv.weakGrad_memLp _ hM (hcamp center a ha hah v hv hw)
  have hsub : Metric.ball center (R / 2) ⊆ Metric.ball center R :=
    Metric.ball_subset_ball (by linarith)
  let hs : H1Witness v (Metric.ball center (R / 2)) := hv.restrict Metric.isOpen_ball hsub
  have hGc : ContinuousOn G (Metric.ball center (R / 2)) := hholder.continuousOn hβ
  have hder := classical_derivative_of_continuous_weak_gradient _ Metric.isOpen_ball v hs
    (hcont.mono hsub) G hGc hGae
  have hfd : ∀ x ∈ Metric.ball center (R / 2), fderiv ℝ v x = innerSL ℝ (G x) :=
    fun x hx => (hder.1 x hx).fderiv
  have hsqrt : Real.sqrt (A * energy hv.weakGrad center R) =
      Real.sqrt A * Real.sqrt (energy hv.weakGrad center R) := Real.sqrt_mul hA.le _
  refine ⟨hder.2, ?_, K, ?_, ?_⟩
  · intro x hx
    rw [hfd x hx, innerSL_apply_norm]
    calc
      ‖G x‖ ≤ B * (Real.sqrt (energy hv.weakGrad center R) +
        Real.sqrt (A * energy hv.weakGrad center R)) := hsup x hx
      _ = _ := by rw [hsqrt]; ring
  · rw [hsqrt] at hK
    have hp : 0 ≤ B * Real.sqrt (energy hv.weakGrad center R) := by positivity
    nlinarith only [hK, hp]
  · intro x hx y hy
    rw [hfd x hx, hfd y hy]
    have hd : edist (innerSL ℝ (G x)) (innerSL ℝ (G y)) = edist (G x) (G y) := by
      simp only [edist_dist, dist_eq_norm]
      rw [← map_sub, innerSL_apply_norm]
    rw [hd]
    exact hholder x hx y hy


theorem weak_divergence_schauder_gain_from_L2
    (κ Λ R : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (hR : 0 < R)
    (H α : NNReal) (hα : 0 < α) (hαone : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (center : V) (a : V → Mat),
      CoefficientBounds a (Metric.ball center R) κ Λ →
      CoefficientHolder a (Metric.ball center R) H α →
      ∀ (v : V → ℝ) (hv : H1Witness v (Metric.ball center R)),
      ContinuousOn v (Metric.ball center R) → WeakEquation a hv →
      ContDiffOn ℝ 1 v (Metric.ball center (R / 2)) ∧
      (∀ x ∈ Metric.ball center (R / 2),
        ‖fderiv ℝ v x‖ ≤ C * Real.sqrt (∫ y in Metric.ball center R, |v y| ^ 2)) ∧
      ∃ K : NNReal, (K : ℝ) ≤ C * Real.sqrt (∫ y in Metric.ball center R, |v y| ^ 2) ∧
        HolderOnWith K (α / 2) (fderiv ℝ v) (Metric.ball center (R / 2)) := by
  obtain ⟨A, hA, hgain⟩ := weak_divergence_schauder_gain κ Λ (R / 4) hκ hΛ
    (by linarith) H α hα hαone
  obtain ⟨Q, hQ, hcacc⟩ := caccioppoli_from_weak_equation κ Λ hκ hΛ
  obtain ⟨A₀, hA₀, hregular⟩ := weak_divergence_schauder_gain κ Λ R hκ hΛ hR H α hα hαone
  let L := A * Real.sqrt (Q / (R / 4) ^ 2)
  let D := L + 2 * L * ((R / 8) ^ ((α / 2 : NNReal) : ℝ))⁻¹
  have hL : 0 < L := by dsimp [L]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro c a ha hah v hv hcont hw
  let I := ∫ y in Metric.ball c R, |v y| ^ 2
  have hI : 0 ≤ I := integral_nonneg fun _ => sq_nonneg _
  have hInt : Integrable (fun y => |v y| ^ 2) (volume.restrict (Metric.ball c R)) := by
    simpa only [Real.norm_eq_abs] using hv.memLp.norm.integrable_sq
  have local_gain (x : V) (hx : x ∈ Metric.ball c (R / 2)) :
      (∀ z ∈ Metric.ball x (R / 8), ‖fderiv ℝ v z‖ ≤ L * Real.sqrt I) ∧
      ∃ K : NNReal, (K : ℝ) ≤ L * Real.sqrt I ∧
        HolderOnWith K (α / 2) (fderiv ℝ v) (Metric.ball x (R / 8)) := by
    have houter : Metric.ball x (R / 2) ⊆ Metric.ball c R := by
      intro y hy
      have ht := dist_triangle y x c
      have hxc := Metric.mem_ball.mp hx
      have hyx := Metric.mem_ball.mp hy
      exact Metric.mem_ball.mpr (by linarith)
    have hinner : Metric.ball x (R / 4) ⊆ Metric.ball c R :=
      (Metric.ball_subset_ball (by linarith : R / 4 ≤ R / 2)).trans houter
    obtain ⟨ho, hgo, hwo⟩ := weak_equation_restrict a _ Metric.isOpen_ball v hv hw x
      (R / 2) (by linarith) houter
    obtain ⟨hi, hgi, hwi⟩ := weak_equation_restrict a _ Metric.isOpen_ball v hv hw x
      (R / 4) (by linarith) hinner
    have hao : CoefficientBounds a (Metric.ball x (R / 2)) κ Λ :=
      ⟨fun i j => (ha.measurable i j).mono_measure (Measure.restrict_mono_set volume houter),
        fun z hz => ha.coercive z (houter hz), fun z hz => ha.mixed z (houter hz)⟩
    have hai : CoefficientBounds a (Metric.ball x (R / 4)) κ Λ :=
      ⟨fun i j => (ha.measurable i j).mono_measure (Measure.restrict_mono_set volume hinner),
        fun z hz => ha.coercive z (hinner hz), fun z hz => ha.mixed z (hinner hz)⟩
    have hahi : CoefficientHolder a (Metric.ball x (R / 4)) H α :=
      fun i j => (hah i j).mono hinner
    have he := hcacc x (R / 2) (R / 4) (by linarith) (by linarith) a hao v ho hwo
    have hei : energy hi.weakGrad x (R / 4) ≤ Q / (R / 4) ^ 2 * I := by
      have heq : energy hi.weakGrad x (R / 4) = energy ho.weakGrad x (R / 4) := by
        unfold energy
        simp_rw [hgi, hgo]
      rw [heq]
      have hmono : (∫ y in Metric.ball x (R / 2), |v y| ^ 2) ≤ I :=
        integral_mono_measure (Measure.restrict_mono_set volume houter)
          (Eventually.of_forall fun y => sq_nonneg _) hInt
      convert he.trans (mul_le_mul_of_nonneg_left hmono (by positivity)) using 1
      congr 2
      ring
    have hsqrt : Real.sqrt (energy hi.weakGrad x (R / 4)) ≤
        Real.sqrt (Q / (R / 4) ^ 2) * Real.sqrt I := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ Q / (R / 4) ^ 2)]
      exact Real.sqrt_le_sqrt hei
    obtain ⟨-, hs, K, hK, hh⟩ := hgain x a hai hahi v hi (hcont.mono hinner) hwi
    have hrad : (R / 4) / 2 = R / 8 := by ring
    rw [hrad] at hs hh
    refine ⟨?_, K, ?_, hh⟩
    · intro z hz
      exact (hs z hz).trans (by dsimp [L]; nlinarith only [mul_le_mul_of_nonneg_left hsqrt hA.le])
    · exact hK.trans (by dsimp [L]; nlinarith only [mul_le_mul_of_nonneg_left hsqrt hA.le])
  have hpoint : ∀ x ∈ Metric.ball c (R / 2), ‖fderiv ℝ v x‖ ≤ L * Real.sqrt I := by
    intro x hx
    exact (local_gain x hx).1 x (Metric.mem_ball_self (by linarith))
  let K : NNReal := Real.toNNReal (D * Real.sqrt I)
  have hK : (K : ℝ) = D * Real.sqrt I := Real.coe_toNNReal _ (by positivity)
  refine ⟨(hregular c a ha hah v hv hcont hw).1, ?_, K, hK.le, ?_⟩
  · intro x hx
    exact (hpoint x hx).trans (mul_le_mul_of_nonneg_right
      (by dsimp only [D]; exact le_add_of_nonneg_right (by positivity) : L ≤ D) (Real.sqrt_nonneg _))
  · intro x hx y hy
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (α / 2).coe_nonneg,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
    apply ENNReal.ofReal_le_ofReal
    rw [hK]
    by_cases hxy : dist x y < R / 8
    · obtain ⟨J, hJ, hh⟩ := (local_gain x hx).2
      have hyx : y ∈ Metric.ball x (R / 8) := Metric.mem_ball.mpr (by simpa [dist_comm] using hxy)
      have hb := hh.dist_le (Metric.mem_ball_self (by linarith)) hyx
      have hLD : L ≤ D := by dsimp only [D]; exact le_add_of_nonneg_right (by positivity)
      exact hb.trans (mul_le_mul_of_nonneg_right
        (hJ.trans (mul_le_mul_of_nonneg_right hLD (Real.sqrt_nonneg _)))
        (Real.rpow_nonneg dist_nonneg _))
    · have hrad : 0 < (R / 8) ^ ((α / 2 : NNReal) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
      have hp : (R / 8) ^ ((α / 2 : NNReal) : ℝ) ≤ dist x y ^ ((α / 2 : NNReal) : ℝ) :=
        Real.rpow_le_rpow (by linarith) (le_of_not_gt hxy) (α / 2).coe_nonneg
      have ht : dist (fderiv ℝ v x) (fderiv ℝ v y) ≤ 2 * L * Real.sqrt I := by
        calc
          _ ≤ ‖fderiv ℝ v x‖ + ‖fderiv ℝ v y‖ := dist_le_norm_add_norm _ _
          _ ≤ _ := by linarith [hpoint x hx, hpoint y hy]
      have hfac : 2 * L ≤ D * dist x y ^ ((α / 2 : NNReal) : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hp (by positivity :
          0 ≤ 2 * L * ((R / 8) ^ ((α / 2 : NNReal) : ℝ))⁻¹)
        have he : 2 * L * ((R / 8) ^ ((α / 2 : NNReal) : ℝ))⁻¹ *
            (R / 8) ^ ((α / 2 : NNReal) : ℝ) = 2 * L := by rw [mul_assoc, inv_mul_cancel₀ hrad.ne', mul_one]
        rw [he] at hmul
        dsimp only [D]
        have hz : 0 ≤ L * dist x y ^ ((α / 2 : NNReal) : ℝ) := by positivity
        calc
          _ ≤ 2 * L * ((R / 8) ^ ((α / 2 : NNReal) : ℝ))⁻¹ * dist x y ^ ((α / 2 : NNReal) : ℝ) := hmul
          _ ≤ _ := by rw [add_mul]; exact le_add_of_nonneg_left hz
      exact ht.trans (by nlinarith only [mul_le_mul_of_nonneg_right hfac (Real.sqrt_nonneg I)])


end SeifertSurfaces.WeakSchauder
