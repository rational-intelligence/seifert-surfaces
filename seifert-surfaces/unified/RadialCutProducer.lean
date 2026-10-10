import TubeUtilities
import FramedCollarProducer
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
noncomputable section

structure RadialProfile (ε : ℝ) where
  profile : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞
  increasing : StrictMono profile
  zero : profile 0 = 0
  epsilon_one : profile ε = 1
  two : profile 2 = 2
  scalar : ℝ
  scalar_pos : 0 < scalar
  inner : ℝ
  inner_pos : 0 < inner
  linear_near_zero : ∀ r, |r| < inner → profile r = scalar * r
  outer : ℝ
  outer_pos : 0 < outer
  outer_lt_two : outer < 2
  identity_near_outer : ∀ r, outer ≤ r → profile r = r

theorem radial_profile_exists (ε : ℝ) (hε : 0 < ε) (h1 : ε < 1) :
    Nonempty (RadialProfile ε) := by
  let c := (ε + 1) / 2
  let b : ContDiffBump c := ⟨(1 - ε) / 2, 1 / 2, by linarith, by linarith⟩
  have hb : ContDiff ℝ ∞ b := b.contDiff
  obtain ⟨C, hC⟩ := b.hasCompactSupport.deriv.exists_bound_of_continuous
    (hb.continuous_deriv (by norm_num))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 - ε) * (C + 1) + 1)
  have hNpos : 0 < (N : ℝ) := by nlinarith
  let a := (1 - ε) / (N : ℝ)
  have ha : 0 < a := div_pos (by linarith) hNpos
  have haN : a * (N : ℝ) = 1 - ε := div_mul_cancel₀ _ (ne_of_gt hNpos)
  have haC : a * C < 1 := by
    have hbound : (1 - ε) * C < (N : ℝ) := by nlinarith
    calc
      a * C = ((1 - ε) * C) / (N : ℝ) := by dsimp [a]; ring
      _ < 1 := (div_lt_one hNpos).mpr hbound
  let f : ℝ → ℝ := fun x => x + a * b x
  have hf : ContDiff ℝ ∞ f := contDiff_id.add (contDiff_const.mul hb)
  have hderiv (x : ℝ) : HasDerivAt f (1 + a * deriv b x) x :=
    (hasDerivAt_id x).add ((hb.differentiable (by norm_num) x).hasDerivAt.const_mul a)
  have hderivpos (x : ℝ) : 0 < 1 + a * deriv b x := by
    have hlower := (abs_le.mp (show |deriv b x| ≤ C from hC x)).1
    have := mul_le_mul_of_nonneg_left hlower ha.le
    nlinarith
  have hmono : StrictMono f :=
    strictMono_of_deriv_pos (fun x => by rw [(hderiv x).deriv]; exact hderivpos x)
  have hfix (x : ℝ) (hx : 1 / 2 ≤ |x - c|) : f x = x := by
    have hz : b x = 0 := b.zero_of_le_dist (by simpa only [b, Real.dist_eq] using hx)
    simp [f, hz]
  have hsurj : Function.Surjective f := by
    intro y
    let M := max (|y| + |c| + 1) 2
    have hM : 0 ≤ M := le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_right _ _)
    have hMbound : |y| + |c| + 1 ≤ M := le_max_left _ _
    have hL : f (-M) = -M := hfix _ (by
      rw [show -M - c = -(M + c) by ring, abs_neg]
      exact (show 1 / 2 ≤ M + c by linarith [neg_abs_le c, abs_nonneg y]).trans (le_abs_self _))
    have hU : f M = M := hfix _ (by
      have hc := le_abs_self c
      have hdiff : 1 / 2 ≤ M - c := by linarith [abs_nonneg y]
      exact hdiff.trans (le_abs_self _))
    have hy : y ∈ Icc (f (-M)) (f M) := by
      rw [hL, hU]
      constructor
      · linarith [neg_abs_le y, abs_nonneg c]
      · linarith [le_abs_self y, abs_nonneg c]
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc (by linarith : -M ≤ M) hf.continuous.continuousOn hy
    exact ⟨x, hx⟩
  let e : ℝ ≃ₜ ℝ := (hmono.orderIsoOfSurjective f hsurj).toHomeomorph
  have he : (e : ℝ → ℝ) = f := rfl
  have heinv : ContDiff ℝ ∞ e.symm :=
    e.contDiff_symm_deriv (fun x => (hderivpos x).ne')
      (by simpa only [he] using hderiv) (by simpa only [he] using hf)
  let d : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
    ⟨e.toEquiv, hf.contMDiff, heinv.contMDiff⟩
  let iter : ℕ → Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
    Nat.rec (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞) (fun _ d' => d'.trans d)
  have hsucc (n : ℕ) (x : ℝ) : iter (n + 1) x = f (iter n x) := rfl
  have hmonoit : ∀ n, StrictMono (iter n) := by
    intro n
    induction n with
    | zero => exact strictMono_id
    | succ n ih => exact hmono.comp ih
  have hfixit : ∀ n x, 1 / 2 ≤ |x - c| → iter n x = x := by
    intro n
    induction n with
    | zero => intro x _; rfl
    | succ n ih => intro x hx; rw [hsucc, ih x hx, hfix x hx]
  have heps : ∀ k, k ≤ N → iter k ε = ε + (k : ℝ) * a := by
    intro k
    induction k with
    | zero => intro _; simp [iter]
    | succ k ih =>
      intro hk
      have hkN : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
      have hb1 : b (ε + (k : ℝ) * a) = 1 := by
        apply b.one_of_mem_closedBall
        rw [Metric.mem_closedBall, Real.dist_eq]
        change |ε + (k : ℝ) * a - c| ≤ (1 - ε) / 2
        rw [abs_le]
        have hnonneg : 0 ≤ (k : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha.le
        have hupper : (k : ℝ) * a ≤ (N : ℝ) * a :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hkN) ha.le
        dsimp [c]
        constructor <;> nlinarith [haN]
      rw [hsucc, ih hkN]
      change (ε + (k : ℝ) * a) + a * b (ε + (k : ℝ) * a) = _
      rw [hb1, Nat.cast_add, Nat.cast_one]
      ring
  have hzero : iter N 0 = 0 := hfixit N 0 (by
    dsimp [c]
    rw [zero_sub, abs_neg, abs_of_pos (by linarith)]
    linarith)
  refine ⟨⟨iter N, hmonoit N, hzero, ?_, ?_, 1, by norm_num,
    ε / 2, by linarith, ?_, 1 + ε / 2, by linarith, by linarith, ?_⟩⟩
  · rw [heps N le_rfl]
    nlinarith [haN]
  · apply hfixit
    dsimp [c]
    exact (show 1 / 2 ≤ 2 - (ε + 1) / 2 by linarith).trans (le_abs_self _)
  · intro r hr
    rw [one_mul]
    apply hfixit
    apply (show 1 / 2 ≤ c - r by dsimp [c]; linarith [(abs_lt.mp hr).2]).trans
    rw [abs_sub_comm]
    exact le_abs_self _
  · intro r hr
    apply hfixit
    exact (show 1 / 2 ≤ r - c by dsimp [c]; linarith).trans (le_abs_self _)

def radialPlaneMap {ε : ℝ} (ρ : RadialProfile ε) (w : Euc 2) : Euc 2 :=
  if w = 0 then 0 else (ρ.profile ‖w‖ / ‖w‖) • w
def radialPlaneInverse {ε : ℝ} (ρ : RadialProfile ε) (w : Euc 2) : Euc 2 :=
  if w = 0 then 0 else (ρ.profile.symm ‖w‖ / ‖w‖) • w

theorem radial_plane_smooth_at_zero {ε : ℝ} (ρ : RadialProfile ε) :
    ContDiffAt ℝ ∞ (radialPlaneMap ρ) 0 ∧ ContDiffAt ℝ ∞ (radialPlaneInverse ρ) 0 := by
  have hcont : Filter.Tendsto (fun w : Euc 2 => ‖w‖) (𝓝 0) (𝓝 0) := by
    simpa [ContinuousAt, norm_zero] using
      (continuous_norm.continuousAt : ContinuousAt (fun w : Euc 2 => ‖w‖) 0)
  have hmap : radialPlaneMap ρ =ᶠ[𝓝 (0 : Euc 2)] (fun w => ρ.scalar • w) := by
    filter_upwards [hcont.eventually_lt_const ρ.inner_pos] with w hw
    by_cases hzero : w = 0
    · simp [radialPlaneMap, hzero]
    · rw [radialPlaneMap, if_neg hzero,
        ρ.linear_near_zero ‖w‖ (by simpa [abs_of_nonneg (norm_nonneg w)] using hw)]
      rw [mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hzero)]
  have hzero : ρ.profile.symm 0 = 0 := by
    apply ρ.profile.injective
    simpa using ρ.zero.symm
  have hinverse : StrictMono ρ.profile.symm := by
    intro a b hab
    exact (ρ.increasing.lt_iff_lt).mp (by simpa using hab)
  have hhalf : ρ.profile (ρ.inner / 2) = ρ.scalar * (ρ.inner / 2) :=
    ρ.linear_near_zero _ (by rw [abs_of_pos (by linarith [ρ.inner_pos] : 0 < ρ.inner / 2)]; linarith [ρ.inner_pos])
  have hinv : radialPlaneInverse ρ =ᶠ[𝓝 (0 : Euc 2)]
      (fun w => ρ.scalar⁻¹ • w) := by
    have hδ : 0 < ρ.scalar * (ρ.inner / 2) :=
      mul_pos ρ.scalar_pos (by linarith [ρ.inner_pos])
    filter_upwards [hcont.eventually_lt_const hδ] with w hw
    have hnonneg : 0 ≤ ρ.profile.symm ‖w‖ := by
      simpa [hzero] using hinverse.monotone (norm_nonneg w)
    have hbound : ρ.profile.symm ‖w‖ < ρ.inner / 2 := by
      apply (ρ.increasing.lt_iff_lt).mp
      simpa [hhalf] using hw
    have hlinear := ρ.linear_near_zero (ρ.profile.symm ‖w‖)
      (by rw [abs_of_nonneg hnonneg]; linarith [ρ.inner_pos])
    have heq : ρ.profile.symm ‖w‖ = ρ.scalar⁻¹ * ‖w‖ := by
      have heq' : ‖w‖ = ρ.scalar * ρ.profile.symm ‖w‖ := by simpa using hlinear
      calc
        ρ.profile.symm ‖w‖ = ρ.scalar⁻¹ * (ρ.scalar * ρ.profile.symm ‖w‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ρ.scalar_pos), one_mul]
        _ = ρ.scalar⁻¹ * ‖w‖ := congrArg (fun r => ρ.scalar⁻¹ * r) heq'.symm
    by_cases hwzero : w = 0
    · simp [radialPlaneInverse, hwzero]
    · rw [radialPlaneInverse, if_neg hwzero, heq,
        mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hwzero)]
  exact ⟨((contDiffAt_const (c := ρ.scalar)).smul contDiffAt_id).congr_of_eventuallyEq hmap,
    ((contDiffAt_const (c := ρ.scalar⁻¹)).smul contDiffAt_id).congr_of_eventuallyEq hinv⟩
theorem radial_plane_preserves_disk {ε : ℝ} (ρ : RadialProfile ε) (w : TubeDisk) :
    radialPlaneMap ρ (w : Euc 2) ∈ tubeDiskOpen := by
  change ‖radialPlaneMap ρ (w : Euc 2) - 0‖ < 2
  simp only [sub_zero]
  have hw : ‖(w : Euc 2)‖ < 2 := by simpa [tubeDiskOpen, Metric.mem_ball, dist_zero_right] using w.property
  by_cases hzero : (w : Euc 2) = 0
  · simp [radialPlaneMap, hzero]
  · have hnorm : 0 < ‖(w : Euc 2)‖ := norm_pos_iff.mpr hzero
    have hpositive : 0 < ρ.profile ‖(w : Euc 2)‖ := by
      simpa [ρ.zero] using ρ.increasing hnorm
    rw [radialPlaneMap, if_neg hzero, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hpositive hnorm), div_mul_cancel₀ _ (ne_of_gt hnorm)]
    simpa [ρ.two] using ρ.increasing hw
def radialTubeDisk {ε : ℝ} (ρ : RadialProfile ε) (w : TubeDisk) : TubeDisk :=
  ⟨radialPlaneMap ρ w, radial_plane_preserves_disk ρ w⟩
theorem radial_disk_diffeomorph_exists {ε : ℝ} (ρ : RadialProfile ε) :
    ∃ A : Diffeomorph 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 2) TubeDisk TubeDisk ∞,
      (A : TubeDisk → TubeDisk) = radialTubeDisk ρ ∧
      ∀ w, (A.symm w : Euc 2) = radialPlaneInverse ρ (w : Euc 2) := by
  have hzero : ρ.profile.symm 0 = 0 := by
    apply ρ.profile.injective
    simpa using ρ.zero.symm
  have hinverse : StrictMono ρ.profile.symm := by
    intro a b hab
    exact ρ.increasing.lt_iff_lt.mp (by simpa using hab)
  have htwo : ρ.profile.symm 2 = 2 := by
    apply ρ.profile.injective
    simpa using ρ.two.symm
  have hinvdisk (w : TubeDisk) : radialPlaneInverse ρ (w : Euc 2) ∈ tubeDiskOpen := by
    change ‖radialPlaneInverse ρ (w : Euc 2) - 0‖ < 2
    simp only [sub_zero]
    have hw : ‖(w : Euc 2)‖ < 2 := by
      simpa [tubeDiskOpen, Metric.mem_ball, dist_zero_right] using w.property
    by_cases hwzero : (w : Euc 2) = 0
    · simp [radialPlaneInverse, hwzero]
    · have hpos := norm_pos_iff.mpr hwzero
      have hρpos : 0 < ρ.profile.symm ‖(w : Euc 2)‖ := by
        simpa [hzero] using hinverse hpos
      rw [radialPlaneInverse, if_neg hwzero, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hρpos hpos), div_mul_cancel₀ _ (ne_of_gt hpos)]
      simpa [htwo] using hinverse hw
  have hinv (f g : ℝ → ℝ) (hfzero : f 0 = 0) (hginv : Function.LeftInverse g f)
      (hfmono : StrictMono f) (w : Euc 2) :
      (if (if w = 0 then 0 else (f ‖w‖ / ‖w‖) • w) = 0 then 0
       else (g ‖if w = 0 then 0 else (f ‖w‖ / ‖w‖) • w‖ /
         ‖if w = 0 then 0 else (f ‖w‖ / ‖w‖) • w‖) •
         (if w = 0 then 0 else (f ‖w‖ / ‖w‖) • w)) = w := by
    by_cases hwzero : w = 0
    · simp [hwzero]
    · have hpos := norm_pos_iff.mpr hwzero
      have hfpos : 0 < f ‖w‖ := by simpa [hfzero] using hfmono hpos
      have hnorm : ‖(f ‖w‖ / ‖w‖) • w‖ = f ‖w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hfpos hpos),
          div_mul_cancel₀ _ (ne_of_gt hpos)]
      have hne : (f ‖w‖ / ‖w‖) • w ≠ 0 := by
        intro hz
        have := hnorm
        rw [hz, norm_zero] at this
        linarith
      simp only [if_neg hwzero, if_neg hne, hnorm, smul_smul]
      rw [hginv ‖w‖]
      have hcoeff : ‖w‖ / f ‖w‖ * (f ‖w‖ / ‖w‖) = 1 := by
        field_simp
      rw [hcoeff, one_smul]
  have hsmooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
      (hz : ContDiffAt ℝ ∞ (fun w : Euc 2 => if w = 0 then 0 else (f ‖w‖ / ‖w‖) • w) 0) :
      ContDiff ℝ ∞ (fun w : Euc 2 => if w = 0 then 0 else (f ‖w‖ / ‖w‖) • w) := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : w = 0
    · simpa [hw] using hz
    · have hn : ContDiffAt ℝ ∞ (fun w : Euc 2 => ‖w‖) w := contDiffAt_norm ℝ hw
      apply ((hf.contDiffAt.comp w hn).div hn (norm_ne_zero_iff.mpr hw)).smul contDiffAt_id
        |>.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hw] with v hv
      simp [hv]
  let inv : TubeDisk → TubeDisk := fun w => ⟨radialPlaneInverse ρ w, hinvdisk w⟩
  have hforward : ContMDiff 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 2) ∞ (radialTubeDisk ρ) := by
    apply (ContMDiff.subtypeVal_comp_iff tubeDiskOpen _).mp
    exact (hsmooth ρ.profile ρ.profile.contMDiff_toFun.contDiff
      (radial_plane_smooth_at_zero ρ).1).contMDiff.comp contMDiff_subtype_val
  have hbackward : ContMDiff 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 2) ∞ inv := by
    apply (ContMDiff.subtypeVal_comp_iff tubeDiskOpen _).mp
    exact (hsmooth ρ.profile.symm ρ.profile.symm.contMDiff_toFun.contDiff
      (radial_plane_smooth_at_zero ρ).2).contMDiff.comp contMDiff_subtype_val
  let A : Diffeomorph 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 2) TubeDisk TubeDisk ∞ :=
    { toEquiv :=
        { toFun := radialTubeDisk ρ
          invFun := inv
          left_inv := by
            intro w
            apply Subtype.ext
            exact hinv ρ.profile ρ.profile.symm ρ.zero ρ.profile.left_inv ρ.increasing w
          right_inv := by
            intro w
            apply Subtype.ext
            exact hinv ρ.profile.symm ρ.profile hzero ρ.profile.right_inv hinverse w }
      contMDiff_toFun := hforward
      contMDiff_invFun := hbackward }
  exact ⟨A, rfl, fun _ => rfl⟩

structure RadialSphereExpansion {K : OrientedKnot} (T : TubularNeighborhood K)
    {ε : ℝ} (ρ : RadialProfile ε) where
  ambient : Diffeomorph (𝓡 3) (𝓡 3) ThreeSphere ThreeSphere ∞
  inside : ∀ p : TubeDomain,
    ambient (T.tube 0 p) = T.tube 0 (p.1, radialTubeDisk ρ p.2)
  outside : ∀ x ∉ Set.range (T.tube 0), ambient x = x

/-- S4b: smooth gluing uses identity on an OUTER ANNULUS and linearity near
zero. The punctured radial formula alone is not a smoothness premise. -/
theorem radial_sphere_expansion_exists {K : OrientedKnot} (T : TubularNeighborhood K)
    {ε : ℝ} (ρ : RadialProfile ε) : Nonempty (RadialSphereExpansion T ρ) := by
  classical
  obtain ⟨D, hD, hDinv⟩ := radial_disk_diffeomorph_exists ρ
  obtain ⟨e, he⟩ := tube_image_diffeomorph_exists T
  let B := (Diffeomorph.refl (𝓡 1) Circle ∞).prodCongr D
  let H := e.symm.trans (B.trans e)
  let small : Set ThreeSphere := T.tube 0 '' {p : TubeDomain | ‖(p.2 : Euc 2)‖ ≤ ρ.outer}
  have hclosed : IsClosed small := by
    let lift : Circle × Metric.closedBall (0 : Euc 2) ρ.outer → TubeDomain := fun q =>
      (q.1, ⟨q.2.val, by
        change ‖q.2.val - 0‖ < 2
        have hnorm : ‖q.2.val‖ ≤ ρ.outer := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using q.2.property
        simpa using lt_of_le_of_lt hnorm ρ.outer_lt_two⟩)
    have hlift : Continuous lift :=
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
    have himage : (T.tube 0 ∘ lift) '' univ = small := by
      ext y
      constructor
      · rintro ⟨⟨z, w⟩, _, rfl⟩
        refine ⟨lift (z, w), ?_, rfl⟩
        change ‖w.val‖ ≤ ρ.outer
        simpa only [Metric.mem_closedBall, dist_zero_right] using w.property
      · rintro ⟨⟨z, w⟩, hw, rfl⟩
        refine ⟨(z, ⟨w.val, ?_⟩), Set.mem_univ _, ?_⟩
        · simpa [Metric.mem_closedBall, dist_zero_right] using hw
        · rfl
    rw [← himage]
    exact (isCompact_univ.image ((T.smoothEmbedding 0).isEmbedding.continuous.comp hlift)).isClosed
  have hsub : small ⊆ Set.range (T.tube 0) := by
    rintro y ⟨p, _, rfl⟩
    exact ⟨p, rfl⟩
  have hDfix (w : TubeDisk) (hw : ρ.outer ≤ ‖(w : Euc 2)‖) : D w = w := by
    rw [hD]
    apply Subtype.ext
    change radialPlaneMap ρ (w : Euc 2) = (w : Euc 2)
    by_cases hzero : (w : Euc 2) = 0
    · simp [radialPlaneMap, hzero]
    · rw [radialPlaneMap, if_neg hzero, ρ.identity_near_outer _ hw,
        div_self (norm_ne_zero_iff.mpr hzero), one_smul]
  have hHfix (x : tubeImageOpen T) (hx : (x : ThreeSphere) ∉ small) : H x = x := by
    let p := e.symm x
    have hpx : T.tube 0 p = (x : ThreeSphere) := by
      rw [← he]
      exact congrArg Subtype.val (e.apply_symm_apply x)
    have hnorm : ρ.outer ≤ ‖(p.2 : Euc 2)‖ := by
      by_contra h
      exact hx ⟨p, le_of_lt (lt_of_not_ge h), hpx⟩
    have hB : B p = p := by
      change (p.1, D p.2) = p
      rw [hDfix p.2 hnorm]
    change e (B p) = x
    rw [hB]
    exact e.apply_symm_apply x
  have hHinvfix (x : tubeImageOpen T) (hx : (x : ThreeSphere) ∉ small) : H.symm x = x := by
    apply H.injective
    change H (H.symm x) = H x
    rw [H.apply_symm_apply, hHfix x hx]
  let extend (J : Diffeomorph (𝓡 3) (𝓡 3) (tubeImageOpen T) (tubeImageOpen T) ∞)
      (x : ThreeSphere) : ThreeSphere :=
    if hx : x ∈ Set.range (T.tube 0) then J ⟨x, hx⟩ else x
  have hrestrict (J : Diffeomorph (𝓡 3) (𝓡 3) (tubeImageOpen T) (tubeImageOpen T) ∞) :
      (fun x : tubeImageOpen T => extend J x) = Subtype.val ∘ J := by
    funext x
    have hx : (x : ThreeSphere) ∈ Set.range (T.tube 0) := x.property
    simp only [extend, dif_pos hx, Function.comp_apply]
  have hextfix (J : Diffeomorph (𝓡 3) (𝓡 3) (tubeImageOpen T) (tubeImageOpen T) ∞)
      (hJ : ∀ x : tubeImageOpen T, (x : ThreeSphere) ∉ small → J x = x)
      (x : ThreeSphere) (hx : x ∉ small) : extend J x = x := by
    by_cases hin : x ∈ Set.range (T.tube 0)
    · simp only [extend, dif_pos hin, hJ ⟨x, hin⟩ hx]
    · simp only [extend, dif_neg hin]
  have hsmooth (J : Diffeomorph (𝓡 3) (𝓡 3) (tubeImageOpen T) (tubeImageOpen T) ∞)
      (hJ : ∀ x : tubeImageOpen T, (x : ThreeSphere) ∉ small → J x = x) :
      ContMDiff (𝓡 3) (𝓡 3) ∞ (extend J) := by
    intro x
    by_cases hin : x ∈ Set.range (T.tube 0)
    · apply (contMDiffAt_subtype_iff (x := (⟨x, hin⟩ : tubeImageOpen T))).mp
      have hres : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : tubeImageOpen T => extend J x) := by
        rw [hrestrict]
        exact contMDiff_subtype_val.comp J.contMDiff
      exact hres ⟨x, hin⟩
    · apply contMDiffAt_id.congr_of_eventuallyEq
      have hout : x ∉ small := fun h => hin (hsub h)
      filter_upwards [hclosed.isOpen_compl.mem_nhds hout] with y hy
      exact hextfix J hJ y hy
  have hinverse (J : Diffeomorph (𝓡 3) (𝓡 3) (tubeImageOpen T) (tubeImageOpen T) ∞) :
      Function.LeftInverse (extend J.symm) (extend J) := by
    intro x
    by_cases hin : x ∈ Set.range (T.tube 0)
    · have hmem : (J ⟨x, hin⟩ : ThreeSphere) ∈ Set.range (T.tube 0) := (J ⟨x, hin⟩).property
      simp only [extend, dif_pos hin, dif_pos hmem]
      exact congrArg Subtype.val (J.symm_apply_apply ⟨x, hin⟩)
    · simp only [extend, dif_neg hin]
  let ambient : Diffeomorph (𝓡 3) (𝓡 3) ThreeSphere ThreeSphere ∞ :=
    { toEquiv :=
        { toFun := extend H
          invFun := extend H.symm
          left_inv := hinverse H
          right_inv := hinverse H.symm }
      contMDiff_toFun := hsmooth H hHfix
      contMDiff_invFun := hsmooth H.symm hHinvfix }
  refine ⟨⟨ambient, ?_, ?_⟩⟩
  · intro p
    have hmem : T.tube 0 p ∈ Set.range (T.tube 0) := ⟨p, rfl⟩
    have hep : (⟨T.tube 0 p, hmem⟩ : tubeImageOpen T) = e p := by
      apply Subtype.ext
      exact (he p).symm
    change extend H (T.tube 0 p) = _
    simp only [extend, dif_pos hmem, hep]
    change (e (B (e.symm (e p))) : ThreeSphere) = _
    rw [e.symm_apply_apply, he]
    change T.tube 0 (p.1, D p.2) = _
    rw [hD]
  · intro x hx
    change extend H x = x
    simp only [extend, dif_neg hx]

def expandedSphereMap {K : OrientedKnot} {T : TubularNeighborhood K}
    {F : SphereSpanningSurface.{0} K} {R : FramedRibbon T F}
    (C : CutSurface R) {ρ : RadialProfile R.epsilon} (A : RadialSphereExpansion T ρ) :
    C.surface → ThreeSphere := A.ambient ∘ R.ambient ∘ F.embedding ∘ C.inclusion

theorem expanded_surface_in_given_exterior {K : OrientedKnot} {T : TubularNeighborhood K}
    {F : SphereSpanningSurface.{0} K} {R : FramedRibbon T F}
    (C : CutSurface R) {ρ : RadialProfile R.epsilon} (A : RadialSphereExpansion T ρ) :
    ∀ x, expandedSphereMap C A x ∈ T.exteriorSet := by
  intro x
  change expandedSphereMap C A x ∉ ⋃ i, T.openTube i
  intro hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hi0 : i = 0 := Subsingleton.elim _ _
  subst i
  obtain ⟨q, hq, heq⟩ := hi
  have hin : R.ambient (F.embedding (C.inclusion x)) ∈ Set.range (T.tube 0) := by
    by_contra hout
    have hfix := A.outside _ hout
    have hpoint : R.ambient (F.embedding (C.inclusion x)) = T.tube 0 q := by
      simpa [expandedSphereMap, Function.comp_def, hfix] using heq.symm
    exact hout ⟨q, hpoint.symm⟩
  obtain ⟨p, hp⟩ := hin
  have hqp : q = (p.1, radialTubeDisk ρ p.2) := by
    apply (T.smoothEmbedding 0).isEmbedding.injective
    calc
      T.tube 0 q = expandedSphereMap C A x := heq
      _ = A.ambient (T.tube 0 p) := by simp [expandedSphereMap, Function.comp_def, hp]
      _ = T.tube 0 (p.1, radialTubeDisk ρ p.2) := A.inside p
  have hpε : ‖(p.2 : Euc 2)‖ < R.epsilon := by
    have hnorm : ‖radialPlaneMap ρ (p.2 : Euc 2)‖ < 1 := by
      simpa [hqp, radialTubeDisk] using hq
    by_cases hpzero : (p.2 : Euc 2) = 0
    · simpa [hpzero] using R.epsilon_pos
    · have hpos := norm_pos_iff.mpr hpzero
      have hρpos : 0 < ρ.profile ‖(p.2 : Euc 2)‖ := by
        simpa [ρ.zero] using ρ.increasing hpos
      rw [radialPlaneMap, if_neg hpzero, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hρpos hpos), div_mul_cancel₀ _ (ne_of_gt hpos)] at hnorm
      exact ρ.increasing.lt_iff_lt.mp (by simpa [ρ.epsilon_one] using hnorm)
  have hsmall : R.ambient (F.embedding (C.inclusion x)) ∈ closedTubeRadius T (2 * R.epsilon) := by
    exact ⟨p, le_of_lt (show ‖(p.2 : Euc 2)‖ < 2 * R.epsilon by linarith [R.epsilon_pos]), hp⟩
  obtain ⟨z, t, hcollar⟩ := framed_ribbon_only_small_tube R (C.inclusion x) hsmall
  obtain ⟨w, hw, hgraph⟩ := R.collar_graph z t
  have hpw : p = (z, w) := (T.smoothEmbedding 0).isEmbedding.injective (by
    rw [hp, hcollar, hgraph])
  have ht : (t : ℝ) < 1 / 2 := by
    have hnorm : ‖(p.2 : Euc 2)‖ = 2 * R.epsilon * (t : ℝ) := by
      rw [hpw, hw, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by linarith [R.epsilon_pos]) t.property.1), unitVector_norm, mul_one]
    rw [hnorm] at hpε
    nlinarith [R.epsilon_pos]
  have hcut : C.inclusion x ∈ cutSet R := by
    rw [← C.image_eq]
    exact ⟨x, rfl⟩
  exact hcut ⟨(z, t), ht, hcollar.symm⟩

theorem expanded_boundary_graph {K : OrientedKnot} {T : TubularNeighborhood K}
    {F : SphereSpanningSurface.{0} K} {R : FramedRibbon T F}
    (C : CutSurface R) {ρ : RadialProfile R.epsilon} (A : RadialSphereExpansion T ρ) :
    ∀ z, expandedSphereMap C A (C.boundary.toFun z) = T.tube 0 (z, unitDisk (R.direction z)) := by
  intro z
  obtain ⟨t, ht, hcut⟩ := C.boundary_graph z
  obtain ⟨w, hw, hgraph⟩ := R.collar_graph z t
  have hw' : (w : Euc 2) = R.epsilon • unitVector (R.direction z) := by
    rw [hw, ht]
    congr 1
    ring
  have hnorm : ‖(w : Euc 2)‖ = R.epsilon := by
    rw [hw', norm_smul, Real.norm_eq_abs, abs_of_pos R.epsilon_pos, unitVector_norm, mul_one]
  have hne : (w : Euc 2) ≠ 0 := by
    intro hzero
    have := hnorm
    rw [hzero, norm_zero] at this
    linarith [R.epsilon_pos]
  have hdisk : radialTubeDisk ρ w = unitDisk (R.direction z) := by
    apply Subtype.ext
    change radialPlaneMap ρ (w : Euc 2) = unitVector (R.direction z)
    rw [radialPlaneMap, if_neg hne, hnorm, ρ.epsilon_one, hw', smul_smul]
    simp [ne_of_gt R.epsilon_pos]
  change A.ambient (R.ambient (F.embedding (C.inclusion (C.boundary.toFun z)))) = _
  rw [hcut, hgraph, A.inside, hdisk]

end
end SeifertSurfaces.LongitudeProducers
