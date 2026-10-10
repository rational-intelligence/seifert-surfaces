import SectorRegularityHelpers
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import A5RelativeC1Inverse

set_option autoImplicit false
open scoped ContDiff NNReal
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

private theorem norm_sectorUnit (t : ℝ) : ‖sectorUnit t‖ = 1 := by
  have h : ‖sectorUnit t‖ ^ 2 = 1 := by
    simp [EuclideanSpace.real_norm_sq_eq, sectorUnit, Fin.sum_univ_two,
      Real.cos_sq_add_sin_sq]
  nlinarith [norm_nonneg (sectorUnit t)]

private theorem norm_sectorUnit_sub (a b : ℝ) (hab : a ≤ b)
    (hd : b - a ≤ 2 * Real.pi) :
    ‖sectorUnit b - sectorUnit a‖ = 2 * Real.sin ((b - a) / 2) := by
  have hs : 0 ≤ Real.sin ((b - a) / 2) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith) (by linarith)
  have hsq : ‖sectorUnit b - sectorUnit a‖ ^ 2 =
      (2 * Real.sin ((b - a) / 2)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two, PiLp.sub_apply, sectorUnit]
    norm_num only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hc := Real.cos_sub b a
    have hh := Real.sin_sq_eq_half_sub ((b - a) / 2)
    rw [show 2 * ((b - a) / 2) = b - a by ring] at hh
    nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]
  nlinarith [norm_nonneg (sectorUnit b - sectorUnit a)]

/-- Every proper closed angular interval has a uniform inverse chord bound.
The constant is allowed to depend on the angle, including for reflex sectors. -/
theorem sector_angular_distance_bound (θ : ℝ) (hθ : 0 < θ)
    (hθπ : θ < 2 * Real.pi) :
    ∃ K : ℝ, 0 < K ∧ ∀ a ∈ Icc (0 : ℝ) θ, ∀ b ∈ Icc (0 : ℝ) θ,
      |a - b| ≤ K * ‖sectorUnit a - sectorUnit b‖ := by
  let K := θ / (2 * Real.sin (θ / 2))
  have hs : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith) (by linarith)
  have hK : 0 < K := div_pos hθ (by positivity)
  refine ⟨K, hK, ?_⟩
  have ordered (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) θ)
      (hb : b ∈ Icc (0 : ℝ) θ) (hab : a ≤ b) :
      b - a ≤ K * ‖sectorUnit b - sectorUnit a‖ := by
    let t := (b - a) / θ
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hab) hθ.le
    have ht1 : t ≤ 1 := (div_le_one hθ).mpr (by linarith [ha.1, hb.2])
    have hconc := (strictConcaveOn_sin_Icc.concaveOn).2
      (show (0 : ℝ) ∈ Icc 0 Real.pi by exact ⟨le_rfl, Real.pi_pos.le⟩)
      (show θ / 2 ∈ Icc 0 Real.pi by constructor <;> linarith)
      (sub_nonneg.mpr ht1) ht (by ring : (1 - t) + t = 1)
    have he : t * (θ / 2) = (b - a) / 2 := by
      dsimp [t]
      field_simp
    simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add] at hconc
    have hconc' : t * Real.sin (θ / 2) ≤ Real.sin ((b - a) / 2) := by
      simpa only [he] using hconc
    rw [norm_sectorUnit_sub a b hab (by linarith [ha.1, hb.2])]
    have hmul := mul_le_mul_of_nonneg_left hconc' (le_of_lt hK)
    have hid : K * (t * Real.sin (θ / 2)) = (b - a) / 2 := by
      dsimp [K, t]
      field_simp
    rw [hid] at hmul
    nlinarith
  intro a ha b hb
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab), norm_sub_rev]
    simpa only [neg_sub] using ordered a b ha hb hab
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    exact ordered b a hb ha hba

private theorem hasDerivAt_sectorUnit (t : ℝ) :
    HasDerivAt sectorUnit (!₂[-Real.sin t, Real.cos t] : Euc 2) t := by
  convert ((Real.hasDerivAt_cos t).smul_const (EuclideanSpace.single 0 (1 : ℝ) : Euc 2)).add
    ((Real.hasDerivAt_sin t).smul_const (EuclideanSpace.single 1 (1 : ℝ) : Euc 2)) using 1
  · ext s i
    fin_cases i <;> simp [sectorUnit]
  · ext i
    fin_cases i <;> simp

private theorem norm_sectorUnit_deriv (t : ℝ) :
    ‖(!₂[-Real.sin t, Real.cos t] : Euc 2)‖ = 1 := by
  have h : ‖(!₂[-Real.sin t, Real.cos t] : Euc 2)‖ ^ 2 = 1 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]
  nlinarith [norm_nonneg (!₂[-Real.sin t, Real.cos t] : Euc 2)]

/-- A derivative bound controls oscillation on the literal sector, including
reflex sectors, by a constant depending only on the opening. -/
theorem sector_norm_sub_le_of_derivative_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) :
    ∃ L : ℝ, 0 < L ∧ ∀ (R C : ℝ) (f : Euc 2 → V) (Df : Euc 2 → Euc 2 →L[ℝ] V),
      0 ≤ C →
      (∀ x ∈ Metric.ball 0 R ∩ planarSector θ,
        HasFDerivWithinAt f (Df x) (Metric.ball 0 R ∩ planarSector θ) x) →
      (∀ x ∈ Metric.ball 0 R ∩ planarSector θ, ‖Df x‖ ≤ C) →
      ∀ x ∈ Metric.ball 0 R ∩ planarSector θ,
        ∀ y ∈ Metric.ball 0 R ∩ planarSector θ,
          ‖f x - f y‖ ≤ L * C * ‖x - y‖ := by
  obtain ⟨K, hK, hchord⟩ := sector_angular_distance_bound θ hθ hθπ
  refine ⟨1 + 2 * K, by positivity, ?_⟩
  intro R C f Df hC hf hDf
  let S := Metric.ball (0 : Euc 2) R ∩ planarSector θ
  have mem (r a : ℝ) (hr : 0 ≤ r) (hrR : r < R) (ha : a ∈ Icc (0 : ℝ) θ) :
      r • sectorUnit a ∈ S := by
    refine ⟨?_, r, hr, a, ha, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr, norm_sectorUnit, mul_one] using hrR
  have radial (r s a : ℝ) (hs : 0 ≤ s) (hsr : s ≤ r) (hrR : r < R)
      (ha : a ∈ Icc (0 : ℝ) θ) :
      ‖f (r • sectorUnit a) - f (s • sectorUnit a)‖ ≤ C * (r - s) := by
    have hm : MapsTo (fun u : ℝ => u • sectorUnit a) (Icc s r) S := by
      intro u hu
      exact mem u a (hs.trans hu.1) (hu.2.trans_lt hrR) ha
    apply norm_image_sub_le_of_norm_deriv_le_segment'
      (f' := fun u => Df (u • sectorUnit a) (sectorUnit a))
      (fun u hu => (hf _ (hm hu)).comp_hasDerivWithinAt u
        (by simpa only [one_smul, id_eq] using
          ((hasDerivAt_id u).smul_const (sectorUnit a)).hasDerivWithinAt) hm)
      (fun u hu => ?_) r ⟨hsr, le_rfl⟩
    calc
      ‖Df (u • sectorUnit a) (sectorUnit a)‖ ≤
          ‖Df (u • sectorUnit a)‖ * ‖sectorUnit a‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C := by simpa only [norm_sectorUnit, mul_one] using hDf _ (hm ⟨hu.1, hu.2.le⟩)
  have angular_ordered (s a b : ℝ) (hs : 0 ≤ s) (hsR : s < R)
      (ha : a ∈ Icc (0 : ℝ) θ) (hb : b ∈ Icc (0 : ℝ) θ) (hab : a ≤ b) :
      ‖f (s • sectorUnit b) - f (s • sectorUnit a)‖ ≤ C * s * (b - a) := by
    have hm : MapsTo (fun u : ℝ => s • sectorUnit u) (Icc a b) S := by
      intro u hu
      exact mem s u hs hsR ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩
    apply norm_image_sub_le_of_norm_deriv_le_segment'
      (f' := fun u => Df (s • sectorUnit u) (s • (!₂[-Real.sin u, Real.cos u] : Euc 2)))
      (fun u hu => (hf _ (hm hu)).comp_hasDerivWithinAt u
        ((hasDerivAt_sectorUnit u).const_smul s).hasDerivWithinAt hm)
      (fun u hu => ?_) b ⟨hab, le_rfl⟩
    calc
      ‖Df (s • sectorUnit u) (s • (!₂[-Real.sin u, Real.cos u] : Euc 2))‖ ≤
          ‖Df (s • sectorUnit u)‖ * ‖s • (!₂[-Real.sin u, Real.cos u] : Euc 2)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖Df (s • sectorUnit u)‖ * s := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs, norm_sectorUnit_deriv, mul_one]
      _ ≤ C * s := mul_le_mul_of_nonneg_right (hDf _ (hm ⟨hu.1, hu.2.le⟩)) hs
  have angular (s a b : ℝ) (hs : 0 ≤ s) (hsR : s < R)
      (ha : a ∈ Icc (0 : ℝ) θ) (hb : b ∈ Icc (0 : ℝ) θ) :
      ‖f (s • sectorUnit a) - f (s • sectorUnit b)‖ ≤ C * s * |a - b| := by
    rcases le_total a b with hab | hba
    · rw [abs_of_nonpos (sub_nonpos.mpr hab), norm_sub_rev, neg_sub]
      exact angular_ordered s a b hs hsR ha hb hab
    · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
      exact angular_ordered s b a hs hsR hb ha hba
  have ordered (r s a b : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hsr : s ≤ r)
      (hrR : r < R) (ha : a ∈ Icc (0 : ℝ) θ) (hb : b ∈ Icc (0 : ℝ) θ) :
      ‖f (r • sectorUnit a) - f (s • sectorUnit b)‖ ≤
        (1 + 2 * K) * C * ‖r • sectorUnit a - s • sectorUnit b‖ := by
    let d := ‖r • sectorUnit a - s • sectorUnit b‖
    have hrad : r - s ≤ d := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
        abs_of_nonneg hs, norm_sectorUnit, mul_one] using
        norm_sub_norm_le (r • sectorUnit a) (s • sectorUnit b)
    have hsame : ‖r • sectorUnit a - s • sectorUnit a‖ = r - s := by
      rw [← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsr),
        norm_sectorUnit, mul_one]
    have hunit : s * ‖sectorUnit a - sectorUnit b‖ ≤ 2 * d := by
      calc
        s * ‖sectorUnit a - sectorUnit b‖ = ‖s • sectorUnit a - s • sectorUnit b‖ := by
          rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
        _ ≤ ‖s • sectorUnit a - r • sectorUnit a‖ + d := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = (r - s) + d := by rw [norm_sub_rev, hsame]
        _ ≤ 2 * d := by linarith
    have hangle : s * |a - b| ≤ 2 * K * d := by
      have ha' := mul_le_mul_of_nonneg_left (hchord a ha b hb) hs
      have hu' := mul_le_mul_of_nonneg_left hunit hK.le
      nlinarith
    calc
      ‖f (r • sectorUnit a) - f (s • sectorUnit b)‖ ≤
          ‖f (r • sectorUnit a) - f (s • sectorUnit a)‖ +
          ‖f (s • sectorUnit a) - f (s • sectorUnit b)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C * (r - s) + C * s * |a - b| :=
        add_le_add (radial r s a hs hsr hrR ha) (angular s a b hs (hsr.trans_lt hrR) ha hb)
      _ ≤ (1 + 2 * K) * C * d := by
        nlinarith [mul_nonneg hC (sub_nonneg.mpr hrad),
          mul_nonneg hC (sub_nonneg.mpr hangle)]
  intro x hx y hy
  obtain ⟨r, hr, a, ha, rfl⟩ := hx.2
  obtain ⟨s, hs, b, hb, rfl⟩ := hy.2
  have hrR : r < R := by simpa only [Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hr, norm_sectorUnit, mul_one] using hx.1
  have hsR : s < R := by simpa only [Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hs, norm_sectorUnit, mul_one] using hy.1
  rcases le_total s r with hsr | hrs
  · exact ordered r s a b hr hs hsr hrR ha hb
  · simpa only [norm_sub_rev] using ordered s r b a hs hr hrs hsR hb ha

/-- A C1 map on a proper native sector, with invertible derivative at its
vertex, agrees near that vertex with an ambient homeomorphism. The image
region is the actual image under this map, and need not be a straight sector. -/
theorem C1_sector_local_homeomorph_extension
    (θ R : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) (hR : 0 < R)
    (f : Euc 2 → Euc 2) (f₀ : Euc 2 ≃L[ℝ] Euc 2)
    (hf : ContDiffOn ℝ 1 f (Metric.ball 0 R ∩ planarSector θ))
    (hf₀ : HasFDerivWithinAt f (f₀ : Euc 2 →L[ℝ] Euc 2)
      (Metric.ball 0 R ∩ planarSector θ) 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∃ H : Euc 2 ≃ₜ Euc 2,
      EqOn f H (Metric.ball 0 r ∩ planarSector θ) := by
  let S := Metric.ball (0 : Euc 2) R ∩ planarSector θ
  have hS : UniqueDiffOn ℝ S := by
    simpa only [S, inter_comm] using
      (planarSector_uniqueDiffOn hθ hθπ).inter (Metric.isOpen_ball (x := (0 : Euc 2)) (ε := R))
  have hz : (0 : Euc 2) ∈ S := ⟨Metric.mem_ball_self hR,
    0, le_rfl, 0, ⟨le_rfl, hθ.le⟩, by simp⟩
  have hzero : fderivWithin ℝ f S 0 = (f₀ : Euc 2 →L[ℝ] Euc 2) :=
    hf₀.fderivWithin (hS 0 hz)
  obtain ⟨L, hL, hbound⟩ := sector_norm_sub_le_of_derivative_bound (V := Euc 2) θ hθ hθπ
  let N : ℝ≥0 := ‖(f₀.symm : Euc 2 →L[ℝ] Euc 2)‖₊
  let A := lipschitzExtensionConstant (Euc 2)
  have hN : 0 < N := by exact_mod_cast f₀.symm.norm_pos
  have hA : 0 < A := lipschitzExtensionConstant_pos (Euc 2)
  let c : ℝ≥0 := N⁻¹ / (2 * A)
  have hc : 0 < c := by dsimp [c]; positivity
  have hac : A * c < N⁻¹ := by
    have he : A * c = N⁻¹ / 2 := by dsimp [c]; field_simp
    rw [he]
    exact half_lt_self (inv_pos.mpr hN)
  let ε : ℝ := (c : ℝ) / L
  have hε : 0 < ε := div_pos (by exact_mod_cast hc) hL
  let D : Euc 2 → Euc 2 →L[ℝ] Euc 2 := fun x =>
    fderivWithin ℝ f S x - (f₀ : Euc 2 →L[ℝ] Euc 2)
  have hD : ContinuousWithinAt D S 0 :=
    (hf.continuousOn_fderivWithin hS le_rfl 0 hz).sub continuousWithinAt_const
  have hDzero : D 0 = 0 := by simp only [D, hzero, sub_self]
  have hsmall : ∀ᶠ x in 𝓝[S] (0 : Euc 2), ‖D x‖ < ε := by
    exact hD.norm.tendsto.eventually (gt_mem_nhds (by simpa [hDzero] using hε))
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.mem_nhdsWithin_iff.mp hsmall
  let r := min δ R
  have hr : 0 < r := lt_min hδ hR
  have hrR : r ≤ R := min_le_right _ _
  let T := Metric.ball (0 : Euc 2) r ∩ planarSector θ
  have hTS : T ⊆ S := fun _ hx => ⟨Metric.ball_subset_ball hrR hx.1, hx.2⟩
  have hDsmall (x : Euc 2) (hx : x ∈ T) : ‖D x‖ ≤ ε := by
    exact (hδsmall ⟨Metric.ball_subset_ball (min_le_left δ R) hx.1, hTS hx⟩).le
  have hdiff (x : Euc 2) (hx : x ∈ T) :
      HasFDerivWithinAt (f - ⇑f₀) (D x) T x := by
    exact (((hf.differentiableOn (by norm_num)) x (hTS hx)).hasFDerivWithinAt.sub
      f₀.hasFDerivAt.hasFDerivWithinAt).mono hTS
  have hlip : LipschitzOnWith c (f - ⇑f₀) T := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro x hx y hy
    have hb := hbound r ε (f - ⇑f₀) D hε.le hdiff hDsmall x hx y hy
    have he : L * ε = c := by dsimp [ε]; field_simp
    simpa only [he] using hb
  obtain ⟨H, hH⟩ := hlip.approximatesLinearOn.exists_homeomorph_extension (Or.inr hac)
  exact ⟨r, hr, hrR, H, hH⟩

/-- The inverse of the projected native sector is C1 on its actual curved
image. All derivatives are relative to the indicated domains. -/
theorem C1_sector_inverse_on_image
    (θ R : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) (hR : 0 < R)
    (f : Euc 2 → Euc 2) (f₀ : Euc 2 ≃L[ℝ] Euc 2)
    (hf : ContDiffOn ℝ 1 f (Metric.ball 0 R ∩ planarSector θ))
    (hf₀ : HasFDerivWithinAt f (f₀ : Euc 2 →L[ℝ] Euc 2)
      (Metric.ball 0 R ∩ planarSector θ) 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∃ H : Euc 2 ≃ₜ Euc 2,
      EqOn f H (Metric.ball 0 r ∩ planarSector θ) ∧
      ContDiffOn ℝ 1 H.symm (f '' (Metric.ball 0 r ∩ planarSector θ)) ∧
      UniqueDiffOn ℝ (f '' (Metric.ball 0 r ∩ planarSector θ)) := by
  let S := Metric.ball (0 : Euc 2) R ∩ planarSector θ
  have hS : UniqueDiffOn ℝ S := by
    simpa only [S, inter_comm] using
      (planarSector_uniqueDiffOn hθ hθπ).inter (Metric.isOpen_ball (x := (0 : Euc 2)) (ε := R))
  have hz : (0 : Euc 2) ∈ S := ⟨Metric.mem_ball_self hR,
    0, le_rfl, 0, ⟨le_rfl, hθ.le⟩, by simp⟩
  have hzero : fderivWithin ℝ f S 0 = (f₀ : Euc 2 →L[ℝ] Euc 2) :=
    hf₀.fderivWithin (hS 0 hz)
  have hu : ∀ᶠ x in 𝓝[S] (0 : Euc 2), IsUnit (fderivWithin ℝ f S x) :=
    (hf.continuousOn_fderivWithin hS le_rfl 0 hz).tendsto.eventually
      (Units.isOpen.mem_nhds (by rw [hzero]; exact ContinuousLinearMap.isUnit_iff_bijective.mpr f₀.bijective))
  obtain ⟨δ, hδ, hδunit⟩ := Metric.mem_nhdsWithin_iff.mp hu
  obtain ⟨r₀, hr₀, hr₀R, H, hH⟩ := C1_sector_local_homeomorph_extension θ R hθ hθπ hR f f₀ hf hf₀
  let r := min δ r₀
  have hr : 0 < r := lt_min hδ hr₀
  have hrR : r ≤ R := (min_le_right δ r₀).trans hr₀R
  let T := Metric.ball (0 : Euc 2) r ∩ planarSector θ
  have hTS : T ⊆ S := fun _ hx => ⟨Metric.ball_subset_ball hrR hx.1, hx.2⟩
  have hT : UniqueDiffOn ℝ T := by
    simpa only [T, inter_comm] using
      (planarSector_uniqueDiffOn hθ hθπ).inter (Metric.isOpen_ball (x := (0 : Euc 2)) (ε := r))
  have hHT : EqOn f H T := by
    intro x hx
    exact hH ⟨Metric.ball_subset_ball (min_le_right δ r₀) hx.1, hx.2⟩
  have hbij (x : Euc 2) (hx : x ∈ T) : Function.Bijective (fderivWithin ℝ f S x) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp
      (hδunit ⟨Metric.ball_subset_ball (min_le_left δ r₀) hx.1, hTS hx⟩)
  have hd (x : Euc 2) (hx : x ∈ T) :
      HasFDerivWithinAt f (fderivWithin ℝ f S x) T x :=
    ((hf.differentiableOn (by norm_num)) x (hTS hx)).hasFDerivWithinAt.mono hTS
  have himage : UniqueDiffOn ℝ (f '' T) := by
    rintro y ⟨x, hx, rfl⟩
    exact (hd x hx).uniqueDiffWithinAt (hT x hx) (hbij x hx).surjective.denseRange
  have hmaps : MapsTo H.symm (f '' T) T := by
    rintro y ⟨x, hx, rfl⟩
    rw [hHT hx, H.symm_apply_apply]
    exact hx
  have heq : ∀ y ∈ f '' T, f (H.symm y) = id y := by
    intro y hy
    rw [hHT (hmaps hy), H.apply_symm_apply]
    rfl
  have hinj (x : Euc 2) (hx : x ∈ T) : Function.Injective (fderivWithin ℝ f T x) := by
    rw [(hd x hx).fderivWithin (hT x hx)]
    exact (hbij x hx).injective
  have hq := C1_lift_through_relative_immersion T (f '' T) hT himage f id H.symm
    (hf.mono hTS) contDiffOn_id hinj H.symm.continuous.continuousOn hmaps heq
  exact ⟨r, hr, hrR, H, hHT, hq.1, himage⟩

/-- Project a C1 native sector to any plane transverse to its tangent kernel.
The resulting C1 section parametrizes exactly the original local image. -/
theorem C1_sector_graph_of_transverse_projection
    (θ R : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) (hR : 0 < R)
    (G : Euc 2 → Euc 3) (P : Euc 3 →L[ℝ] Euc 2)
    (hG : ContDiffOn ℝ 1 G (Metric.ball 0 R ∩ planarSector θ))
    (hP : Function.Bijective (P.comp
      (fderivWithin ℝ G (Metric.ball 0 R ∩ planarSector θ) 0))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∃ H : Euc 2 ≃ₜ Euc 2,
      EqOn (P ∘ G) H (Metric.ball 0 r ∩ planarSector θ) ∧
      UniqueDiffOn ℝ ((P ∘ G) '' (Metric.ball 0 r ∩ planarSector θ)) ∧
      ContDiffOn ℝ 1 (G ∘ H.symm) ((P ∘ G) '' (Metric.ball 0 r ∩ planarSector θ)) ∧
      (∀ y ∈ (P ∘ G) '' (Metric.ball 0 r ∩ planarSector θ), P (G (H.symm y)) = y) ∧
      (G ∘ H.symm) '' ((P ∘ G) '' (Metric.ball 0 r ∩ planarSector θ)) =
        G '' (Metric.ball 0 r ∩ planarSector θ) := by
  let S := Metric.ball (0 : Euc 2) R ∩ planarSector θ
  have hz : (0 : Euc 2) ∈ S := ⟨Metric.mem_ball_self hR,
    0, le_rfl, 0, ⟨le_rfl, hθ.le⟩, by simp⟩
  let f₀ := ContinuousLinearEquiv.ofBijective
    (P.comp (fderivWithin ℝ G S 0))
      (LinearMap.ker_eq_bot.mpr hP.injective) (LinearMap.range_eq_top.mpr hP.surjective)
  have hf : ContDiffOn ℝ 1 (P ∘ G) S := P.contDiff.comp_contDiffOn hG
  have hf₀ : HasFDerivWithinAt (P ∘ G) (f₀ : Euc 2 →L[ℝ] Euc 2) S 0 :=
    P.hasFDerivAt.comp_hasFDerivWithinAt 0
      ((hG.differentiableOn (by norm_num)) 0 hz).hasFDerivWithinAt
  obtain ⟨r, hr, hrR, H, hH, hq, himage⟩ :=
    C1_sector_inverse_on_image θ R hθ hθπ hR (P ∘ G) f₀ hf hf₀
  let T := Metric.ball (0 : Euc 2) r ∩ planarSector θ
  have hTS : T ⊆ S := fun _ hx => ⟨Metric.ball_subset_ball hrR hx.1, hx.2⟩
  have hmaps : MapsTo H.symm ((P ∘ G) '' T) T := by
    rintro y ⟨x, hx, rfl⟩
    rw [hH hx, H.symm_apply_apply]
    exact hx
  refine ⟨r, hr, hrR, H, hH, himage, (hG.mono hTS).comp hq hmaps, ?_, ?_⟩
  · intro y hy
    change (P ∘ G) (H.symm y) = y
    rw [hH (hmaps hy), H.apply_symm_apply]
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨H.symm y, hmaps hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(P ∘ G) x, ⟨x, hx, rfl⟩, ?_⟩
      change G (H.symm ((P ∘ G) x)) = G x
      rw [hH hx, H.symm_apply_apply]

/-- Rank at a native sector vertex produces an actual transverse projection;
no parametrization of its projected boundary is supplied as a hypothesis. -/
theorem C1_sector_rank_projection
    (θ R : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) (hR : 0 < R)
    (G : Euc 2 → Euc 3)
    (hG : ContDiffOn ℝ 1 G (Metric.ball 0 R ∩ planarSector θ))
    (hrank : Function.Injective
      (fderivWithin ℝ G (Metric.ball 0 R ∩ planarSector θ) 0)) :
    ∃ P : Euc 3 →L[ℝ] Euc 2,
      P.comp (fderivWithin ℝ G (Metric.ball 0 R ∩ planarSector θ) 0) =
        ContinuousLinearMap.id ℝ (Euc 2) ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∃ H : Euc 2 ≃ₜ Euc 2,
        EqOn (P ∘ G) H (Metric.ball 0 r ∩ planarSector θ) ∧
        UniqueDiffOn ℝ ((P ∘ G) '' (Metric.ball 0 r ∩ planarSector θ)) ∧
        ContDiffOn ℝ 1 (G ∘ H.symm) ((P ∘ G) '' (Metric.ball 0 r ∩ planarSector θ)) ∧
        (∀ y ∈ (P ∘ G) '' (Metric.ball 0 r ∩ planarSector θ), P (G (H.symm y)) = y) ∧
        (G ∘ H.symm) '' ((P ∘ G) '' (Metric.ball 0 r ∩ planarSector θ)) =
          G '' (Metric.ball 0 r ∩ planarSector θ) := by
  let D := fderivWithin ℝ G (Metric.ball 0 R ∩ planarSector θ) 0
  obtain ⟨L, hL⟩ := D.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hrank)
  let P : Euc 3 →L[ℝ] Euc 2 := L.toContinuousLinearMap
  have hPD : P.comp D = ContinuousLinearMap.id ℝ (Euc 2) := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun A : Euc 2 →ₗ[ℝ] Euc 2 => A v) hL
  refine ⟨P, hPD, C1_sector_graph_of_transverse_projection θ R hθ hθπ hR G P hG ?_⟩
  change Function.Bijective (P.comp D)
  rw [hPD]
  exact Function.bijective_id

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
