import A5SectorBoundaryCoordinates
import AffineHalfStripCalculusProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers
open SeifertSurfaces.LongitudeProducers.QuotientChartHelpers
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

private theorem sin_nonneg_iff_of_small {a : ℝ} (ha : -Real.pi < a) (ha' : a < Real.pi) :
    0 ≤ Real.sin a ↔ 0 ≤ a := by
  constructor
  · intro hs
    by_contra hn
    exact (not_lt_of_ge hs) (Real.sin_neg_of_neg_of_neg_pi_lt (lt_of_not_ge hn) ha)
  · intro hn
    rcases eq_or_lt_of_le hn with he | hp
    · simp [← he]
    · exact (Real.sin_pos_of_pos_of_lt_pi hp ha').le

/-- Near a nonzero point of the actual first native boundary ray, every
sector opening in (0,2pi) is literally the same closed upper halfplane. -/
theorem native_sector_first_ray_local_halfplane
    (A : SectorModel) (ha : A.interiorChart = false)
    (r : ℝ) (hr : 0 < r) (hR : r < A.radius) :
    ∀ᶠ z : Euc 2 in 𝓝 (r • sectorUnit 0), z ∈ A.domain ↔ 0 ≤ z 1 := by
  let x := r • sectorUnit 0
  have hx0 : x ≠ 0 := by
    intro he
    have h := congrArg (fun z : Euc 2 => z 0) he
    simp [x, sectorUnit] at h
    exact hr.ne' h
  have hxsec : x ∈ planarSector A.angle := ⟨r, hr.le, 0, ⟨le_rfl, A.angle_positive.le⟩, rfl⟩
  have hangle : centeredSectorAngle A.angle x = 0 := by
    exact centered_angle_polar A.angle r 0 ⟨A.angle_positive, A.angle_lt_two_pi⟩ hr
      ⟨le_rfl, A.angle_positive.le⟩
  have hac := (centered_angle_smooth_on_sector_nonzero A.angle A.angle_positive
    A.angle_lt_two_pi x hxsec hx0).continuousAt
  have hnear : ∀ᶠ z : Euc 2 in 𝓝 x,
      centeredSectorAngle A.angle z ∈ Ioo (-Real.pi) (min A.angle Real.pi) := by
    apply hac.eventually
    rw [hangle]
    exact isOpen_Ioo.mem_nhds ⟨neg_neg_of_pos Real.pi_pos, lt_min A.angle_positive Real.pi_pos⟩
  have hxball : x ∈ Metric.ball (0 : Euc 2) A.radius := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hn : ‖sectorUnit 0‖ = 1 := by
      simp [sectorUnit, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rwa [hn, mul_one]
  filter_upwards [hnear, Metric.isOpen_ball.mem_nhds hxball,
    isOpen_compl_singleton.mem_nhds hx0] with z hz hzB hz0
  have hrec := congrArg (fun y : Euc 2 => y 1) (centered_polar_reconstruction A.angle z)
  have hcoord : z 1 = ‖z‖ * Real.sin (centeredSectorAngle A.angle z) := by
    simpa [polarPoint] using hrec.symm
  simp only [SectorModel.domain, ha, Bool.false_eq_true, ↓reduceIte,
    mem_inter_iff, and_iff_right hzB]
  rw [planar_sector_iff_centered_angle A.angle A.angle_positive A.angle_lt_two_pi z hz0,
    mem_Icc, and_iff_left (le_of_lt (hz.2.trans_le (min_le_left _ _))), hcoord,
    mul_nonneg_iff_of_pos_left (norm_pos_iff.mpr hz0)]
  exact (sin_nonneg_iff_of_small hz.1 (hz.2.trans_le (min_le_right _ _))).symm

/-- Near the second actual boundary ray the inward halfplane is clockwise
from that ray, including native reflex openings. -/
theorem native_sector_second_ray_local_halfplane
    (A : SectorModel) (ha : A.interiorChart = false)
    (r : ℝ) (hr : 0 < r) (hR : r < A.radius) :
    ∀ᶠ z : Euc 2 in 𝓝 (r • sectorUnit A.angle),
      z ∈ A.domain ↔ 0 ≤ Real.sin A.angle * z 0 - Real.cos A.angle * z 1 := by
  let x := r • sectorUnit A.angle
  have hn : ‖sectorUnit A.angle‖ = 1 := by
    have hs : ‖sectorUnit A.angle‖ ^ 2 = 1 := by
      simp [EuclideanSpace.real_norm_sq_eq, sectorUnit, Fin.sum_univ_two,
        Real.cos_sq_add_sin_sq]
    nlinarith [norm_nonneg (sectorUnit A.angle)]
  have hx0 : x ≠ 0 := smul_ne_zero hr.ne' (norm_ne_zero_iff.mp (by rw [hn]; norm_num))
  have hxsec : x ∈ planarSector A.angle :=
    ⟨r, hr.le, A.angle, ⟨A.angle_positive.le, le_rfl⟩, rfl⟩
  have hangle : centeredSectorAngle A.angle x = A.angle := by
    exact centered_angle_polar A.angle r A.angle ⟨A.angle_positive, A.angle_lt_two_pi⟩ hr
      ⟨A.angle_positive.le, le_rfl⟩
  have hac := (centered_angle_smooth_on_sector_nonzero A.angle A.angle_positive
    A.angle_lt_two_pi x hxsec hx0).continuousAt
  have hnear : ∀ᶠ z : Euc 2 in 𝓝 x,
      A.angle - centeredSectorAngle A.angle z ∈ Ioo (-Real.pi) (min A.angle Real.pi) := by
    apply (continuousAt_const.sub hac).eventually
    simp only [Pi.sub_apply]
    rw [hangle, sub_self]
    exact isOpen_Ioo.mem_nhds ⟨neg_neg_of_pos Real.pi_pos, lt_min A.angle_positive Real.pi_pos⟩
  have hxball : x ∈ Metric.ball (0 : Euc 2) A.radius := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hn, mul_one]
    exact hR
  filter_upwards [hnear, Metric.isOpen_ball.mem_nhds hxball,
    isOpen_compl_singleton.mem_nhds hx0] with z hz hzB hz0
  have hrec := centered_polar_reconstruction A.angle z
  have hcoord : Real.sin A.angle * z 0 - Real.cos A.angle * z 1 =
      ‖z‖ * Real.sin (A.angle - centeredSectorAngle A.angle z) := by
    have h0 := congrArg (fun y : Euc 2 => y 0) hrec
    have h1 := congrArg (fun y : Euc 2 => y 1) hrec
    simp only [polarPoint, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    rw [← h0, ← h1, Real.sin_sub]
    ring
  have hangpos : 0 ≤ centeredSectorAngle A.angle z := by
    have hh := hz.2.trans_le (min_le_left _ _)
    linarith
  simp only [SectorModel.domain, ha, Bool.false_eq_true, ↓reduceIte,
    mem_inter_iff, and_iff_right hzB]
  rw [planar_sector_iff_centered_angle A.angle A.angle_positive A.angle_lt_two_pi z hz0,
    mem_Icc, and_iff_right hangpos, hcoord,
    mul_nonneg_iff_of_pos_left (norm_pos_iff.mpr hz0),
    sin_nonneg_iff_of_small hz.1 (hz.2.trans_le (min_le_right _ _)), sub_nonneg]

theorem native_sector_orthonormal_boundary_frame
    (A : SectorModel) (x : Euc 2) (hx : x ∈ A.domain ∩ frontier A.domain)
    (hregular : x ≠ 0 ∨ A.angle = Real.pi) :
    ∃ e m : Euc 2, ‖e‖ = 1 ∧ ‖m‖ = 1 ∧ inner ℝ e m = 0 ∧
      inner ℝ m x = 0 ∧ (∀ᶠ z in 𝓝 x, z ∈ A.domain ↔ 0 ≤ inner ℝ m z) := by
  have hxb : x ∈ A.boundary := by
    by_contra hn
    exact hx.2.2 (by rw [AreaCertificates.sector_model_interior]; exact ⟨hx.1, hn⟩)
  have ha : A.interiorChart = false := by
    cases h : A.interiorChart
    · rfl
    · simp [SectorModel.boundary, h] at hxb
  have hframe0 : ‖(!₂[1, 0] : Euc 2)‖ = 1 ∧ ‖(!₂[0, 1] : Euc 2)‖ = 1 ∧
      inner ℝ (!₂[1, 0] : Euc 2) !₂[0, 1] = 0 := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, PiLp.inner_apply]
  by_cases hx0 : x = 0
  · subst x
    have hpi : A.angle = Real.pi := hregular.resolve_left (by simp)
    refine ⟨!₂[1, 0], !₂[0, 1], hframe0.1, hframe0.2.1, hframe0.2.2, by simp, ?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : Euc 2) A.radius_positive] with z hz
    simp [SectorModel.domain, ha, hpi, planar_sector_pi_upper_halfplane, hz,
      PiLp.inner_apply, Fin.sum_univ_two]
  have hbd : x ∈ sectorBoundary A.angle := by simpa [SectorModel.boundary, ha] using hxb.2
  obtain ⟨r, hr, he | he⟩ := hbd
  all_goals
    have hrp : 0 < r := lt_of_le_of_ne hr (by intro h; apply hx0; rw [he, ← h, zero_smul])
    have hR : r < A.radius := by
      have hxR : ‖x‖ < A.radius := by simpa only [Metric.mem_ball, dist_zero_right] using hx.1.1
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hrp] at hxR
      simpa [sectorUnit, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.cos_sq_add_sin_sq] using hxR
  · refine ⟨!₂[1, 0], !₂[0, 1], hframe0.1, hframe0.2.1, hframe0.2.2, ?_, ?_⟩
    · simp [he, sectorUnit, PiLp.inner_apply, Fin.sum_univ_two]
    · have h := native_sector_first_ray_local_halfplane A ha r hrp hR
      rw [← he] at h
      simpa [PiLp.inner_apply, Fin.sum_univ_two] using h
  · let e := sectorUnit A.angle
    let m : Euc 2 := !₂[Real.sin A.angle, -Real.cos A.angle]
    have heunit : ‖e‖ = 1 := by
      have hs : ‖e‖ ^ 2 = 1 := by simp [e, EuclideanSpace.real_norm_sq_eq, sectorUnit, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]
      nlinarith [norm_nonneg e]
    have hmunit : ‖m‖ = 1 := by
      have hs : ‖m‖ ^ 2 = 1 := by simp [m, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]
      nlinarith [norm_nonneg m]
    have hem : inner ℝ e m = 0 := by simp [e, m, sectorUnit, PiLp.inner_apply, Fin.sum_univ_two]; ring
    refine ⟨e, m, heunit, hmunit, hem, ?_, ?_⟩
    · rw [he, inner_smul_right]
      have hme : inner ℝ m (sectorUnit A.angle) = 0 := by rw [real_inner_comm]; exact hem
      rw [hme, mul_zero]
    · have h := native_sector_second_ray_local_halfplane A ha r hrp hR
      rw [← he] at h
      simpa [m, PiLp.inner_apply, Fin.sum_univ_two, sub_eq_add_neg, mul_comm] using h

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
