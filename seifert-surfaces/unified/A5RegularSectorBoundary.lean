import A5BoundaryAngles
import AreaSectorInteriorSupport
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

private theorem unit_norm (t : ℝ) : ‖sectorUnit t‖ = 1 := by
  have he : ‖sectorUnit t‖ ^ 2 = 1 := by
    simp [EuclideanSpace.real_norm_sq_eq, sectorUnit, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]
  nlinarith [norm_nonneg (sectorUnit t)]

private theorem boundary_closed (θ : ℝ) : IsClosed (sectorBoundary θ) :=
  AreaCertificates.sector_boundary_rays_closed θ

private theorem boundary_smul (θ a : ℝ) (ha : 0 ≤ a) {v : Euc 2}
    (hv : v ∈ sectorBoundary θ) : a • v ∈ sectorBoundary θ := by
  obtain ⟨r, hr, he | he⟩ := hv
  · exact ⟨a * r, mul_nonneg ha hr, Or.inl (by rw [he, smul_smul])⟩
  · exact ⟨a * r, mul_nonneg ha hr, Or.inr (by rw [he, smul_smul])⟩

/-- A proper sector boundary contains a nonzero vector and its negative only
when its literal opening is pi. Reflex sectors are included in the argument. -/
theorem sector_boundary_opposite_vectors_angle
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi)
    (v : Euc 2) (hv : v ≠ 0)
    (hplus : v ∈ sectorBoundary θ) (hminus : -v ∈ sectorBoundary θ) : θ = Real.pi := by
  obtain ⟨r, hr, hrv⟩ := hplus
  obtain ⟨s, hs, hsv⟩ := hminus
  have hrnorm : ‖v‖ = r := by
    rcases hrv with he | he <;> rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, unit_norm, mul_one]
  have hsnorm : ‖v‖ = s := by
    rw [← norm_neg v]
    rcases hsv with he | he <;> rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs, unit_norm, mul_one]
  have hrs : s = r := hsnorm.symm.trans hrnorm
  rw [hrs] at hsv
  have hr0 : r ≠ 0 := hrnorm.symm ▸ norm_ne_zero_iff.mpr hv
  have hopp : sectorUnit θ = -sectorUnit 0 := by
    rcases hrv with ha | ha <;> rcases hsv with hb | hb
    · have he : -v = v := hb.trans ha.symm
      exfalso
      apply hv
      ext i
      have hi := congrArg (fun w : Euc 2 => w i) he
      change -(v i) = v i at hi
      change v i = 0
      linarith
    · have he : r • sectorUnit θ = -(r • sectorUnit 0) := hb.symm.trans (congrArg Neg.neg ha)
      have hn := congrArg (fun w : Euc 2 => r⁻¹ • w) he
      simpa [smul_smul, hr0] using hn
    · have he : r • sectorUnit 0 = -(r • sectorUnit θ) := hb.symm.trans (congrArg Neg.neg ha)
      have hn := congrArg (fun w : Euc 2 => r⁻¹ • w) he
      have hu : sectorUnit 0 = -sectorUnit θ := by simpa [smul_smul, hr0] using hn
      simpa using congrArg Neg.neg hu.symm
    · have he : -v = v := hb.trans ha.symm
      exfalso
      apply hv
      ext i
      have hi := congrArg (fun w : Euc 2 => w i) he
      change -(v i) = v i at hi
      change v i = 0
      linarith
  have hcos : Real.cos θ = -1 := by
    simpa [sectorUnit] using congrArg (fun w : Euc 2 => w 0) hopp
  by_cases hle : θ ≤ Real.pi
  · exact Real.strictAntiOn_cos.injOn ⟨hθ.le, hle⟩ ⟨Real.pi_pos.le, le_rfl⟩
      (by simpa only [Real.cos_pi] using hcos)
  · have hcos' : Real.cos (2 * Real.pi - θ) = Real.cos Real.pi := by
      rw [Real.cos_two_pi_sub, hcos, Real.cos_pi]
    have he := Real.strictAntiOn_cos.injOn
      (show 2 * Real.pi - θ ∈ Icc (0 : ℝ) Real.pi by constructor <;> linarith)
      ⟨Real.pi_pos.le, le_rfl⟩ hcos'
    linarith

/-- A regular two-sided differentiable boundary curve cannot pass through a
nonstraight native sector corner. This uses its actual coordinate derivative
and the literal closed sector boundary. -/
theorem regular_curve_through_sector_origin_forces_pi
    (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi)
    (q : ℝ → Euc 2) (v : Euc 2) (hq0 : q 0 = 0)
    (hq : HasDerivAt q v 0) (hv : v ≠ 0)
    (hboundary : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ sectorBoundary θ) : θ = Real.pi := by
  have hplus : v ∈ sectorBoundary θ := by
    apply (boundary_closed θ).mem_of_tendsto hq.tendsto_slope_zero_right
    filter_upwards [hboundary.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)] with t ht htp
    simp only [zero_add, hq0, sub_zero]
    exact boundary_smul θ t⁻¹ (inv_nonneg.mpr htp.le) ht
  have hminus : -v ∈ sectorBoundary θ := by
    apply (boundary_closed θ).mem_of_tendsto hq.tendsto_slope_zero_left.neg
    filter_upwards [hboundary.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin (s := Iio (0 : ℝ)) (a := 0)] with t ht htn
    simp only [zero_add, hq0, sub_zero, ← neg_smul]
    exact boundary_smul θ (-t⁻¹) (neg_nonneg.mpr (inv_nonpos.mpr htn.le)) ht
  exact sector_boundary_opposite_vectors_angle θ hθ hθπ v hv hplus hminus

/-- The same conclusion consumes the literal domain/frontier condition used
by native seam lifts. It also proves that the chart is a boundary chart. -/
theorem regular_curve_in_sector_frontier_forces_pi
    (A : SectorModel) (q : ℝ → Euc 2) (v : Euc 2)
    (hq0 : q 0 = 0) (hq : HasDerivAt q v 0) (hv : v ≠ 0)
    (hboundary : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ A.domain ∩ frontier A.domain) :
    A.interiorChart = false ∧ A.angle = Real.pi := by
  have boundary_mem (z : Euc 2) (hz : z ∈ A.domain ∩ frontier A.domain) : z ∈ A.boundary := by
    by_contra hn
    exact hz.2.2 (by rw [AreaCertificates.sector_model_interior]; exact ⟨hz.1, hn⟩)
  have hqbd : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ A.boundary := hboundary.mono (fun t ht => boundary_mem _ ht)
  have hfalse : A.interiorChart = false := by
    have hzero := hqbd.self_of_nhds
    cases h : A.interiorChart
    · rfl
    · simp [SectorModel.boundary, h] at hzero
  refine ⟨hfalse, regular_curve_through_sector_origin_forces_pi A.angle A.angle_positive
    A.angle_lt_two_pi q v hq0 hq hv ?_⟩
  filter_upwards [hqbd] with t ht
  simpa only [SectorModel.boundary, hfalse, Bool.false_eq_true, ↓reduceIte] using ht.2

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
