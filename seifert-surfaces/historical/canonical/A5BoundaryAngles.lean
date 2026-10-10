import SectorPieces
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
open Set
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-- A consecutive collection of sectors has an opening in `[π,2π)`.
Individual sectors may be reflex. -/
theorem consecutive_sector_opening (angles : List ℝ)
    (hupper : ∀ a ∈ angles, a < 2 * Real.pi)
    (htotal : Real.pi ≤ angles.sum) :
    ∃ before chosen after : List ℝ, angles = before ++ chosen ++ after ∧
      Real.pi ≤ chosen.sum ∧ chosen.sum < 2 * Real.pi := by
  induction angles with
  | nil => simpa using (not_le_of_gt Real.pi_pos htotal)
  | cons a tail ih =>
    by_cases ha : Real.pi ≤ a
    · exact ⟨[], [a], tail, by simp, by simpa using ha,
        by simpa using hupper a (by simp)⟩
    · by_cases ht : Real.pi ≤ tail.sum
      · obtain ⟨before, chosen, after, he, hlo, hhi⟩ :=
          ih (fun b hb => hupper b (by simp [hb])) ht
        refine ⟨a :: before, chosen, after, ?_, hlo, hhi⟩
        simp only [List.cons_append, he]
      · refine ⟨[], a :: tail, [], by simp, htotal, ?_⟩
        simp only [List.sum_cons]
        linarith

private theorem sectorUnit_antipodal (a : ℝ) :
    sectorUnit (a + Real.pi) = -sectorUnit a := by
  ext i
  fin_cases i <;> simp [sectorUnit]

private theorem sectorUnit_rotate (a d : ℝ) :
    sectorUnit (a + d) = Real.cos d • sectorUnit a +
      Real.sin d • sectorUnit (a + Real.pi / 2) := by
  ext i
  fin_cases i <;> simp [sectorUnit, Real.cos_add, Real.sin_add] <;> ring

private theorem sectorUnit_spans (a : ℝ) (x : Euc 2) :
    x = (Real.cos a * x 0 + Real.sin a * x 1) • sectorUnit a +
      (-Real.sin a * x 0 + Real.cos a * x 1) • sectorUnit (a + Real.pi / 2) := by
  have hu := Real.cos_sq_add_sin_sq a
  ext i
  fin_cases i <;> simp [sectorUnit, Real.cos_add, Real.sin_add]
  · linear_combination -(x 0) * hu
  · linear_combination -(x 1) * hu

/-- A nonzero covector cannot be nonnegative on an angular sweep longer than
one half circle. This is the algebraic step after the native A4 conclusion. -/
theorem nonnegative_sector_sweep_le_pi (L : Euc 2 →L[ℝ] ℝ)
    (hL : L ≠ 0) (a b : ℝ)
    (hpositive : ∀ t ∈ Icc a b, 0 ≤ L (sectorUnit t)) :
    b - a ≤ Real.pi := by
  by_contra hn
  have hlong : Real.pi < b - a := lt_of_not_ge hn
  let d := min ((b - a - Real.pi) / 2) (Real.pi / 2)
  have hd : 0 < d := lt_min (by linarith) (by linarith [Real.pi_pos])
  have hdπ : d < Real.pi :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  have hdlength : d ≤ (b - a - Real.pi) / 2 := min_le_left _ _
  have hz (t : ℝ) (ht : a ≤ t) (htπ : t + Real.pi ≤ b) :
      L (sectorUnit t) = 0 := by
    have hlo := hpositive t ⟨ht, by linarith [Real.pi_pos]⟩
    have hhi := hpositive (t + Real.pi) ⟨by linarith [Real.pi_pos], htπ⟩
    rw [sectorUnit_antipodal, map_neg] at hhi
    linarith
  have ha : L (sectorUnit a) = 0 := hz a le_rfl (by linarith)
  have had : L (sectorUnit (a + d)) = 0 := hz (a + d) (by linarith) (by linarith)
  have hs : Real.sin d ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hd hdπ).ne'
  rw [sectorUnit_rotate, map_add, map_smul, map_smul, ha] at had
  have har : L (sectorUnit (a + Real.pi / 2)) = 0 := by
    have hp : Real.sin d * L (sectorUnit (a + Real.pi / 2)) = 0 := by simpa using had
    exact (mul_eq_zero.mp hp).resolve_left hs
  apply hL
  ext x
  rw [sectorUnit_spans a x, map_add, map_smul, map_smul, ha, har]
  simp

/-- Opposite boundary rays and the A4 nonzero radial covector force the
entire positive angular sweep to be exactly `π`. -/
theorem boundary_sector_sweep_eq_pi (L : Euc 2 →L[ℝ] ℝ)
    (hL : L ≠ 0) (a b : ℝ) (hab : a ≤ b)
    (hpositive : ∀ t ∈ Icc a b, 0 ≤ L (sectorUnit t))
    (hends : sectorUnit b = -sectorUnit a) :
    b - a = Real.pi := by
  have hle := nonnegative_sector_sweep_le_pi L hL a b hpositive
  have hc : Real.cos b = -Real.cos a := by
    simpa [sectorUnit] using congrArg (fun x : Euc 2 => x 0) hends
  have hs : Real.sin b = -Real.sin a := by
    simpa [sectorUnit] using congrArg (fun x : Euc 2 => x 1) hends
  have hcos : Real.cos (b - a) = Real.cos Real.pi := by
    rw [Real.cos_sub, hc, hs, Real.cos_pi]
    nlinarith [Real.cos_sq_add_sin_sq a]
  exact Real.strictAntiOn_cos.injOn ⟨sub_nonneg.mpr hab, hle⟩
    ⟨Real.pi_pos.le, le_rfl⟩ hcos

/-- The collar's nonnegative defining function gives a nonnegative derivative
on every ray of the actual closed sector. -/
theorem closed_sector_radial_derivative_nonnegative
    (θ r : ℝ) (hr : 0 < r) (v : Euc 2 → ℝ) (L : Euc 2 →L[ℝ] ℝ)
    (hv0 : v 0 = 0)
    (hv : ∀ x ∈ Metric.ball 0 r ∩ planarSector θ, 0 ≤ v x)
    (hd : HasFDerivWithinAt v L (Metric.ball 0 r ∩ planarSector θ) 0) :
    ∀ t ∈ Icc 0 θ, 0 ≤ L (sectorUnit t) := by
  intro t ht
  have hu : ‖sectorUnit t‖ = 1 := by
    have hs : ‖sectorUnit t‖ ^ 2 = 1 := by
      simp only [EuclideanSpace.real_norm_sq_eq, sectorUnit, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      exact Real.cos_sq_add_sin_sq t
    nlinarith [norm_nonneg (sectorUnit t)]
  have hm : IsMinOn v (Metric.ball 0 r ∩ planarSector θ) 0 := by
    intro x hx
    rw [hv0]
    exact hv x hx
  have hseg : segment ℝ (0 : Euc 2) (0 + (r / 2) • sectorUnit t) ⊆
      Metric.ball 0 r ∩ planarSector θ := by
    rw [zero_add, segment_eq_image_lineMap]
    rintro x ⟨s, hs, rfl⟩
    have he : AffineMap.lineMap (0 : Euc 2) ((r / 2) • sectorUnit t) s =
        (s * (r / 2)) • sectorUnit t := by simp [AffineMap.lineMap_apply_module', smul_smul]
    rw [he]
    have hp : 0 ≤ s * (r / 2) := mul_nonneg hs.1 (by positivity)
    refine ⟨?_, s * (r / 2), hp, t, ht, rfl⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hp, hu, mul_one]
    nlinarith [hs.2]
  have hcone := mem_posTangentConeAt_of_segment_subset hseg
  have hn := hm.isLocalMinOn.hasFDerivWithinAt_nonneg hd hcone
  rw [map_smul] at hn
  change 0 ≤ (r / 2) * L (sectorUnit t) at hn
  exact nonneg_of_mul_nonneg_right hn (by positivity)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
