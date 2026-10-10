import NativeBoundaryLinearDifferenceEquation
import NativeBoundaryHolderCompactAlgebra

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal Interval

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_tangential_quotient_holder_from_within_derivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r) (g : E2 → F) (α C : ℝ≥0)
    (hg : ContDiffOn ℝ 1 g (nativeClosedBoundaryCap c (2 * r)))
    (hH : HolderOnWith C α
      (fun x => fderivWithin ℝ g (nativeClosedBoundaryCap c (2 * r)) x (coordinateVector 2 1))
      (nativeClosedBoundaryCap c (2 * r))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ h : ℝ, h ≠ 0 → |h| < r →
      (∀ x ∈ nativeClosedBoundaryCap c r, ‖h⁻¹ • (g (shift 1 h x) - g x)‖ ≤ B) ∧
      HolderOnWith C α (fun x => h⁻¹ • (g (shift 1 h x) - g x)) (nativeClosedBoundaryCap c r) := by
  let K := nativeClosedBoundaryCap c (2 * r)
  let D := fun x => fderivWithin ℝ g K x (coordinateVector 2 1)
  have hDc : ContinuousOn D K :=
    (hg.continuousOn_fderivWithin (nativeClosedBoundaryCap_uniqueDiffOn c (2 * r) (by positivity) hcf)
      (by norm_num)).clm_apply continuousOn_const
  have hKc : IsCompact K := (isCompact_closedBall c (2 * r)).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  obtain ⟨B0, hB0⟩ := hKc.exists_bound_of_continuousOn hDc
  let B := max B0 0
  refine ⟨B, le_max_right _ _, ?_⟩
  intro h hne hsmall
  have hpath (x : E2) (hx : x ∈ nativeClosedBoundaryCap c r) :
      MapsTo (fun t : ℝ => x + t • (h • coordinateVector 2 1)) (Icc (0 : ℝ) 1) K := by
    intro t ht
    refine ⟨?_, ?_⟩
    · have hn : ‖t • (h • coordinateVector 2 1)‖ ≤ |h| := by
        simp only [norm_smul, Real.norm_eq_abs, QuotientHelpers.coordinate_norm, mul_one, abs_of_nonneg ht.1]
        exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg h)).trans_eq (one_mul _)
      change dist (x + t • (h • coordinateVector 2 1)) c ≤ 2 * r
      have hh := dist_triangle (x + t • (h • coordinateVector 2 1)) x c
      rw [dist_self_add_left] at hh
      have hx' : dist x c ≤ r := hx.1
      linarith
    · change 0 ≤ (x + t • (h • coordinateVector 2 1)) 0
      simpa [coordinateVector] using hx.2
  let G (x : E2) (t : ℝ) := D (x + t • (h • coordinateVector 2 1))
  have hGi (x : E2) (hx : x ∈ nativeClosedBoundaryCap c r) :
      IntervalIntegrable (G x) volume 0 1 :=
    (hDc.comp (by fun_prop) (hpath x hx)).intervalIntegrable_of_Icc (by norm_num)
  have hrep (x : E2) (hx : x ∈ nativeClosedBoundaryCap c r) :
      h⁻¹ • (g (shift 1 h x) - g x) = ∫ t in (0 : ℝ)..1, G x t := by
    have hpC : ContinuousOn (fun t : ℝ => g (x + t • (h • coordinateVector 2 1))) (Icc (0 : ℝ) 1) :=
      hg.continuousOn.comp (by fun_prop) (hpath x hx)
    have hpD (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
        HasDerivWithinAt (fun s => g (x + s • (h • coordinateVector 2 1))) (h • G x t) (Ioi t) t := by
      have hdpath : HasDerivAt (fun s : ℝ => x + s • (h • coordinateVector 2 1))
          (h • coordinateVector 2 1) t := by
        convert (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const (h • coordinateVector 2 1)) using 1 <;>
          simp only [zero_add, one_smul, id_eq]
        funext s
        rfl
      have hgD := (hg.differentiableOn (by norm_num) _ (hpath x hx ⟨ht.1.le, ht.2.le⟩)).hasFDerivWithinAt
      have hcD := hgD.comp_hasDerivWithinAt t hdpath.hasDerivWithinAt (hpath x hx)
      have hAt := hcD.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      convert hAt.hasDerivWithinAt using 1 <;> simp only [map_smul, G, D, K, Function.comp_def]
    have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by norm_num : (0 : ℝ) ≤ 1)
      hpC hpD ((hGi x hx).smul h)
    rw [intervalIntegral.integral_smul] at hi
    simp only [one_smul, zero_smul, add_zero] at hi
    change h • (∫ t in (0 : ℝ)..1, G x t) = g (shift 1 h x) - g x at hi
    rw [← hi, smul_smul, inv_mul_cancel₀ hne, one_smul]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hrep x hx]
    have hb : ∀ t ∈ Ι (0 : ℝ) 1, ‖G x t‖ ≤ B := by
      intro t ht
      exact (hB0 _ (hpath x hx (by simpa using uIoc_subset_uIcc ht))).trans (le_max_left _ _)
    simpa only [sub_zero, abs_one, one_mul, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  · apply native_holder_of_norm_distance_bound
    intro x hx y hy
    rw [hrep x hx, hrep y hy, ← intervalIntegral.integral_sub (hGi x hx) (hGi y hy)]
    have hb : ∀ t ∈ Ι (0 : ℝ) 1, ‖G x t - G y t‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
      intro t ht
      have htt : t ∈ Icc (0 : ℝ) 1 := by simpa using uIoc_subset_uIcc ht
      have hh := hH.dist_le (hpath x hx htt) (hpath y hy htt)
      rw [dist_add_right] at hh
      simpa only [G, D, K, dist_eq_norm] using hh
    simpa only [sub_zero, abs_one, one_mul, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
