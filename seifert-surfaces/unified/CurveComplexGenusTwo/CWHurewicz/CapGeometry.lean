import CurveComplexGenusTwo.CWHurewicz.ExcisionClean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Normalize

namespace CurveComplexGenusTwo.CWHurewicz

open scoped InnerProductSpace
open scoped unitInterval

private theorem cap_inner_ge_half {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y v : E) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hd : dist y v ≤ 1) : (1 / 2 : ℝ) ≤ ⟪y, v⟫_ℝ := by
  have hsq : ‖y - v‖ ^ 2 = 2 - 2 * ⟪y, v⟫_ℝ := by
    rw [norm_sub_sq_real, hy, hv]
    ring
  have hdist : ‖y - v‖ ≤ 1 := by simpa [dist_eq_norm] using hd
  have hs : ‖y - v‖ ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdist)
      (add_nonneg (norm_nonneg (y - v)) zero_le_one)]
  nlinarith

private def capSegment {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y v : E) (t : ℝ) : E := (1 - t) • y + t • v

private theorem capSegment_inner_pos {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y v : E) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hd : dist y v ≤ 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < ⟪capSegment y v t, v⟫_ℝ := by
  have ha := cap_inner_ge_half y v hy hv hd
  have hvv : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hlin : ⟪capSegment y v t, v⟫_ℝ =
      (1 - t) * ⟪y, v⟫_ℝ + t := by
    unfold capSegment
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hvv]
    ring
  rw [hlin]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ha)]

private theorem capSegment_ne_zero {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y v : E) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hd : dist y v ≤ 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    capSegment y v t ≠ 0 := by
  intro h
  have hp := capSegment_inner_pos y v hy hv hd t ht0 ht1
  simp [h] at hp

private theorem capSegment_norm_le_one {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y v : E) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖capSegment y v t‖ ≤ 1 := by
  unfold capSegment
  calc
    ‖(1 - t) • y + t • v‖ ≤ ‖(1 - t) • y‖ + ‖t • v‖ := norm_add_le _ _
    _ = 1 := by
      rw [norm_smul, norm_smul, hy, hv]
      simp [abs_of_nonneg ht0, abs_of_nonneg (sub_nonneg.mpr ht1)]

private theorem capSegment_inner_ge_half {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y v : E) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hd : dist y v ≤ 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 / 2 : ℝ) ≤ ⟪capSegment y v t, v⟫_ℝ := by
  have ha := cap_inner_ge_half y v hy hv hd
  have hvv : ⟪v, v⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hlin : ⟪capSegment y v t, v⟫_ℝ =
      (1 - t) * ⟪y, v⟫_ℝ + t := by
    unfold capSegment
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hvv]
    ring
  rw [hlin]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ha)]

private theorem capNormalize_mem_cap {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y v : E) (hy : ‖y‖ = 1) (hv : ‖v‖ = 1)
    (hd : dist y v ≤ 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    dist (NormedSpace.normalize (capSegment y v t)) v ≤ 1 := by
  let u := capSegment y v t
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr
    (capSegment_ne_zero y v hy hv hd t ht0 ht1)
  have hnorm : ‖u‖ ≤ 1 := capSegment_norm_le_one y v hy hv t ht0 ht1
  have hinner : (1 / 2 : ℝ) ≤ ⟪u, v⟫_ℝ :=
    capSegment_inner_ge_half y v hy hv hd t ht0 ht1
  have hscaled : (1 / 2 : ℝ) ≤ ‖u‖⁻¹ * ⟪u, v⟫_ℝ := by
    calc
      (1 / 2 : ℝ) ≤ ⟪u, v⟫_ℝ / ‖u‖ :=
        (le_div_iff₀ hnu).2 (by nlinarith)
      _ = ‖u‖⁻¹ * ⟪u, v⟫_ℝ := by ring
  have hnormed : ‖NormedSpace.normalize u‖ = 1 :=
    NormedSpace.norm_normalize (capSegment_ne_zero y v hy hv hd t ht0 ht1)
  have hinnerNorm : (1 / 2 : ℝ) ≤ ⟪NormedSpace.normalize u, v⟫_ℝ := by
    simpa [NormedSpace.normalize, real_inner_smul_left, div_eq_inv_mul] using hscaled
  have hsq : ‖NormedSpace.normalize u - v‖ ^ 2 =
      2 - 2 * ⟪NormedSpace.normalize u, v⟫_ℝ := by
    rw [norm_sub_sq_real, hnormed, hv]
    ring
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (NormedSpace.normalize u - v)]

def unitCap {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) : Set E := {y | ‖y‖ = 1 ∧ dist y v ≤ 1}

noncomputable def capContraction {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : E) (hv : ‖v‖ = 1) :
    I × unitCap v → unitCap v := fun p =>
  ⟨NormedSpace.normalize (capSegment p.2.val v p.1.val),
    ⟨NormedSpace.norm_normalize
      (capSegment_ne_zero p.2.val v p.2.property.1 hv p.2.property.2
        p.1.val p.1.property.1 p.1.property.2),
      capNormalize_mem_cap p.2.val v p.2.property.1 hv p.2.property.2
        p.1.val p.1.property.1 p.1.property.2⟩⟩

theorem capContraction_continuous {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : E) (hv : ‖v‖ = 1) :
    Continuous (capContraction v hv) := by
  let seg : I × unitCap v → E := fun p => capSegment p.2.val v p.1.val
  have hs : Continuous seg := by
    unfold seg capSegment
    fun_prop
  have hnz : ∀ p, seg p ≠ 0 := by
    intro p
    exact capSegment_ne_zero p.2.val v p.2.property.1 hv p.2.property.2
      p.1.val p.1.property.1 p.1.property.2
  have hnorm : Continuous (fun p => ‖seg p‖⁻¹) :=
    hs.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (hnz p))
  have hnormalized : Continuous (fun p => NormedSpace.normalize (seg p)) := by
    change Continuous (fun p => ‖seg p‖⁻¹ • seg p)
    exact hnorm.smul hs
  exact hnormalized.subtype_mk _

theorem capContraction_zero {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : E) (hv : ‖v‖ = 1) (y : unitCap v) :
    capContraction v hv (0, y) = y := by
  apply Subtype.ext
  simp [capContraction, capSegment, NormedSpace.normalize_eq_self_of_norm_eq_one y.property.1]

theorem capContraction_one {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : E) (hv : ‖v‖ = 1) (y : unitCap v) :
    (capContraction v hv (1, y)).val = v := by
  simp [capContraction, capSegment, NormedSpace.normalize_eq_self_of_norm_eq_one hv]

theorem capContraction_base {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : E) (hv : ‖v‖ = 1) (t : I) :
    (capContraction v hv (t, ⟨v, ⟨hv, by simp⟩⟩)).val = v := by
  have hsum : capSegment v v t.val = v := by
    simp [capSegment, ← add_smul, sub_add_cancel]
  simp [capContraction, hsum, NormedSpace.normalize_eq_self_of_norm_eq_one hv]

end CurveComplexGenusTwo.CWHurewicz
