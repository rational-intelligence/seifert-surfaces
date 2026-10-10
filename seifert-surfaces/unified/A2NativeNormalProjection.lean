import AppendixACoordinatesReady

set_option autoImplicit false
open Set Matrix
open scoped BigOperators
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.A2NativeNormalProjection
open SeifertSurfaces.AppendixACoordinates

private theorem inner_sum_left (g : MetricTensor) (y : E3)
    (v : Fin 2 → E3) (w : E3) :
    coordinateInner g y (∑ i, v i) w = ∑ i, coordinateInner g y (v i) w := by
  simp only [Fin.sum_univ_two, coordinateInner_add_left]

private theorem inner_sub_left (g : MetricTensor) (y u v w : E3) :
    coordinateInner g y (u - v) w = coordinateInner g y u w - coordinateInner g y v w := by
  simp only [coordinateInner, PiLp.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]

private theorem inner_symmetric (g : MetricTensor) (y : E3)
    (hs : ∀ a b, g y a b = g y b a) (v w : E3) :
    coordinateInner g y v w = coordinateInner g y w v := by
  simp only [coordinateInner, Fin.sum_univ_three, hs]
  ring

/-- Metric projection onto the range of the actual rank-two coordinate differential. -/
def tangentProjection (g : MetricTensor) (y : E3) (L : E2 →L[ℝ] E3) (H : E3) : E3 :=
  let v := fun i : Fin 2 => L (coordinateVector 2 i)
  let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j => coordinateInner g y (v i) (v j)
  ∑ i : Fin 2, (∑ j : Fin 2, A⁻¹ i j * coordinateInner g y (v j) H) • v i

def normalProjection (g : MetricTensor) (y : E3) (L : E2 →L[ℝ] E3) (H : E3) : E3 :=
  H - tangentProjection g y L H

theorem tangentProjection_mem_range (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (H : E3) :
    tangentProjection g y L H ∈ LinearMap.range L.toLinearMap := by
  classical
  let v := fun i : Fin 2 => L (coordinateVector 2 i)
  let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j => coordinateInner g y (v i) (v j)
  refine ⟨∑ i : Fin 2, (∑ j : Fin 2, A⁻¹ i j * coordinateInner g y (v j) H) •
    coordinateVector 2 i, ?_⟩
  simp only [map_sum, map_smul, ContinuousLinearMap.coe_coe]
  rfl

theorem normalProjection_orthogonal (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (H : E3) (hs : ∀ a b, g y a b = g y b a)
    (hA : (show Matrix (Fin 2) (Fin 2) ℝ from fun i j => coordinateInner g y
      (L (coordinateVector 2 i)) (L (coordinateVector 2 j))).PosDef) :
    ∀ w : E2, coordinateInner g y (normalProjection g y L H) (L w) = 0 := by
  classical
  let v := fun i : Fin 2 => L (coordinateVector 2 i)
  let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j => coordinateInner g y (v i) (v j)
  let b : Fin 2 → ℝ := fun i => coordinateInner g y (v i) H
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have hcoeff (k : Fin 2) :
      (∑ i : Fin 2, A k i * (∑ j : Fin 2, A⁻¹ i j * b j)) = b k := by
    change (A *ᵥ (A⁻¹ *ᵥ b)) k = b k
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hbase (k : Fin 2) :
      coordinateInner g y (normalProjection g y L H) (v k) = 0 := by
    change coordinateInner g y
      (H - ∑ i : Fin 2, (∑ j : Fin 2, A⁻¹ i j * b j) • v i) (v k) = 0
    rw [inner_sub_left, inner_sum_left]
    simp only [coordinateInner_smul_left]
    have hswap (i : Fin 2) : coordinateInner g y (v i) (v k) = A k i :=
      inner_symmetric g y hs (v i) (v k)
    simp only [hswap]
    have hsum : (∑ i : Fin 2,
        (∑ j : Fin 2, A⁻¹ i j * b j) * A k i) = b k := by
      simpa only [mul_comm] using hcoeff k
    change coordinateInner g y H (v k) -
      (∑ i : Fin 2, (∑ j : Fin 2, A⁻¹ i j * b j) * A k i) = 0
    rw [hsum, inner_symmetric g y hs H (v k)]
    exact sub_self _
  intro w
  have hw : w = ∑ k : Fin 2, w k • coordinateVector 2 k := by
    ext k
    fin_cases k <;> simp [coordinateVector, EuclideanSpace.single]
  rw [hw, map_sum]
  rw [inner_symmetric g y hs]
  rw [inner_sum_left]
  simp only [map_smul, coordinateInner_smul_left]
  apply Finset.sum_eq_zero
  intro k hk
  rw [inner_symmetric g y hs]
  rw [hbase]
  exact mul_zero _

theorem normalProjection_zero_iff_range (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (H : E3) (hs : ∀ a b, g y a b = g y b a)
    (hp : ∀ v : E3, v ≠ 0 → 0 < coordinateInner g y v v)
    (hA : (show Matrix (Fin 2) (Fin 2) ℝ from fun i j => coordinateInner g y
      (L (coordinateVector 2 i)) (L (coordinateVector 2 j))).PosDef) :
    normalProjection g y L H = 0 ↔ H ∈ LinearMap.range L.toLinearMap := by
  constructor
  · intro hn
    have h := sub_eq_zero.mp hn
    rw [h]
    exact tangentProjection_mem_range g y L H
  · intro hH
    obtain ⟨w, hw⟩ := hH
    obtain ⟨z, hz⟩ := tangentProjection_mem_range g y L H
    change L w = H at hw
    change L z = tangentProjection g y L H at hz
    have hn : normalProjection g y L H = L (w - z) := by
      simp only [normalProjection, map_sub, hw, hz]
    by_contra hne
    have hpos := hp (normalProjection g y L H) hne
    have hzero := normalProjection_orthogonal g y L H hs hA (w - z)
    rw [← hn] at hzero
    linarith

theorem normalProjection_inner_trace (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (H : E3) (hs : ∀ a b, g y a b = g y b a)
    (hA : (show Matrix (Fin 2) (Fin 2) ℝ from fun i j => coordinateInner g y
      (L (coordinateVector 2 i)) (L (coordinateVector 2 j))).PosDef) :
    coordinateInner g y (normalProjection g y L H) H =
      coordinateInner g y (normalProjection g y L H) (normalProjection g y L H) := by
  obtain ⟨z, hz⟩ := tangentProjection_mem_range g y L H
  change L z = tangentProjection g y L H at hz
  have ho := normalProjection_orthogonal g y L H hs hA z
  rw [hz] at ho
  have hn : H = normalProjection g y L H + tangentProjection g y L H := by
    simp only [normalProjection, sub_add_cancel]
  calc
    coordinateInner g y (normalProjection g y L H) H =
      coordinateInner g y (normalProjection g y L H)
        (normalProjection g y L H + tangentProjection g y L H) := congrArg _ hn
    _ = coordinateInner g y (normalProjection g y L H) (normalProjection g y L H) +
        coordinateInner g y (normalProjection g y L H) (tangentProjection g y L H) := by
      simp only [coordinateInner, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
    _ = _ := by rw [ho, add_zero]

end SeifertSurfaces.OriginalEndpoints.A2NativeNormalProjection
