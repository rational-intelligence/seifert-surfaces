import DiagramExtensionHelpers
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Pi
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1600000
open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers.DiagramRemainingHelpers
open Foundations MetricFoundations
noncomputable section

/-- X1: finite C1 data, including the actual within derivative on closed corners. -/
structure FiniteC1RectangleExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : Euc 2) (F : Euc 2 → E) where
  neighborhood : Set (Euc 2)
  neighborhood_open : IsOpen neighborhood
  rectangle_inside : euclideanRectangle a b ⊆ neighborhood
  map : Euc 2 → E
  c1 : ContDiffOn ℝ 1 map neighborhood
  values : EqOn map F (euclideanRectangle a b)
  derivative : ∀ x ∈ euclideanRectangle a b,
    fderiv ℝ map x = fderivWithin ℝ F (euclideanRectangle a b) x

def firstCoordinateReflection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Euc 2 → E) (x : Euc 2) : E :=
  (3 : ℝ) • F !₂[-x 0, x 1] - (2 : ℝ) • F !₂[-2 * x 0, x 1]

def secondCoordinateReflection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Euc 2 → E) (x : Euc 2) : E :=
  (3 : ℝ) • F !₂[x 0, -x 1] - (2 : ℝ) • F !₂[x 0, -2 * x 1]

theorem nondegenerate_rectangle_unique_diff (a b : Euc 2) (hab : ∀ j, a j < b j) :
    UniqueDiffOn ℝ (euclideanRectangle a b) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  have hrectangle : euclideanRectangle a b = e ⁻¹' Set.pi Set.univ (fun j => Icc (a j) (b j)) := by
    ext x
    change (∀ j, a j ≤ x j ∧ x j ≤ b j) ↔ _
    simp only [Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, Set.mem_Icc, forall_true_left]
    rfl
  rw [hrectangle]
  exact e.uniqueDiffOn_preimage_iff.mpr
    (UniqueDiffOn.univ_pi fun j => uniqueDiffOn_Icc (hab j))

end
end SeifertSurfaces.LongitudeProducers.DiagramRemainingHelpers

-- Preserve the certified helper declarations' compiler-generated binder names.
run_cmd Lean.modifyEnv fun env =>
  Lean.Meta.auxLemmasExt.modifyState (env.setMainModule `DiagramFiniteC1Interfaces) fun _ => {}

namespace SeifertSurfaces.LongitudeProducers.DiagramExtensionRoundingHelpers
open Foundations MetricFoundations DiagramRemainingHelpers
noncomputable section

/-- The literal first-coordinate union, with the left value used on the seam. -/
def closedHalfStripUnion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : Euc 2 → E) (x : Euc 2) : E :=
  if x 0 ≤ 0 then F x else G x

/-- Finite C1 gluing on two nondegenerate closed half rectangles. -/
theorem finite_c1_closed_half_strip_gluing {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (leftWidth rightWidth lower upper : ℝ)
    (hleft : 0 < leftWidth) (hright : 0 < rightWidth) (hvertical : lower < upper)
    (F G : Euc 2 → E)
    (hF : ContDiffOn ℝ 1 F (euclideanRectangle !₂[-leftWidth, lower] !₂[0, upper]))
    (hG : ContDiffOn ℝ 1 G (euclideanRectangle !₂[0, lower] !₂[rightWidth, upper]))
    (hvalues : ∀ y ∈ Icc lower upper, F !₂[0, y] = G !₂[0, y])
    (hjet : ∀ y ∈ Icc lower upper,
      fderivWithin ℝ F (euclideanRectangle !₂[-leftWidth, lower] !₂[0, upper]) !₂[0, y] =
        fderivWithin ℝ G (euclideanRectangle !₂[0, lower] !₂[rightWidth, upper]) !₂[0, y]) :
    ContDiffOn ℝ 1 (closedHalfStripUnion F G)
      (euclideanRectangle !₂[-leftWidth, lower] !₂[rightWidth, upper]) ∧
    (∀ x ∈ euclideanRectangle !₂[-leftWidth, lower] !₂[0, upper],
      fderivWithin ℝ (closedHalfStripUnion F G)
        (euclideanRectangle !₂[-leftWidth, lower] !₂[rightWidth, upper]) x =
          fderivWithin ℝ F (euclideanRectangle !₂[-leftWidth, lower] !₂[0, upper]) x) ∧
    (∀ x ∈ euclideanRectangle !₂[0, lower] !₂[rightWidth, upper],
      fderivWithin ℝ (closedHalfStripUnion F G)
        (euclideanRectangle !₂[-leftWidth, lower] !₂[rightWidth, upper]) x =
          fderivWithin ℝ G (euclideanRectangle !₂[0, lower] !₂[rightWidth, upper]) x) := by
  classical
  let L := euclideanRectangle !₂[-leftWidth, lower] !₂[0, upper]
  let R := euclideanRectangle !₂[0, lower] !₂[rightWidth, upper]
  let T := euclideanRectangle !₂[-leftWidth, lower] !₂[rightWidth, upper]
  let U := closedHalfStripUnion F G
  have unique (a b : Euc 2) (hab : ∀ j, a j < b j) :
      UniqueDiffOn ℝ (euclideanRectangle a b) := by
    have hs : euclideanRectangle a b = ((EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹'
        (Set.pi univ (fun j => Icc (a j) (b j)))) := by
      ext x
      change (∀ j, a j ≤ x j ∧ x j ≤ b j) ↔
        (∀ j ∈ (univ : Set (Fin 2)), a j ≤ x j ∧ x j ≤ b j)
      exact ⟨fun h j _ => h j, fun h j => h j (mem_univ _)⟩
    rw [hs]
    exact (EuclideanSpace.equiv (Fin 2) ℝ).uniqueDiffOn_preimage_iff.mpr
      (UniqueDiffOn.univ_pi fun j => uniqueDiffOn_Icc (hab j))
  have closed (a b : Euc 2) : IsClosed (euclideanRectangle a b) := by
    have hs : euclideanRectangle a b = ⋂ j : Fin 2, {x : Euc 2 | a j ≤ x j ∧ x j ≤ b j} := by
      ext x
      exact ⟨fun hx => mem_iInter.mpr hx, fun hx => mem_iInter.mp hx⟩
    rw [hs]
    exact isClosed_iInter fun j =>
      (isClosed_le continuous_const (EuclideanSpace.proj j).continuous).inter
        (isClosed_le (EuclideanSpace.proj j).continuous continuous_const)
  have uL : UniqueDiffOn ℝ L := unique _ _ (by
    intro j; fin_cases j
    · change -leftWidth < 0; linarith
    · exact hvertical)
  have uR : UniqueDiffOn ℝ R := unique _ _ (by
    intro j; fin_cases j
    · exact hright
    · exact hvertical)
  have uT : UniqueDiffOn ℝ T := unique _ _ (by
    intro j; fin_cases j
    · change -leftWidth < rightWidth; linarith
    · exact hvertical)
  have cL : IsClosed L := closed _ _
  have cR : IsClosed R := closed _ _
  have hLT : L ⊆ T := by
    intro x hx j
    fin_cases j
    · have h := hx 0
      change -leftWidth ≤ x 0 ∧ x 0 ≤ rightWidth
      change -leftWidth ≤ x 0 ∧ x 0 ≤ 0 at h
      exact ⟨h.1, h.2.trans hright.le⟩
    · exact hx 1
  have hRT : R ⊆ T := by
    intro x hx j
    fin_cases j
    · have h := hx 0
      change -leftWidth ≤ x 0 ∧ x 0 ≤ rightWidth
      change 0 ≤ x 0 ∧ x 0 ≤ rightWidth at h
      exact ⟨(by linarith [h.1]), h.2⟩
    · exact hx 1
  have hT : T = L ∪ R := by
    apply Subset.antisymm
    · intro x hx
      by_cases h : x 0 ≤ 0
      · left
        intro j; fin_cases j
        · exact ⟨(hx 0).1, h⟩
        · exact hx 1
      · right
        intro j; fin_cases j
        · exact ⟨le_of_lt (lt_of_not_ge h), (hx 0).2⟩
        · exact hx 1
    · exact union_subset hLT hRT
  have seam (x : Euc 2) (h : x 0 = 0) : x = !₂[0, x 1] := by
    ext j; fin_cases j
    · exact h
    · rfl
  have eqL : EqOn U F L := by
    intro x hx
    exact if_pos (hx 0).2
  have eqR : EqOn U G R := by
    intro x hx
    change (if x 0 ≤ 0 then F x else G x) = G x
    by_cases h : x 0 ≤ 0
    · rw [if_pos h]
      have hzero : x 0 = 0 := le_antisymm h (hx 0).1
      rw [seam x hzero]
      exact hvalues (x 1) (hx 1)
    · exact if_neg h
  let d : Euc 2 → Euc 2 →L[ℝ] E := fun x =>
    if x 0 ≤ 0 then fderivWithin ℝ F L x else fderivWithin ℝ G R x
  have dL : EqOn d (fderivWithin ℝ F L) L := by
    intro x hx
    exact if_pos (hx 0).2
  have dR : EqOn d (fderivWithin ℝ G R) R := by
    intro x hx
    change (if x 0 ≤ 0 then fderivWithin ℝ F L x else fderivWithin ℝ G R x) = _
    by_cases h : x 0 ≤ 0
    · rw [if_pos h]
      have hzero : x 0 = 0 := le_antisymm h (hx 0).1
      rw [seam x hzero]
      exact hjet (x 1) (hx 1)
    · exact if_neg h
  have hdL (x : Euc 2) (hx : x ∈ L) : HasFDerivWithinAt U (d x) L x := by
    rw [dL hx]
    exact (hF.differentiableOn (by decide) x hx).hasFDerivWithinAt.congr' eqL hx
  have hdR (x : Euc 2) (hx : x ∈ R) : HasFDerivWithinAt U (d x) R x := by
    rw [dR hx]
    exact (hG.differentiableOn (by decide) x hx).hasFDerivWithinAt.congr' eqR hx
  have hd (x : Euc 2) (hx : x ∈ T) : HasFDerivWithinAt U (d x) T x := by
    rw [hT]
    apply HasFDerivWithinAt.union
    · by_cases hl : x ∈ L
      · exact hdL x hl
      · exact HasFDerivWithinAt.of_notMem_closure (by rwa [cL.closure_eq])
    · by_cases hr : x ∈ R
      · exact hdR x hr
      · exact HasFDerivWithinAt.of_notMem_closure (by rwa [cR.closure_eq])
  have cd : ContinuousOn d T := by
    rw [hT]
    exact ((hF.continuousOn_fderivWithin uL le_rfl).congr dL).union_of_isClosed
      ((hG.continuousOn_fderivWithin uR le_rfl).congr dR) cL cR
  have hc : ContDiffOn ℝ 1 U T := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) uT).mpr
    exact ⟨fun h => (by cases h), d, contDiffOn_zero.mpr cd, hd⟩
  refine ⟨hc, ?_, ?_⟩
  · intro x hx
    exact (hd x (hLT hx)).fderivWithin (uT x (hLT hx)) |>.trans (dL hx)
  · intro x hx
    exact (hd x (hRT hx)).fderivWithin (uT x (hRT hx)) |>.trans (dR hx)

/-- Reflection across the first zero face preserves values and the actual first jet. -/
theorem finite_c1_first_coordinate_reflection {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (width lower upper : ℝ)
    (hwidth : 0 < width) (hvertical : lower < upper) (F : Euc 2 → E)
    (hF : ContDiffOn ℝ 1 F (euclideanRectangle !₂[0, lower] !₂[width, upper])) :
    ContDiffOn ℝ 1 (firstCoordinateReflection F)
      (euclideanRectangle !₂[-width / 2, lower] !₂[0, upper]) ∧
    (∀ y ∈ Icc lower upper, firstCoordinateReflection F !₂[0, y] = F !₂[0, y]) ∧
    (∀ y ∈ Icc lower upper,
      fderivWithin ℝ (firstCoordinateReflection F)
        (euclideanRectangle !₂[-width / 2, lower] !₂[0, upper]) !₂[0, y] =
          fderivWithin ℝ F (euclideanRectangle !₂[0, lower] !₂[width, upper]) !₂[0, y]) := by
  classical
  let S := euclideanRectangle !₂[0, lower] !₂[width, upper]
  let D := euclideanRectangle !₂[-width / 2, lower] !₂[0, upper]
  have unique (a b : Euc 2) (hab : ∀ j, a j < b j) :
      UniqueDiffOn ℝ (euclideanRectangle a b) := by
    have hs : euclideanRectangle a b = ((EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹'
        (Set.pi univ (fun j => Icc (a j) (b j)))) := by
      ext x
      change (∀ j, a j ≤ x j ∧ x j ≤ b j) ↔
        (∀ j ∈ (univ : Set (Fin 2)), a j ≤ x j ∧ x j ≤ b j)
      exact ⟨fun h j _ => h j, fun h j => h j (mem_univ _)⟩
    rw [hs]
    exact (EuclideanSpace.equiv (Fin 2) ℝ).uniqueDiffOn_preimage_iff.mpr
      (UniqueDiffOn.univ_pi fun j => uniqueDiffOn_Icc (hab j))
  have uD : UniqueDiffOn ℝ D := unique _ _ (by
    intro j; fin_cases j
    · change -width / 2 < 0
      linarith
    · exact hvertical)
  let M : ℝ → (Euc 2 →L[ℝ] Euc 2) := fun c =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun j =>
        if j = 0 then c • (EuclideanSpace.proj 0) else EuclideanSpace.proj 1)
  have hM (c : ℝ) (x : Euc 2) : M c x = !₂[c * x 0, x 1] := by
    ext j; fin_cases j <;> simp [M]
  have maps (c : ℝ) (hc : c = -1 ∨ c = -2) : MapsTo (M c) D S := by
    intro x hx
    have hx0 := hx 0
    have hx1 := hx 1
    change -width / 2 ≤ x 0 ∧ x 0 ≤ 0 at hx0
    change lower ≤ x 1 ∧ x 1 ≤ upper at hx1
    rw [hM]
    intro j
    fin_cases j
    · change 0 ≤ c * x 0 ∧ c * x 0 ≤ width
      rcases hc with rfl | rfl <;> constructor <;> linarith
    · exact hx1
  have hm1 := maps (-1) (Or.inl rfl)
  have hm2 := maps (-2) (Or.inr rfl)
  have hc1 := hF.comp (M (-1)).contDiff.contDiffOn hm1
  have hc2 := hF.comp (M (-2)).contDiff.contDiffOn hm2
  have hc : ContDiffOn ℝ 1 (firstCoordinateReflection F) D := by
    apply ((hc1.const_smul (3 : ℝ)).sub (hc2.const_smul (2 : ℝ))).congr
    intro x _
    dsimp only [firstCoordinateReflection]
    simp only [Function.comp_apply, hM,
      neg_one_mul, neg_mul, one_mul]
  refine ⟨hc, ?_, ?_⟩
  · intro y _
    dsimp only [firstCoordinateReflection]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      neg_zero, mul_zero]
    rw [← sub_smul]
    norm_num
  · intro y hy
    let z : Euc 2 := !₂[0, y]
    have hz : z ∈ D := by
      intro j
      fin_cases j
      · change -width / 2 ≤ 0 ∧ (0 : ℝ) ≤ 0
        constructor <;> linarith
      · exact hy
    have hz1 : M (-1) z = z := by rw [hM]; simp [z]
    have hz2 : M (-2) z = z := by rw [hM]; simp [z]
    have hs : z ∈ S := hz1 ▸ hm1 hz
    have hd := (hF.differentiableOn (by decide) z hs).hasFDerivWithinAt
    have hd1 : HasFDerivWithinAt F (fderivWithin ℝ F S z) S (M (-1) z) := hz1.symm ▸ hd
    have hd2 : HasFDerivWithinAt F (fderivWithin ℝ F S z) S (M (-2) z) := hz2.symm ▸ hd
    have hcomp1 := hd1.comp z (M (-1)).hasFDerivAt.hasFDerivWithinAt hm1
    have hcomp2 := hd2.comp z (M (-2)).hasFDerivAt.hasFDerivWithinAt hm2
    have hcombo := (hcomp1.const_smul (3 : ℝ)).sub (hcomp2.const_smul (2 : ℝ))
    have hmap : (3 : ℝ) • (fderivWithin ℝ F S z).comp (M (-1)) -
        (2 : ℝ) • (fderivWithin ℝ F S z).comp (M (-2)) = fderivWithin ℝ F S z := by
      ext w
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply]
      have hw1 : M (-1) w = !₂[-w 0, w 1] := by simpa using hM (-1) w
      have hw2 : M (-2) w = !₂[-2 * w 0, w 1] := by simpa using hM (-2) w
      rw [hw1, hw2]
      calc
        (3 : ℝ) • (fderivWithin ℝ F S z) !₂[-w 0, w 1] -
            (2 : ℝ) • (fderivWithin ℝ F S z) !₂[-2 * w 0, w 1] =
            (fderivWithin ℝ F S z) ((3 : ℝ) • !₂[-w 0, w 1] -
              (2 : ℝ) • !₂[-2 * w 0, w 1]) := by
          rw [map_sub, (fderivWithin ℝ F S z).map_smul,
            (fderivWithin ℝ F S z).map_smul]
        _ = (fderivWithin ℝ F S z) w := by
          congr 1
          ext j
          fin_cases j <;> simp <;> ring
    have hfinal : HasFDerivWithinAt (firstCoordinateReflection F)
        (fderivWithin ℝ F S z) D z := by
      rw [hmap] at hcombo
      apply hcombo.congr'
      · intro x _
        dsimp only [firstCoordinateReflection]
        simp only [Function.comp_apply, hM,
          neg_one_mul, neg_mul, one_mul, Pi.sub_apply, Pi.smul_apply]
      · exact hz
    exact hfinal.fderivWithin (uD z hz)

/-- The second coordinate uses the original literal 3,-2 reflection formula too. -/
theorem finite_c1_second_coordinate_reflection {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (width lower upper : ℝ)
    (hwidth : 0 < width) (hhorizontal : lower < upper) (F : Euc 2 → E)
    (hF : ContDiffOn ℝ 1 F (euclideanRectangle !₂[lower, 0] !₂[upper, width])) :
    ContDiffOn ℝ 1 (secondCoordinateReflection F)
      (euclideanRectangle !₂[lower, -width / 2] !₂[upper, 0]) ∧
    (∀ x ∈ Icc lower upper, secondCoordinateReflection F !₂[x, 0] = F !₂[x, 0]) ∧
    (∀ x ∈ Icc lower upper,
      fderivWithin ℝ (secondCoordinateReflection F)
        (euclideanRectangle !₂[lower, -width / 2] !₂[upper, 0]) !₂[x, 0] =
          fderivWithin ℝ F (euclideanRectangle !₂[lower, 0] !₂[upper, width]) !₂[x, 0]) := by
  classical
  let S := euclideanRectangle !₂[lower, 0] !₂[upper, width]
  let D := euclideanRectangle !₂[lower, -width / 2] !₂[upper, 0]
  have unique (a b : Euc 2) (hab : ∀ j, a j < b j) :
      UniqueDiffOn ℝ (euclideanRectangle a b) := by
    have hs : euclideanRectangle a b = ((EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹'
        (Set.pi univ (fun j => Icc (a j) (b j)))) := by
      ext x
      change (∀ j, a j ≤ x j ∧ x j ≤ b j) ↔
        (∀ j ∈ (univ : Set (Fin 2)), a j ≤ x j ∧ x j ≤ b j)
      exact ⟨fun h j _ => h j, fun h j => h j (mem_univ _)⟩
    rw [hs]
    exact (EuclideanSpace.equiv (Fin 2) ℝ).uniqueDiffOn_preimage_iff.mpr
      (UniqueDiffOn.univ_pi fun j => uniqueDiffOn_Icc (hab j))
  have uD : UniqueDiffOn ℝ D := unique _ _ (by
    intro j; fin_cases j
    · exact hhorizontal
    · change -width / 2 < 0
      linarith)
  let M : ℝ → (Euc 2 →L[ℝ] Euc 2) := fun c =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun j =>
        if j = 1 then c • (EuclideanSpace.proj 1) else EuclideanSpace.proj 0)
  have hM (c : ℝ) (x : Euc 2) : M c x = !₂[x 0, c * x 1] := by
    ext j; fin_cases j <;> simp [M]
  have maps (c : ℝ) (hc : c = -1 ∨ c = -2) : MapsTo (M c) D S := by
    intro x hx
    have hx0 := hx 0
    have hx1 := hx 1
    change lower ≤ x 0 ∧ x 0 ≤ upper at hx0
    change -width / 2 ≤ x 1 ∧ x 1 ≤ 0 at hx1
    rw [hM]
    intro j
    fin_cases j
    · exact hx0
    · change 0 ≤ c * x 1 ∧ c * x 1 ≤ width
      rcases hc with rfl | rfl <;> constructor <;> linarith
  have hm1 := maps (-1) (Or.inl rfl)
  have hm2 := maps (-2) (Or.inr rfl)
  have hc1 := hF.comp (M (-1)).contDiff.contDiffOn hm1
  have hc2 := hF.comp (M (-2)).contDiff.contDiffOn hm2
  have hc : ContDiffOn ℝ 1 (secondCoordinateReflection F) D := by
    apply ((hc1.const_smul (3 : ℝ)).sub (hc2.const_smul (2 : ℝ))).congr
    intro x _
    dsimp only [secondCoordinateReflection]
    simp only [Function.comp_apply, hM,
      neg_one_mul, neg_mul, one_mul]
  refine ⟨hc, ?_, ?_⟩
  · intro y _
    dsimp only [secondCoordinateReflection]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      neg_zero, mul_zero]
    rw [← sub_smul]
    norm_num
  · intro y hy
    let z : Euc 2 := !₂[y, 0]
    have hz : z ∈ D := by
      intro j
      fin_cases j
      · exact hy
      · change -width / 2 ≤ 0 ∧ (0 : ℝ) ≤ 0
        constructor <;> linarith
    have hz1 : M (-1) z = z := by rw [hM]; simp [z]
    have hz2 : M (-2) z = z := by rw [hM]; simp [z]
    have hs : z ∈ S := hz1 ▸ hm1 hz
    have hd := (hF.differentiableOn (by decide) z hs).hasFDerivWithinAt
    have hd1 : HasFDerivWithinAt F (fderivWithin ℝ F S z) S (M (-1) z) := hz1.symm ▸ hd
    have hd2 : HasFDerivWithinAt F (fderivWithin ℝ F S z) S (M (-2) z) := hz2.symm ▸ hd
    have hcomp1 := hd1.comp z (M (-1)).hasFDerivAt.hasFDerivWithinAt hm1
    have hcomp2 := hd2.comp z (M (-2)).hasFDerivAt.hasFDerivWithinAt hm2
    have hcombo := (hcomp1.const_smul (3 : ℝ)).sub (hcomp2.const_smul (2 : ℝ))
    have hmap : (3 : ℝ) • (fderivWithin ℝ F S z).comp (M (-1)) -
        (2 : ℝ) • (fderivWithin ℝ F S z).comp (M (-2)) = fderivWithin ℝ F S z := by
      ext w
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply]
      have hw1 : M (-1) w = !₂[w 0, -w 1] := by simpa using hM (-1) w
      have hw2 : M (-2) w = !₂[w 0, -2 * w 1] := by simpa using hM (-2) w
      rw [hw1, hw2]
      calc
        (3 : ℝ) • (fderivWithin ℝ F S z) !₂[w 0, -w 1] -
            (2 : ℝ) • (fderivWithin ℝ F S z) !₂[w 0, -2 * w 1] =
            (fderivWithin ℝ F S z) ((3 : ℝ) • !₂[w 0, -w 1] -
              (2 : ℝ) • !₂[w 0, -2 * w 1]) := by
          rw [map_sub, (fderivWithin ℝ F S z).map_smul,
            (fderivWithin ℝ F S z).map_smul]
        _ = (fderivWithin ℝ F S z) w := by
          congr 1
          ext j
          fin_cases j <;> simp <;> ring
    have hfinal : HasFDerivWithinAt (secondCoordinateReflection F)
        (fderivWithin ℝ F S z) D z := by
      rw [hmap] at hcombo
      apply hcombo.congr'
      · intro x _
        dsimp only [secondCoordinateReflection]
        simp only [Function.comp_apply, hM,
          neg_one_mul, neg_mul, one_mul, Pi.sub_apply, Pi.smul_apply]
      · exact hz
    exact hfinal.fderivWithin (uD z hz)



end
end SeifertSurfaces.LongitudeProducers.DiagramExtensionRoundingHelpers

-- Restore the actual exporting module before elaborating the original consumer.
run_cmd Lean.modifyEnv fun env => env.setMainModule `DiagramExtensionRemaining

namespace SeifertSurfaces.LongitudeProducers.DiagramRemainingHelpers
open Foundations MetricFoundations DiagramExtensionRoundingHelpers
noncomputable section

theorem finite_c1_closed_rectangle_extension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (a b : Euc 2)
    (hab : ∀ j, a j < b j) (F : Euc 2 → E)
    (hF : ContDiffOn ℝ 1 F (euclideanRectangle a b)) :
    Nonempty (FiniteC1RectangleExtension a b F) := by
  have hfirst  
    (w lower upper : ℝ) (hw : 0<w) (hvertical : lower<upper) (F : Euc 2 → E)
    (hF : ContDiffOn ℝ 1 F (euclideanRectangle !₂[0,lower] !₂[w,upper])) :
    ∃ G : Euc 2 → E,
      ContDiffOn ℝ 1 G (euclideanRectangle !₂[-w/2,lower] !₂[7*w/4,upper]) ∧
      EqOn G F (euclideanRectangle !₂[0,lower] !₂[w,upper])  := by
  
    obtain ⟨hreflect,hvalues,hjet⟩ := finite_c1_first_coordinate_reflection w lower upper hw hvertical F hF
    let H := closedHalfStripUnion (firstCoordinateReflection F) F
    have hH : ContDiffOn ℝ 1 H (euclideanRectangle !₂[-w/2,lower] !₂[w,upper]) := by
      have hc := finite_c1_closed_half_strip_gluing (w/2) w lower upper (by positivity) hw hvertical
        (firstCoordinateReflection F) F (by simpa only [neg_div] using hreflect) hF hvalues
        (by simpa only [neg_div] using hjet)
      simpa only [neg_div] using hc.1
    have hHF : EqOn H F (euclideanRectangle !₂[0,lower] !₂[w,upper]) := by
      intro x hx
      dsimp [H,closedHalfStripUnion]
      split_ifs with h
      · have hz : x 0=0 := le_antisymm h (hx 0).1
        have heq : x=!₂[0,x 1] := by ext j;fin_cases j;exact hz;rfl
        rw [heq]
        exact hvalues (x 1) (hx 1)
      · rfl
    let A : Euc 2 → Euc 2 := fun x=>!₂[w-x 0,x 1]
    have hA : ContDiff ℝ ∞ A := by
      apply (contDiff_piLp (p := 2)).mpr
      intro j
      fin_cases j <;> dsimp [A] <;> fun_prop
    let R := H ∘ A
    have hR : ContDiffOn ℝ 1 R (euclideanRectangle !₂[0,lower] !₂[3*w/2,upper]) := by
      apply hH.comp (hA.of_le (by simp)).contDiffOn
      intro x hx j
      have hx0 := hx 0
      have hx1 := hx 1
      fin_cases j
      · change -w/2≤w-x 0 ∧ w-x 0≤w
        change 0≤x 0 ∧ x 0≤3*w/2 at hx0
        constructor <;> linarith
      · exact hx1
    obtain ⟨hr2,hv2,hj2⟩ := finite_c1_first_coordinate_reflection (3*w/2) lower upper
      (by positivity) hvertical R hR
    rw [show -(3*w/2)/2 = -(3*w/4) by ring] at hr2 hj2
    let J := closedHalfStripUnion (firstCoordinateReflection R) R
    have hJ : ContDiffOn ℝ 1 J (euclideanRectangle !₂[-3*w/4,lower] !₂[3*w/2,upper]) := by
      simpa only [neg_mul,neg_div] using (finite_c1_closed_half_strip_gluing (3*w/4) (3*w/2) lower upper
        (by positivity) (by positivity) hvertical (firstCoordinateReflection R) R hr2 hR hv2 hj2).1
    have hJR : EqOn J R (euclideanRectangle !₂[0,lower] !₂[3*w/2,upper]) := by
      intro x hx
      dsimp [J,closedHalfStripUnion]
      split_ifs with h
      · have hz : x 0=0 := le_antisymm h (hx 0).1
        have heq : x=!₂[0,x 1] := by ext j;fin_cases j;exact hz;rfl
        rw [heq]
        exact hv2 (x 1) (hx 1)
      · rfl
    refine ⟨J ∘ A, ?_, ?_⟩
    · apply hJ.comp (hA.of_le (by simp)).contDiffOn
      intro x hx j
      have hx0 := hx 0
      have hx1 := hx 1
      fin_cases j
      · change -3*w/4≤w-x 0 ∧ w-x 0≤3*w/2
        change -w/2≤x 0 ∧ x 0≤7*w/4 at hx0
        constructor <;> linarith
      · exact hx1
    · intro x hx
      have hAx : A x ∈ euclideanRectangle !₂[0,lower] !₂[3*w/2,upper] := by
        intro j
        fin_cases j
        · change 0≤w-x 0 ∧ w-x 0≤3*w/2
          have hx0 := hx 0
          change 0≤x 0 ∧ x 0≤w at hx0
          constructor <;> linarith
        · exact hx 1
      change J (A x)=F x
      rw [hJR hAx]
      have hAA : A (A x)=x := by ext j;fin_cases j <;> dsimp [A] <;> ring
      change H (A (A x))=F x
      rw [hAA]
      exact hHF hx
  let w:=b 0-a 0
  let v:=b 1-a 1
  have hw : 0<w := sub_pos.mpr (hab 0)
  have hv : 0<v := sub_pos.mpr (hab 1)
  let A : Euc 2 → Euc 2 := fun x=>a+x
  have hA : ContDiff ℝ ∞ A := contDiff_const.add contDiff_id
  let f:=F ∘ A
  have hf : ContDiffOn ℝ 1 f (euclideanRectangle !₂[0,0] !₂[w,v]) := by
    apply hF.comp (hA.of_le (by simp)).contDiffOn
    intro x hx j
    fin_cases j
    · have hx0 := hx 0
      change 0≤x 0 ∧ x 0≤w at hx0
      change a 0≤a 0+x 0 ∧ a 0+x 0≤b 0
      dsimp [w] at hx0
      constructor <;> linarith
    · have hx1 := hx 1
      change 0≤x 1 ∧ x 1≤v at hx1
      change a 1≤a 1+x 1 ∧ a 1+x 1≤b 1
      dsimp [v] at hx1
      constructor <;> linarith
  obtain ⟨G,hG,hGf⟩ := hfirst w 0 v hw hv f hf
  let B : Euc 2 → Euc 2 := fun x=>!₂[x 1,x 0]
  have hB : ContDiff ℝ ∞ B := by
    apply (contDiff_piLp (p:=2)).mpr
    intro j
    fin_cases j <;> dsimp [B] <;> fun_prop
  have hBB (x:Euc 2) : B (B x)=x := by ext j;fin_cases j <;> rfl
  let g:=G ∘ B
  have hg : ContDiffOn ℝ 1 g (euclideanRectangle !₂[0,-w/2] !₂[v,7*w/4]) := by
    apply hG.comp (hB.of_le (by simp)).contDiffOn
    intro x hx j
    fin_cases j
    · exact hx 1
    · exact hx 0
  obtain ⟨H,hH,hHg⟩ := hfirst v (-w/2) (7*w/4) hv (by linarith) g hg
  let K:=H ∘ B
  have hK : ContDiffOn ℝ 1 K (euclideanRectangle !₂[-w/2,-v/2] !₂[7*w/4,7*v/4]) := by
    apply hH.comp (hB.of_le (by simp)).contDiffOn
    intro x hx j
    fin_cases j
    · exact hx 1
    · exact hx 0
  have hKf : EqOn K f (euclideanRectangle !₂[0,0] !₂[w,v]) := by
    intro x hx
    have hBx : B x ∈ euclideanRectangle !₂[0,-w/2] !₂[v,7*w/4] := by
      intro j
      fin_cases j
      · exact hx 1
      · have hx0:=hx 0
        change 0≤x 0 ∧ x 0≤w at hx0
        change -w/2≤x 0 ∧ x 0≤7*w/4
        constructor <;> linarith
    change H (B x)=f x
    rw [hHg hBx]
    change G (B (B x))=f x
    rw [hBB]
    exact hGf hx
  let C : Euc 2 → Euc 2 := fun x=>x-a
  have hC : ContDiff ℝ ∞ C := contDiff_id.sub contDiff_const
  let l:Euc 2:=a+!₂[-w/2,-v/2]
  let u:Euc 2:=a+!₂[7*w/4,7*v/4]
  let M : Euc 2 → E:=K ∘ C
  have hM : ContDiffOn ℝ 1 M (euclideanRectangle l u) := by
    apply hK.comp (hC.of_le (by simp)).contDiffOn
    intro x hx j
    fin_cases j
    · have h0:=hx 0
      change a 0 + (-w/2)≤x 0 ∧ x 0≤a 0+7*w/4 at h0
      change -w/2≤x 0-a 0 ∧ x 0-a 0≤7*w/4
      constructor <;> linarith
    · have h1:=hx 1
      change a 1 + (-v/2)≤x 1 ∧ x 1≤a 1+7*v/4 at h1
      change -v/2≤x 1-a 1 ∧ x 1-a 1≤7*v/4
      constructor <;> linarith
  have hMF : EqOn M F (euclideanRectangle a b) := by
    intro x hx
    have hCx : C x ∈ euclideanRectangle !₂[0,0] !₂[w,v] := by
      intro j
      fin_cases j
      · have h0:=hx 0
        change 0≤x 0-a 0 ∧ x 0-a 0≤w
        dsimp [w]
        constructor <;> linarith [h0.1,h0.2]
      · have h1:=hx 1
        change 0≤x 1-a 1 ∧ x 1-a 1≤v
        dsimp [v]
        constructor <;> linarith [h1.1,h1.2]
    change K (C x)=F x
    rw [hKf hCx]
    change F (a+(x-a))=F x
    congr 1
    module
  let N:Set (Euc 2):=⋂ j, {x | l j<x j ∧ x j<u j}
  have hNopen : IsOpen N := isOpen_iInter_of_finite fun j=>
    (isOpen_lt continuous_const (EuclideanSpace.proj j).continuous).inter
      (isOpen_lt (EuclideanSpace.proj j).continuous continuous_const)
  have hrect : euclideanRectangle a b ⊆ N := by
    intro x hx
    apply Set.mem_iInter.mpr
    intro j
    fin_cases j
    · change a 0+(-w/2)<x 0 ∧ x 0<a 0+7*w/4
      have h0:=hx 0
      dsimp [w] at *
      constructor <;> linarith [hab 0,h0.1,h0.2]
    · change a 1+(-v/2)<x 1 ∧ x 1<a 1+7*v/4
      have h1:=hx 1
      dsimp [v] at *
      constructor <;> linarith [hab 1,h1.1,h1.2]
  have hMN : ContDiffOn ℝ 1 M N := hM.mono (by
    intro x hx j
    have h:=Set.mem_iInter.mp hx j
    exact ⟨h.1.le,h.2.le⟩)
  refine ⟨⟨N,hNopen,hrect,M,hMN,hMF,?_⟩⟩
  intro x hx
  have hMd : DifferentiableAt ℝ M x :=
    (hMN x (hrect hx)).contDiffAt (hNopen.mem_nhds (hrect hx)) |>.differentiableAt (by simp)
  rw [← hMd.fderivWithin (nondegenerate_rectangle_unique_diff a b hab x hx)]
  exact fderivWithin_congr hMF (hMF hx)

/-- X2: subdivisions are in each original square, with actual affine Time inclusion. -/
structure SubordinateAngleRectangles {f g : Circle → Euc 3} (H : PiecewiseCurveIsotopy f g) where
  count : ℕ
  originalIndex : Fin count → Fin H.count
  lower : Fin count → Euc 2
  upper : Fin count → Euc 2
  nondegenerate : ∀ i j, lower i j < upper i j
  in_unit_square : ∀ i j, 0 ≤ lower i j ∧ upper i j ≤ 1
  parameter : ∀ i, C(↥(euclideanRectangle (lower i) (upper i)), Time × Time)
  parameter_values : ∀ i (x : ↥(euclideanRectangle (lower i) (upper i))),
    ((parameter i x).1 : ℝ) = (x : Euc 2) 0 ∧ ((parameter i x).2 : ℝ) = (x : Euc 2) 1
  angleLift : Fin count → Euc 2 → ℝ
  angle_c1 : ∀ i, ContDiffOn ℝ 1 (angleLift i) (euclideanRectangle (lower i) (upper i))
  angle_values : ∀ i (x : ↥(euclideanRectangle (lower i) (upper i))), Circle.exp (angleLift i x) =
    (H.coordinate (originalIndex i) (parameter i x)).2
  angleCenter : Fin count → ℝ
  angleWidth : Fin count → ℝ
  angleWidth_bounds : ∀ i, 0 < angleWidth i ∧ angleWidth i < Real.pi
  one_arc : ∀ i (x : ↥(euclideanRectangle (lower i) (upper i))),
    angleLift i x ∈ Ioo (angleCenter i - angleWidth i) (angleCenter i + angleWidth i)
  original_square_covers : ∀ j : Fin H.count,
    (⋃ i, if originalIndex i = j then Set.range (parameter i) else ∅) = univ

theorem subordinate_angle_rectangles_exist {f g : Circle → Euc 3}
    (H : PiecewiseCurveIsotopy f g) : Nonempty (SubordinateAngleRectangles H) := by
  have angleLaws : ∃ angle : ℝ → Circle → ℝ, ∀ c : ℝ,
    IsOpen (Circle.exp '' Ioo (c - Real.pi / 2) (c + Real.pi / 2)) ∧
    ContMDiffOn (𝓡 1) 𝓘(ℝ,ℝ) 1 (angle c)
      (Circle.exp '' Ioo (c - Real.pi / 2) (c + Real.pi / 2)) ∧
    (∀ z, Circle.exp (angle c z) = z) ∧
    (∀ z ∈ Circle.exp '' Ioo (c - Real.pi / 2) (c + Real.pi / 2),
      angle c z ∈ Ioo (c - Real.pi / 2) (c + Real.pi / 2)) := by
    let rot : ℝ → Circle → Circle := fun c z => Circle.exp (-c) * z
    let angle : ℝ → Circle → ℝ := fun c z => c + (Complex.log (rot c z : ℂ)).im
    let arc : ℝ → Set Circle := fun c => Circle.exp '' Ioo (c - Real.pi / 2) (c + Real.pi / 2)
    have hrot (c t : ℝ) : rot c (Circle.exp t) = Circle.exp (t - c) := by
      simp only [rot,Circle.exp_neg,Circle.exp_sub,div_eq_mul_inv,mul_comm]
    have hexp (c : ℝ) (z : Circle) : Circle.exp (angle c z) = z := by
      dsimp only [angle]
      rw [Complex.log_im,Circle.exp_add,Circle.exp_arg]
      dsimp only [rot]
      rw [Circle.exp_neg,
        ←mul_assoc,mul_inv_cancel,one_mul]
    have hθ (c t : ℝ) (ht : t ∈ Ioo (c - Real.pi / 2) (c + Real.pi / 2)) :
        angle c (Circle.exp t) = t := by
      dsimp only [angle]
      rw [Complex.log_im,hrot,Circle.arg_exp (by linarith [ht.1,Real.pi_pos])
        (by linarith [ht.2,Real.pi_pos])]
      ring
    have slit (c : ℝ) (z : Circle) (hz : z ∈ arc c) : (rot c z : ℂ) ∈ Complex.slitPlane := by
      obtain ⟨t,ht,rfl⟩ := hz
      rw [hrot,Complex.mem_slitPlane_iff_arg]
      refine ⟨?_,Circle.coe_ne_zero _⟩
      rw [Circle.arg_exp (by linarith [ht.1,Real.pi_pos]) (by linarith [ht.2,Real.pi_pos])]
      linarith [ht.2,Real.pi_pos]
    have hrange (c : ℝ) (z : Circle) (hz : z ∈ arc c) :
        angle c z ∈ Ioo (c - Real.pi / 2) (c + Real.pi / 2) := by
      obtain ⟨t,ht,rfl⟩ := hz
      rwa [hθ c t ht]
    refine ⟨angle,?_⟩
    intro c
    have hr : Continuous (fun z : Circle => (rot c z : ℂ)) :=
      continuous_subtype_val.comp (continuous_const.mul continuous_id)
    have hEq : arc c = {z | (rot c z : ℂ) ∈ Complex.slitPlane} ∩
        angle c ⁻¹' Ioo (c - Real.pi / 2) (c + Real.pi / 2) := by
      ext z
      exact ⟨fun hz => ⟨slit c z hz,hrange c z hz⟩,
        fun hz => ⟨angle c z,hz.2,hexp c z⟩⟩
    have ho : IsOpen (arc c) := by
      rw [hEq]
      apply ContinuousOn.isOpen_inter_preimage _ (Complex.isOpen_slitPlane.preimage hr) isOpen_Ioo
      intro z hz
      have hl : ContinuousAt Complex.log (rot c z : ℂ) :=
        (Complex.contDiffAt_log hz (n := ∞)).continuousAt
      exact (continuousAt_const.add
        (Complex.imCLM.continuous.continuousAt.comp (hl.comp (f := fun z : Circle => (rot c z : ℂ)) hr.continuousAt))).continuousWithinAt
    have hc : ContMDiffOn (𝓡 1) 𝓘(ℝ,ℝ) 1 (angle c) (arc c) := by
      haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
      have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ,ℂ) 1 (fun z : Circle => (z : ℂ)) := contMDiff_coe_sphere
      have hm : ContMDiff (𝓡 1) (𝓡 1) 1 (rot c) := contMDiff_const.mul contMDiff_id
      have hrotc := hcoe.comp hm
      intro z hz
      have hl := (Complex.contDiffAt_log (slit c z hz) (n := 1)).restrict_scalars ℝ
      have hi := Complex.imCLM.contDiff.contMDiff.contMDiffAt.comp z
        (hl.contMDiffAt.comp z hrotc.contMDiffAt)
      exact (contMDiffAt_const.add hi).contMDiffWithinAt
    exact ⟨ho,hc,hexp c,hrange c⟩
  obtain ⟨angle,laws⟩ := angleLaws
  classical
  let arc : ℝ → Set Circle := fun c => Circle.exp '' Ioo (c - Real.pi / 2) (c + Real.pi / 2)
  let center : (Fin H.count × (Time × Time)) → ℝ := fun q => (H.coordinate q.1 q.2).2.val.arg
  have hradius (q : Fin H.count × (Time × Time)) :
      ∃ r : ℝ, 0 < r ∧ ∀ p ∈ Metric.ball q.2 r,
        (H.coordinate q.1 p).2 ∈ arc (center q) := by
    have hz : (H.coordinate q.1 q.2).2 ∈ arc (center q) := by
      refine ⟨center q,?_,Circle.exp_arg _⟩
      constructor <;> linarith [Real.pi_pos]
    have hc : Continuous (fun p : Time × Time => (H.coordinate q.1 p).2) :=
      (H.coordinate q.1).continuous.snd
    have hpre := hc.continuousAt.preimage_mem_nhds ((laws (center q)).1.mem_nhds hz)
    obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hpre
    exact ⟨r,hr,hsub⟩
  choose radius radius_pos radius_maps using hradius
  let δ : (Fin H.count × (Time × Time)) → ℝ := fun q => radius q / 2
  have hδ (q) : 0 < δ q := half_pos (radius_pos q)
  let U : (Fin H.count × (Time × Time)) → Set (Fin H.count × (Time × Time)) :=
    fun q => {q.1} ×ˢ Metric.ball q.2 (δ q)
  have hU (q) : IsOpen (U q) := (isOpen_discrete _).prod Metric.isOpen_ball
  have hcover : (univ : Set (Fin H.count × (Time × Time))) ⊆ ⋃ q, U q := by
    intro q _
    exact Set.mem_iUnion.mpr ⟨q,by exact ⟨rfl,Metric.mem_ball_self (hδ q)⟩⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let e := s.equivFin
  let data : Fin s.card → Fin H.count × (Time × Time) := fun i => (e.symm i).val
  let a : Fin s.card → Euc 2 := fun i => !₂[max 0 ((data i).2.1 - δ (data i)),
    max 0 ((data i).2.2 - δ (data i))]
  let b : Fin s.card → Euc 2 := fun i => !₂[min 1 ((data i).2.1 + δ (data i)),
    min 1 ((data i).2.2 + δ (data i))]
  have hbounds (u : Time) (d : ℝ) (hd : 0 < d) : max 0 (u - d) < min 1 (u + d) := by
    apply max_lt_iff.mpr
    constructor <;> apply lt_min_iff.mpr <;> constructor <;> linarith [u.property.1,u.property.2]
  have hab (i : Fin s.card) (j : Fin 2) : a i j < b i j := by
    fin_cases j
    · exact hbounds (data i).2.1 _ (hδ _)
    · exact hbounds (data i).2.2 _ (hδ _)
  have hunit (i : Fin s.card) (j : Fin 2) : 0 ≤ a i j ∧ b i j ≤ 1 := by
    fin_cases j <;> exact ⟨le_max_left _ _,min_le_left _ _⟩
  let P : Euc 2 → Time × Time := fun x =>
    (projIcc 0 1 zero_le_one (x 0),projIcc 0 1 zero_le_one (x 1))
  have hPc : Continuous P := (continuous_projIcc.comp (by fun_prop)).prodMk
    (continuous_projIcc.comp (by fun_prop))
  let parameter : ∀ i, C(↥(euclideanRectangle (a i) (b i)),Time × Time) :=
    fun i => ⟨fun x => P x,hPc.comp continuous_subtype_val⟩
  have hpx (i : Fin s.card) (x : Euc 2) (hx : x ∈ euclideanRectangle (a i) (b i)) (j : Fin 2) :
      x j ∈ Icc (0 : ℝ) 1 :=
    ⟨(hunit i j).1.trans (hx j).1,(hx j).2.trans (hunit i j).2⟩
  have hpv (i : Fin s.card) (x : ↥(euclideanRectangle (a i) (b i))) :
      ((parameter i x).1 : ℝ) = (x : Euc 2) 0 ∧ ((parameter i x).2 : ℝ) = (x : Euc 2) 1 := by
    change (projIcc 0 1 zero_le_one ((x : Euc 2) 0) : ℝ) = (x : Euc 2) 0 ∧
      (projIcc 0 1 zero_le_one ((x : Euc 2) 1) : ℝ) = (x : Euc 2) 1
    rw [projIcc_of_mem zero_le_one (hpx i x x.property 0),
      projIcc_of_mem zero_le_one (hpx i x x.property 1)]
    exact ⟨rfl,rfl⟩
  have hPdiff (i : Fin s.card) : ContMDiffOn 𝓘(ℝ,Euc 2) ((𝓡∂ 1).prod (𝓡∂ 1)) 1 P
      (euclideanRectangle (a i) (b i)) := by
    have hc (j : Fin 2) : ContMDiffOn 𝓘(ℝ,Euc 2) (𝓡∂ 1) 1
        (fun x : Euc 2 => projIcc 0 1 zero_le_one (x j)) (euclideanRectangle (a i) (b i)) := by
      have hproj : ContDiff ℝ 1 (fun x : Euc 2 => x j) := by fun_prop
      exact contMDiffOn_projIcc.comp hproj.contMDiff.contMDiffOn (fun x hx => hpx i x hx j)
    exact (hc 0).prodMk (hc 1)
  have hnear (i : Fin s.card) (x : Euc 2) (hx : x ∈ euclideanRectangle (a i) (b i)) :
      P x ∈ Metric.ball (data i).2 (radius (data i)) := by
    have hcoord (j : Fin 2) : |x j - (if j = 0 then ((data i).2.1 : ℝ) else (data i).2.2)| ≤ δ (data i) := by
      fin_cases j
      · change |x 0 - ((data i).2.1 : ℝ)| ≤ δ (data i)
        have h := hx 0
        change max 0 ((data i).2.1 - δ (data i)) ≤ x 0 ∧ x 0 ≤ min 1 ((data i).2.1 + δ (data i)) at h
        apply abs_le.mpr
        constructor <;> linarith [le_max_right (0 : ℝ) ((data i).2.1 - δ (data i)),
          min_le_right (1 : ℝ) ((data i).2.1 + δ (data i))]
      · change |x 1 - ((data i).2.2 : ℝ)| ≤ δ (data i)
        have h := hx 1
        change max 0 ((data i).2.2 - δ (data i)) ≤ x 1 ∧ x 1 ≤ min 1 ((data i).2.2 + δ (data i)) at h
        apply abs_le.mpr
        constructor <;> linarith [le_max_right (0 : ℝ) ((data i).2.2 - δ (data i)),
          min_le_right (1 : ℝ) ((data i).2.2 + δ (data i))]
    change dist (P x) (data i).2 < radius (data i)
    rw [Prod.dist_eq]
    apply max_lt_iff.mpr
    have hd : δ (data i) < radius (data i) := by dsimp [δ]; linarith [radius_pos (data i)]
    constructor
    · have h := hcoord 0
      simpa [P,Subtype.dist_eq,Real.dist_eq,projIcc_of_mem zero_le_one (hpx i x hx 0)] using h.trans_lt hd
    · have h := hcoord 1
      simpa [P,Subtype.dist_eq,Real.dist_eq,projIcc_of_mem zero_le_one (hpx i x hx 1)] using h.trans_lt hd
  let lift : Fin s.card → Euc 2 → ℝ := fun i x => angle (center (data i)) (H.coordinate (data i).1 (P x)).2
  have hangle (i : Fin s.card) : ContDiffOn ℝ 1 (lift i) (euclideanRectangle (a i) (b i)) := by
    have hcoord := (H.source_regular (data i).1).comp_contMDiffOn (hPdiff i)
    have hsnd := contMDiff_snd.comp_contMDiffOn hcoord
    exact ((laws (center (data i))).2.1.comp hsnd (fun x hx => radius_maps _ _ (hnear i x hx))).contDiffOn
  have hmap (i : Fin s.card) (x : ↥(euclideanRectangle (a i) (b i))) :
      (H.coordinate (data i).1 (parameter i x)).2 ∈ arc (center (data i)) :=
    radius_maps _ _ (hnear i x x.property)
  refine ⟨{
    count := s.card
    originalIndex := fun i => (data i).1
    lower := a
    upper := b
    nondegenerate := hab
    in_unit_square := hunit
    parameter := parameter
    parameter_values := hpv
    angleLift := lift
    angle_c1 := hangle
    angle_values := fun i x => (laws (center (data i))).2.2.1 _
    angleCenter := fun i => center (data i)
    angleWidth := fun _ => Real.pi / 2
    angleWidth_bounds := fun _ => ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
    one_arc := fun i x => (laws (center (data i))).2.2.2 _ (hmap i x)
    original_square_covers := ?_ }⟩
  intro j
  apply eq_univ_iff_forall.mpr
  intro p
  have hp := hs (show (j,p) ∈ (univ : Set (Fin H.count × (Time × Time))) from mem_univ _)
  obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hp
  obtain ⟨hqS,hpU⟩ := Set.mem_iUnion.mp hq
  have hj : j = q.1 := hpU.1
  let i : Fin s.card := e ⟨q,hqS⟩
  have hi : data i = q := congrArg Subtype.val (e.symm_apply_apply ⟨q,hqS⟩)
  let x : Euc 2 := !₂[(p.1 : ℝ),(p.2 : ℝ)]
  have hx : x ∈ euclideanRectangle (a i) (b i) := by
    have hd := hpU.2
    change dist p q.2 < δ q at hd
    rw [Prod.dist_eq,max_lt_iff] at hd
    have hd0 : |(p.1 : ℝ) - q.2.1| < δ q := by simpa [Subtype.dist_eq,Real.dist_eq] using hd.1
    have hd1 : |(p.2 : ℝ) - q.2.2| < δ q := by simpa [Subtype.dist_eq,Real.dist_eq] using hd.2
    intro k
    fin_cases k
    · change max 0 ((data i).2.1 - δ (data i)) ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ min 1 ((data i).2.1 + δ (data i))
      rw [hi,max_le_iff,le_min_iff]
      exact ⟨⟨p.1.property.1,by linarith [(abs_lt.mp hd0).1]⟩,
        ⟨p.1.property.2,by linarith [(abs_lt.mp hd0).2]⟩⟩
    · change max 0 ((data i).2.2 - δ (data i)) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ min 1 ((data i).2.2 + δ (data i))
      rw [hi,max_le_iff,le_min_iff]
      exact ⟨⟨p.2.property.1,by linarith [(abs_lt.mp hd1).1]⟩,
        ⟨p.2.property.2,by linarith [(abs_lt.mp hd1).2]⟩⟩
  apply Set.mem_iUnion.mpr
  refine ⟨i,?_⟩
  rw [if_pos (show (data i).1 = j by rw [hi,hj])]
  refine ⟨⟨x,hx⟩,?_⟩
  apply Prod.ext <;> apply Subtype.ext
  · exact (hpv i ⟨x,hx⟩).1
  · exact (hpv i ⟨x,hx⟩).2

def subordinateSourceCoordinates {f g : Circle → Euc 3} {H : PiecewiseCurveIsotopy f g}
    (A : SubordinateAngleRectangles H) (i : Fin A.count)
    (x : ↥(euclideanRectangle (A.lower i) (A.upper i))) : Euc 2 :=
  !₂[(H.coordinate (A.originalIndex i) (A.parameter i x)).1, A.angleLift i x]

def subordinateTargetCoordinates {f g : Circle → Euc 3} {H : PiecewiseCurveIsotopy f g}
    (A : SubordinateAngleRectangles H) (i : Fin A.count)
    (x : ↥(euclideanRectangle (A.lower i) (A.upper i))) : Euc 4 :=
  let p := H.coordinate (A.originalIndex i) (A.parameter i x)
  !₂[(p.1 : ℝ), H.stage p.1 p.2 0, H.stage p.1 p.2 1, H.stage p.1 p.2 2]

/-- X3: both exact maps extend on the same neighborhood, with positive closed-face bounds. -/
structure ExactRectangleExtension {f g : Circle → Euc 3} {H : PiecewiseCurveIsotopy f g}
    (A : SubordinateAngleRectangles H) (i : Fin A.count) where
  neighborhood : Set (Euc 2)
  neighborhood_open : IsOpen neighborhood
  rectangle_inside : euclideanRectangle (A.lower i) (A.upper i) ⊆ neighborhood
  source : Euc 2 → Euc 2
  target : Euc 2 → Euc 4
  source_c1 : ContDiffOn ℝ 1 source neighborhood
  target_c1 : ContDiffOn ℝ 1 target neighborhood
  source_values : ∀ (x : ↥(euclideanRectangle (A.lower i) (A.upper i))),
    source x = subordinateSourceCoordinates A i x
  target_values : ∀ (x : ↥(euclideanRectangle (A.lower i) (A.upper i))),
    target x = subordinateTargetCoordinates A i x
  lowerBound : ℝ
  lowerBound_pos : 0 < lowerBound
  source_minor : ∀ x ∈ euclideanRectangle (A.lower i) (A.upper i),
    lowerBound ≤ |orientedPlaneDet (fderiv ℝ source x (EuclideanSpace.single 0 1))
      (fderiv ℝ source x (EuclideanSpace.single 1 1))|
  target_lower : ∀ x ∈ euclideanRectangle (A.lower i) (A.upper i), ∀ v : Euc 2,
    lowerBound * ‖v‖ ≤ ‖fderiv ℝ target x v‖

theorem exact_closed_rectangle_extensions {f g : Circle → Euc 3}
    {H : PiecewiseCurveIsotopy f g} (A : SubordinateAngleRectangles H) (i : Fin A.count) :
    Nonempty (ExactRectangleExtension A i) := by
  have clamp :
    ∃ p : Euc 2 → Time × Time,
      ContMDiffOn 𝓘(ℝ, Euc 2) ((𝓡∂ 1).prod (𝓡∂ 1)) 1 p
        (euclideanRectangle (A.lower i) (A.upper i)) ∧
      (∀ x : ↥(euclideanRectangle (A.lower i) (A.upper i)), p x = A.parameter i x) ∧
      (∀ x ∈ euclideanRectangle (A.lower i) (A.upper i),
        Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) ((𝓡∂ 1).prod (𝓡∂ 1)) p
          (euclideanRectangle (A.lower i) (A.upper i)) x)) := by
    let K := euclideanRectangle (A.lower i) (A.upper i)
    let p : Euc 2 → Time × Time := fun x =>
      (projIcc 0 1 zero_le_one (x 0), projIcc 0 1 zero_le_one (x 1))
    have hK (x : Euc 2) (hx : x ∈ K) (j : Fin 2) : x j ∈ Icc (0 : ℝ) 1 :=
      ⟨(A.in_unit_square i j).1.trans (hx j).1, (hx j).2.trans (A.in_unit_square i j).2⟩
    have hc (j : Fin 2) : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 1) 1
        (fun x : Euc 2 => projIcc 0 1 zero_le_one (x j)) K := by
      have hproj : ContDiff ℝ 1 (fun x : Euc 2 => x j) := by fun_prop
      exact contMDiffOn_projIcc.comp hproj.contMDiff.contMDiffOn
        (fun x hx => hK x hx j)
    have hp : ContMDiffOn 𝓘(ℝ, Euc 2) ((𝓡∂ 1).prod (𝓡∂ 1)) 1 p K :=
      (hc 0).prodMk (hc 1)
    have hvalues (x : ↥K) : p x = A.parameter i x := by
      apply Prod.ext <;> apply Subtype.ext
      · simpa [p, projIcc_of_mem zero_le_one (hK x x.property 0)] using
          (A.parameter_values i x).1.symm
      · simpa [p, projIcc_of_mem zero_le_one (hK x x.property 1)] using
          (A.parameter_values i x).2.symm
    let C : Time × Time → Euc 2 := fun q => !₂[(q.1 : ℝ), (q.2 : ℝ)]
    have hC : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, Euc 2) 1 C := by
      let L : (ℝ × ℝ) →L[ℝ] Euc 2 :=
        (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.pi fun j => if j = 0 then ContinuousLinearMap.fst ℝ ℝ ℝ
            else ContinuousLinearMap.snd ℝ ℝ ℝ)
      have hL : ContDiff ℝ 1 L := L.contDiff
      have hbase : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ × ℝ) 1
          (fun q : Time × Time => ((q.1 : ℝ), (q.2 : ℝ))) :=
        (contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk_space
          (contMDiff_subtypeVal_Icc.comp contMDiff_snd)
      convert hL.comp_contMDiff hbase using 1
      funext q
      ext j
      fin_cases j <;> simp [L, C]
    have hEq : EqOn (C ∘ p) id K := by
      intro x hx
      ext j
      fin_cases j <;> simp [C, p, projIcc_of_mem zero_le_one (hK x hx 0),
        projIcc_of_mem zero_le_one (hK x hx 1)]
    refine ⟨p, hp, hvalues, ?_⟩
    intro x hx
    have hu := nondegenerate_rectangle_unique_diff _ _ (A.nondegenerate i) x hx
    have hderiv : mfderivWithin 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 2) (C ∘ p) K x =
        (ContinuousLinearMap.id ℝ (Euc 2)) := by
      rw [mfderivWithin_eq_fderivWithin, fderivWithin_congr hEq (hEq hx), fderivWithin_id hu]
      rfl
    rw [mfderiv_comp_mfderivWithin x (hC.mdifferentiableAt one_ne_zero)
      (hp.mdifferentiableOn one_ne_zero x hx) hu.uniqueMDiffWithinAt] at hderiv
    have hinj : Function.Injective ((mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, Euc 2) C (p x)).comp
        (mfderivWithin 𝓘(ℝ, Euc 2) ((𝓡∂ 1).prod (𝓡∂ 1)) p K x)) := by
      rw [hderiv]
      exact Function.injective_id
    exact Function.Injective.of_comp hinj
  obtain ⟨p,hp,hpv,hpi⟩ := clamp
  have coordinates :
    ∃ S : Euc 2 → Euc 2, ∃ T : Euc 2 → Euc 4,
      ContDiffOn ℝ 1 S (euclideanRectangle (A.lower i) (A.upper i)) ∧
      ContDiffOn ℝ 1 T (euclideanRectangle (A.lower i) (A.upper i)) ∧
      (∀ x : ↥(euclideanRectangle (A.lower i) (A.upper i)), S x = subordinateSourceCoordinates A i x) ∧
      (∀ x : ↥(euclideanRectangle (A.lower i) (A.upper i)), T x = subordinateTargetCoordinates A i x) ∧
      (∀ x ∈ euclideanRectangle (A.lower i) (A.upper i),
        Function.Injective (fderivWithin ℝ S (euclideanRectangle (A.lower i) (A.upper i)) x)) ∧
      (∀ x ∈ euclideanRectangle (A.lower i) (A.upper i),
        Function.Injective (fderivWithin ℝ T (euclideanRectangle (A.lower i) (A.upper i)) x)) := by
    let K := euclideanRectangle (A.lower i) (A.upper i)
    let j := A.originalIndex i
    let q := fun x => H.coordinate j (p x)
    let G : Time × Time → Time × Euc 3 := fun u =>
      ((H.coordinate j u).1, H.stage (H.coordinate j u).1 (H.coordinate j u).2)
    let S : Euc 2 → Euc 2 := fun x => !₂[((q x).1 : ℝ), A.angleLift i x]
    let T : Euc 2 → Euc 4 := fun x =>
      !₂[((q x).1 : ℝ), (G (p x)).2 0, (G (p x)).2 1, (G (p x)).2 2]
    have hq : ContMDiffOn 𝓘(ℝ, Euc 2) ((𝓡∂ 1).prod (𝓡 1)) 1 q K :=
      (H.source_regular j).comp_contMDiffOn hp
    have hG : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) 1 G :=
      H.target_regular j
    have hGp := hG.comp_contMDiffOn hp
    have ht : ContDiffOn ℝ 1 (fun x : Euc 2 => ((q x).1 : ℝ)) K :=
      (contMDiff_subtypeVal_Icc.comp_contMDiffOn (contMDiff_fst.comp_contMDiffOn hq)).contDiffOn
    have hs : ContDiffOn ℝ 1 (fun x => (G (p x)).2) K :=
      (contMDiff_snd.comp_contMDiffOn hGp).contDiffOn
    have hS : ContDiffOn ℝ 1 S K := by
      apply contDiffOn_euclidean.mpr
      intro k
      fin_cases k
      · exact ht
      · exact A.angle_c1 i
    have hT : ContDiffOn ℝ 1 T K := by
      apply contDiffOn_euclidean.mpr
      intro k
      fin_cases k
      · exact ht
      · exact (contDiffOn_euclidean.mp hs) 0
      · exact (contDiffOn_euclidean.mp hs) 1
      · exact (contDiffOn_euclidean.mp hs) 2
    have hSv (x : ↥K) : S x = subordinateSourceCoordinates A i x := by
      dsimp only [S, subordinateSourceCoordinates, q]
      rw [hpv x]
    have hTv (x : ↥K) : T x = subordinateTargetCoordinates A i x := by
      dsimp only [T, subordinateTargetCoordinates, q, G]
      rw [hpv x]
    let U2 : Set (Euc 2) := {y | y 0 ∈ Icc (0 : ℝ) 1}
    let V : Euc 2 → Time × Circle := fun y => (projIcc 0 1 zero_le_one (y 0), Circle.exp (y 1))
    have hV : ContMDiffOn 𝓘(ℝ, Euc 2) ((𝓡∂ 1).prod (𝓡 1)) 1 V U2 := by
      have ht0 : ContDiff ℝ 1 (fun y : Euc 2 => y 0) := by fun_prop
      have ht1 : ContDiff ℝ 1 (fun y : Euc 2 => y 1) := by fun_prop
      exact (contMDiffOn_projIcc.comp ht0.contMDiff.contMDiffOn (fun y hy => hy)).prodMk
        ((contMDiff_circleExp.of_le (by exact le_top)).comp ht1.contMDiff |>.contMDiffOn)
    have hSU : MapsTo S K U2 := by
      intro x hx
      exact (q x).1.property
    have hVS : EqOn (V ∘ S) q K := by
      intro x hx
      apply Prod.ext
      · dsimp only [V, S, Function.comp_apply, Matrix.cons_val_zero]
        exact projIcc_val zero_le_one (q x).1
      · change Circle.exp (A.angleLift i x) = (q x).2
        rw [show q x = H.coordinate j (A.parameter i ⟨x,hx⟩) by dsimp [q]; rw [hpv ⟨x,hx⟩]]
        exact A.angle_values i ⟨x,hx⟩
    let U4 : Set (Euc 4) := {y | y 0 ∈ Icc (0 : ℝ) 1}
    let W : Euc 4 → Time × Euc 3 := fun y => (projIcc 0 1 zero_le_one (y 0), !₂[y 1, y 2, y 3])
    have hW : ContMDiffOn 𝓘(ℝ, Euc 4) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) 1 W U4 := by
      have ht0 : ContDiff ℝ 1 (fun y : Euc 4 => y 0) := by fun_prop
      have hs0 : ContDiff ℝ 1 (fun y : Euc 4 => (!₂[y 1,y 2,y 3] : Euc 3)) := by
        apply contDiff_euclidean.mpr
        intro k
        fin_cases k <;> dsimp <;> fun_prop
      exact (contMDiffOn_projIcc.comp ht0.contMDiff.contMDiffOn (fun y hy => hy)).prodMk
        hs0.contMDiff.contMDiffOn
    have hTU : MapsTo T K U4 := by
      intro x hx
      exact (q x).1.property
    have hWT : EqOn (W ∘ T) (G ∘ p) K := by
      intro x hx
      apply Prod.ext
      · dsimp only [W,T,Function.comp_apply,Matrix.cons_val_zero]
        exact projIcc_val zero_le_one (q x).1
      · ext k
        fin_cases k <;> rfl
    have rank {n : ℕ} (F : Euc 2 → Euc n) (x : Euc 2)
        (hi : Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc n) F K x)) :
        Function.Injective (fderivWithin ℝ F K x) := by
      intro u v huv
      have hh : mfderivWithin 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc n) F K x
          ((NormedSpace.fromTangentSpace x).symm u) =
          mfderivWithin 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc n) F K x
          ((NormedSpace.fromTangentSpace x).symm v) := by
        rw [mfderivWithin_eq_fderivWithin]
        simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply] using congrArg
            (NormedSpace.fromTangentSpace (F x)).symm huv
      exact (NormedSpace.fromTangentSpace x).symm.injective (hi hh)
    refine ⟨S,T,hS,hT,hSv,hTv,?_,?_⟩
    · intro x hx
      have hu := nondegenerate_rectangle_unique_diff _ _ (A.nondegenerate i) x hx
      have hi : Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) ((𝓡∂ 1).prod (𝓡 1)) q K x) := by
        change Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) ((𝓡∂ 1).prod (𝓡 1)) (H.coordinate j ∘ p) K x)
        rw [mfderiv_comp_mfderivWithin x ((H.source_regular j).mdifferentiableAt one_ne_zero)
          (hp.mdifferentiableOn one_ne_zero x hx) hu.uniqueMDiffWithinAt]
        exact (H.source_injective j (p x)).comp (hpi x hx)
      have hiv : Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) ((𝓡∂ 1).prod (𝓡 1)) (V ∘ S) K x) := by
        rw [mfderivWithin_congr hVS (hVS hx)]
        exact (tangentSpaceCast ((𝓡∂ 1).prod (𝓡 1)) (q x) ((V ∘ S) x)).injective.comp hi
      rw [mfderivWithin_comp x
        (hV.mdifferentiableOn one_ne_zero (S x) (hSU hx))
        (hS.contMDiffOn.mdifferentiableOn one_ne_zero x hx) hSU hu.uniqueMDiffWithinAt] at hiv
      exact rank S x (Function.Injective.of_comp hiv)
    · intro x hx
      have hu := nondegenerate_rectangle_unique_diff _ _ (A.nondegenerate i) x hx
      have hi : Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) (G ∘ p) K x) := by
        rw [mfderiv_comp_mfderivWithin x (hG.mdifferentiableAt one_ne_zero)
          (hp.mdifferentiableOn one_ne_zero x hx) hu.uniqueMDiffWithinAt]
        exact (H.target_injective j (p x)).comp (hpi x hx)
      have hiv : Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) (W ∘ T) K x) := by
        rw [mfderivWithin_congr hWT (hWT hx)]
        exact (tangentSpaceCast ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) ((G ∘ p) x) ((W ∘ T) x)).injective.comp hi
      rw [mfderivWithin_comp x
        (hW.mdifferentiableOn one_ne_zero (T x) (hTU hx))
        (hT.contMDiffOn.mdifferentiableOn one_ne_zero x hx) hTU hu.uniqueMDiffWithinAt] at hiv
      exact rank T x (Function.Injective.of_comp hiv)
  obtain ⟨S,T,hS,hT,hSv,hTv,hSi,hTi⟩ := coordinates
  classical
  let K := euclideanRectangle (A.lower i) (A.upper i)
  obtain ⟨s⟩ := finite_c1_closed_rectangle_extension (A.lower i) (A.upper i) (A.nondegenerate i) S hS
  obtain ⟨t⟩ := finite_c1_closed_rectangle_extension (A.lower i) (A.upper i) (A.nondegenerate i) T hT
  have hsi (x : Euc 2) (hx : x ∈ K) : Function.Injective (fderiv ℝ s.map x) := by
    rw [s.derivative x hx]
    exact hSi x hx
  have hti (x : Euc 2) (hx : x ∈ K) : Function.Injective (fderiv ℝ t.map x) := by
    rw [t.derivative x hx]
    exact hTi x hx
  have det (L : Euc 2 →L[ℝ] Euc 2) (hi : Function.Injective L) :
      orientedPlaneDet (L (EuclideanSpace.single 0 1)) (L (EuclideanSpace.single 1 1)) ≠ 0 := by
    let e0 : Euc 2 := EuclideanSpace.single 0 1
    let e1 : Euc 2 := EuclideanSpace.single 1 1
    have hv (v : Euc 2) : v = v 0 • e0 + v 1 • e1 := by
      ext j
      fin_cases j <;> simp [e0,e1]
    have hL (v : Euc 2) (j : Fin 2) :
        L v j = v 0 * L e0 j + v 1 * L e1 j := by
      conv_lhs => rw [hv v,map_add,map_smul,map_smul]
      simp
    intro hd
    change L e0 0 * L e1 1 - L e0 1 * L e1 0 = 0 at hd
    let v : Euc 2 := !₂[-L e1 0, L e0 0]
    have hz : L v = 0 := by
      ext j
      fin_cases j
      · rw [hL]
        change -L e1 0 * L e0 0 + L e0 0 * L e1 0 = 0
        ring
      · rw [hL]
        change -L e1 0 * L e0 1 + L e0 0 * L e1 1 = 0
        nlinarith [hd]
    have hvz : v = 0 := hi (hz.trans (map_zero L).symm)
    have ha0 : L e0 0 = 0 := congrArg (fun z : Euc 2 => z 1) hvz
    have hb0 : L e1 0 = 0 := by
      have hh := congrArg (fun z : Euc 2 => z 0) hvz
      change -L e1 0 = 0 at hh
      exact neg_eq_zero.mp hh
    let w : Euc 2 := !₂[-L e1 1, L e0 1]
    have hwz : L w = 0 := by
      ext j
      fin_cases j
      · rw [hL]
        change w 0 * L e0 0 + w 1 * L e1 0 = 0
        rw [ha0,hb0]
        simp
      · rw [hL]
        change -L e1 1 * L e0 1 + L e0 1 * L e1 1 = 0
        ring
    have hw : w = 0 := hi (hwz.trans (map_zero L).symm)
    have ha1 : L e0 1 = 0 := congrArg (fun z : Euc 2 => z 1) hw
    have he0 : L e0 = 0 := by
      ext j
      fin_cases j
      · exact ha0
      · exact ha1
    have hh : e0 = 0 := hi (he0.trans (map_zero L).symm)
    have hh0 := congrArg (fun z : Euc 2 => z 0) hh
    simpa [e0] using hh0
  have hKcompact : IsCompact K := by
    let e := EuclideanSpace.equiv (Fin 2) ℝ
    have hrect : K = e ⁻¹' (Set.pi Set.univ (fun j => Icc (A.lower i j) (A.upper i j))) := by
      ext x
      change (∀ j, A.lower i j ≤ x j ∧ x j ≤ A.upper i j) ↔ _
      simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,Set.mem_Icc,forall_true_left]
      rfl
    rw [hrect]
    exact e.toHomeomorph.isCompact_preimage.mpr
      (isCompact_univ_pi fun j => isCompact_Icc)
  have hKnonempty : K.Nonempty := ⟨A.lower i, fun j => ⟨le_rfl,(A.nondegenerate i j).le⟩⟩
  let d : Euc 2 → ℝ := fun x => |orientedPlaneDet
    (fderiv ℝ s.map x (EuclideanSpace.single 0 1))
    (fderiv ℝ s.map x (EuclideanSpace.single 1 1))|
  have hDs : ContinuousOn (fderiv ℝ s.map) K :=
    (s.c1.continuousOn_fderiv_of_isOpen s.neighborhood_open le_rfl).mono s.rectangle_inside
  have hDt : ContinuousOn (fderiv ℝ t.map) K :=
    (t.c1.continuousOn_fderiv_of_isOpen t.neighborhood_open le_rfl).mono t.rectangle_inside
  have hd : ContinuousOn d K := by
    dsimp only [d,orientedPlaneDet]
    have he0 : ContinuousOn (fun x => fderiv ℝ s.map x (EuclideanSpace.single 0 1)) K := hDs.clm_apply continuousOn_const
    have he1 : ContinuousOn (fun x => fderiv ℝ s.map x (EuclideanSpace.single 1 1)) K := hDs.clm_apply continuousOn_const
    exact (((EuclideanSpace.proj 0).continuous.comp_continuousOn he0 |>.mul
      ((EuclideanSpace.proj 1).continuous.comp_continuousOn he1)).sub
      (((EuclideanSpace.proj 1).continuous.comp_continuousOn he0).mul
      ((EuclideanSpace.proj 0).continuous.comp_continuousOn he1))).abs
  obtain ⟨xm,hxm,hmin⟩ := hKcompact.exists_isMinOn hKnonempty hd
  have hdpos : 0 < d xm := abs_pos.mpr (det _ (hsi xm hxm))
  let B := K ×ˢ Metric.sphere (0 : Euc 2) 1
  have hBcompact : IsCompact B := hKcompact.prod (isCompact_sphere 0 1)
  have hBnonempty : B.Nonempty := by
    obtain ⟨x,hx⟩ := hKnonempty
    refine ⟨(x,EuclideanSpace.single 0 1),hx,?_⟩
    simp
  let m : (Euc 2 × Euc 2) → ℝ := fun q => ‖fderiv ℝ t.map q.1 q.2‖
  have hm : ContinuousOn m B := by
    exact ((hDt.comp continuousOn_fst (fun q hq => hq.1)).clm_apply continuousOn_snd).norm
  obtain ⟨vm,hvm,hvmin⟩ := hBcompact.exists_isMinOn hBnonempty hm
  have hmpos : 0 < m vm := by
    rw [norm_pos_iff]
    intro hz
    have hh : vm.2 = 0 := hti vm.1 hvm.1 (hz.trans (map_zero _).symm)
    have hs := hvm.2
    simp [hh] at hs
  let k := min (d xm) (m vm)
  have hk : 0 < k := lt_min hdpos hmpos
  refine ⟨{
    neighborhood := s.neighborhood ∩ t.neighborhood
    neighborhood_open := s.neighborhood_open.inter t.neighborhood_open
    rectangle_inside := fun x hx => ⟨s.rectangle_inside hx,t.rectangle_inside hx⟩
    source := s.map
    target := t.map
    source_c1 := s.c1.mono inter_subset_left
    target_c1 := t.c1.mono inter_subset_right
    source_values := ?_
    target_values := ?_
    lowerBound := k
    lowerBound_pos := hk
    source_minor := ?_
    target_lower := ?_ }⟩
  · intro x
    exact (s.values x.property).trans (hSv x)
  · intro x
    exact (t.values x.property).trans (hTv x)
  · intro x hx
    exact (min_le_left _ _).trans (hmin hx)
  · intro x hx v
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hun : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := norm_smul_inv_norm hv
    have hunit : (x,(‖v‖⁻¹ : ℝ) • v) ∈ B := ⟨hx,by simpa using hun⟩
    have hb : k ≤ ‖fderiv ℝ t.map x ((‖v‖⁻¹ : ℝ) • v)‖ :=
      calc
        k ≤ m vm := min_le_right (d xm) (m vm)
        _ ≤ m (x,(‖v‖⁻¹ : ℝ) • v) := hvmin hunit
        _ = _ := rfl
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)] at hb
    apply (le_div_iff₀ hn).mp
    simpa only [div_eq_mul_inv,mul_comm] using hb

/-- X4: all values and the exact cover come from the same supplied coordinates. -/
def extensionCoverFromRectangles {f g : Circle → Euc 3} {H : PiecewiseCurveIsotopy f g}
    (A : SubordinateAngleRectangles H) (E : ∀ i, ExactRectangleExtension A i) :
    FiniteCurveExtensionCover H where
  count := A.count
  lower := A.lower
  upper := A.upper
  nondegenerate := A.nondegenerate
  coordinateIndex := A.originalIndex
  parameter := A.parameter
  neighborhood := fun i => (E i).neighborhood
  neighborhood_open := fun i => (E i).neighborhood_open
  neighborhood_contains := fun i => (E i).rectangle_inside
  sourceCoordinates := fun i => (E i).source
  targetCoordinates := fun i => (E i).target
  source_regular := fun i => (E i).source_c1
  target_regular := fun i => (E i).target_c1
  source_time := by
    intro i x
    rw [(E i).source_values]
    rfl
  source_angle := by
    intro i x
    rw [(E i).source_values]
    exact A.angle_values i x
  target_eq := fun i x => (E i).target_values x
  lowerBound := fun i => (E i).lowerBound
  lowerBound_pos := fun i => (E i).lowerBound_pos
  source_minor := fun i => (E i).source_minor
  target_lower := fun i => (E i).target_lower
  covers := by
    ext p
    constructor
    · rintro hp
      obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp hp
      rw [← hx]
      change (((E i).source x) 0, Circle.exp (((E i).source x) 1)) ∈ Icc (0 : ℝ) 1 ×ˢ univ
      rw [(E i).source_values]
      change ((H.coordinate (A.originalIndex i) (A.parameter i x)).1 : ℝ) ∈ Icc (0 : ℝ) 1 ∧ _
      exact ⟨(H.coordinate (A.originalIndex i) (A.parameter i x)).1.property, Set.mem_univ _⟩
    · rintro ⟨hp, _⟩
      let q : Time × Circle := (⟨p.1, hp⟩, p.2)
      have hq : q ∈ ⋃ j, Set.range (H.coordinate j) := by rw [H.covers]; trivial
      obtain ⟨j, u, hu⟩ := Set.mem_iUnion.mp hq
      have huA : u ∈ ⋃ i, if A.originalIndex i = j then Set.range (A.parameter i) else ∅ := by
        rw [A.original_square_covers j]
        trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp huA
      by_cases hij : A.originalIndex i = j
      · rw [if_pos hij] at hi
        obtain ⟨x, hx⟩ := hi
        apply Set.mem_iUnion.mpr
        refine ⟨i, x, ?_⟩
        change (((E i).source x) 0, Circle.exp (((E i).source x) 1)) = p
        rw [(E i).source_values]
        apply Prod.ext
        · change ((H.coordinate (A.originalIndex i) (A.parameter i x)).1 : ℝ) = p.1
          rw [hij, hx, hu]
        · change Circle.exp (A.angleLift i x) = p.2
          rw [A.angle_values, hij, hx, hu]
      · rw [if_neg hij] at hi
        exact hi.elim

theorem extension_cover_literal_fields {f g : Circle → Euc 3} {H : PiecewiseCurveIsotopy f g}
    (A : SubordinateAngleRectangles H) (E : ∀ i, ExactRectangleExtension A i) :
    (extensionCoverFromRectangles A E).coordinateIndex = A.originalIndex ∧
    (extensionCoverFromRectangles A E).parameter = A.parameter ∧
    (∀ i, (extensionCoverFromRectangles A E).sourceCoordinates i = (E i).source ∧
      (extensionCoverFromRectangles A E).targetCoordinates i = (E i).target) := by
  exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

end
end SeifertSurfaces.LongitudeProducers.DiagramRemainingHelpers
