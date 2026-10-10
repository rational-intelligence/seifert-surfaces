import Mathlib

namespace CurveComplexGenusTwo.CWHurewicz

open Convexity

theorem affineCone_face_zero {n m : ℕ}
    (f : ConvexSpace.AffineMap ℝ
      (StdSimplex ℝ (Fin (n + 1))) (StdSimplex ℝ (Fin (m + 1))))
    (y : StdSimplex ℝ (Fin (m + 1))) :
    (f.cone y).comp
        (StdSimplex.affineMap (R := ℝ) (Fin.succAbove (0 : Fin (n + 2)))) = f := by
  apply StdSimplex.affineMap_ext
  intro k
  simp [ConvexSpace.AffineMap.comp_apply]

theorem affineCone_face_succ {n m : ℕ}
    (f : ConvexSpace.AffineMap ℝ
      (StdSimplex ℝ (Fin (n + 1))) (StdSimplex ℝ (Fin (m + 1))))
    (y : StdSimplex ℝ (Fin (m + 1))) (j : Fin (n + 1)) :
    (f.cone y).comp
        (StdSimplex.affineMap (R := ℝ) (Fin.succAbove j.succ)) =
      (f.comp (StdSimplex.affineMap (R := ℝ) j.succAbove)).cone y := by
  apply StdSimplex.affineMap_ext
  intro k
  refine Fin.cases ?_ ?_ k
  · simp [ConvexSpace.AffineMap.comp_apply]
  · intro k
    simp [ConvexSpace.AffineMap.comp_apply, Fin.succ_succAbove_succ]

abbrev affineSimplex (n m : ℕ) :=
  ConvexSpace.AffineMap ℝ
    (StdSimplex ℝ (Fin (n + 1))) (StdSimplex ℝ (Fin (m + 1)))

noncomputable def affineFace {n m : ℕ}
    (f : affineSimplex (n + 1) m) (i : Fin (n + 2)) :
    affineSimplex n m :=
  f.comp (StdSimplex.affineMap (R := ℝ) i.succAbove)

noncomputable def affineBoundary {n m : ℕ}
    (f : affineSimplex (n + 1) m) :
    affineSimplex n m →₀ ℤ :=
  ∑ i : Fin (n + 2),
    (-1 : ℤ) ^ i.val • Finsupp.single (affineFace f i) 1

theorem affineBoundary_cone {n m : ℕ}
    (f : affineSimplex (n + 1) m) (y : StdSimplex ℝ (Fin (m + 1))) :
    affineBoundary (n := n + 1) (m := m) (f.cone y) =
      (Finsupp.single f 1 : affineSimplex (n + 1) m →₀ ℤ) -
        ∑ j : Fin (n + 2),
          (-1 : ℤ) ^ j.val •
            Finsupp.single ((affineFace f j).cone y) 1 := by
  unfold affineBoundary
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    affineFace, affineCone_face_zero, affineCone_face_succ,
    pow_succ, mul_neg, neg_smul]
  rw [Finset.sum_neg_distrib]
  simp
  abel

noncomputable def affineBoundaryMap (n m : ℕ) :
    (affineSimplex (n + 1) m →₀ ℤ) →ₗ[ℤ]
      (affineSimplex n m →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun f => affineBoundary f)

noncomputable def affineConeMap (n m : ℕ)
    (y : StdSimplex ℝ (Fin (m + 1))) :
    (affineSimplex n m →₀ ℤ) →ₗ[ℤ]
      (affineSimplex (n + 1) m →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun f => Finsupp.single (f.cone y) 1)

theorem affineBoundaryMap_cone {n m : ℕ}
    (c : affineSimplex (n + 1) m →₀ ℤ)
    (y : StdSimplex ℝ (Fin (m + 1))) :
    affineBoundaryMap (n + 1) m (affineConeMap (n + 1) m y c) =
      c - affineConeMap n m y (affineBoundaryMap n m c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, hc, hd, add_sub_add_comm]
  | single f a =>
      simp only [affineBoundaryMap, affineConeMap,
        Finsupp.linearCombination_single, map_smul]
      rw [affineBoundary_cone]
      simp [affineBoundary, map_sum, smul_sub, Finset.smul_sum]

noncomputable def affineConstantVertex (m : ℕ)
    (y : StdSimplex ℝ (Fin (m + 1))) : affineSimplex 0 m :=
  StdSimplex.affineMapMk (fun _ => y)

theorem affineBoundary_cone_zero {m : ℕ}
    (f : affineSimplex 0 m) (y : StdSimplex ℝ (Fin (m + 1))) :
    affineBoundary (n := 0) (f.cone y) =
      (Finsupp.single f 1 : affineSimplex 0 m →₀ ℤ) -
        Finsupp.single (affineConstantVertex m y) 1 := by
  have hzero : affineFace (f.cone y) (0 : Fin 2) = f := by
    exact affineCone_face_zero f y
  have hface : affineFace (f.cone y) (1 : Fin 2) = affineConstantVertex m y := by
    apply StdSimplex.affineMap_ext
    intro k
    fin_cases k
    simp [affineFace, affineConstantVertex]
  simp only [affineBoundary, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  rw [hzero]
  change (Finsupp.single f 1 : affineSimplex 0 m →₀ ℤ) +
    ((-1 : ℤ) ^ 1 • Finsupp.single (affineFace (f.cone y) 1) 1 + 0) = _
  rw [hface]
  abel

noncomputable def affineAugmentation (m : ℕ) :
    (affineSimplex 0 m →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => 1)

theorem affineBoundaryMap_cone_zero {m : ℕ}
    (c : affineSimplex 0 m →₀ ℤ)
    (y : StdSimplex ℝ (Fin (m + 1))) :
    affineBoundaryMap 0 m (affineConeMap 0 m y c) =
      c - (affineAugmentation m c) •
        (Finsupp.single (affineConstantVertex m y) 1 : affineSimplex 0 m →₀ ℤ) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, hc, hd, add_sub_add_comm, add_smul]
  | single f a =>
      simp only [affineBoundaryMap, affineConeMap, affineAugmentation,
        Finsupp.linearCombination_single, map_smul]
      rw [affineBoundary_cone_zero]
      simp [smul_sub]

end CurveComplexGenusTwo.CWHurewicz
