import WindingChains
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped Simplicial BigOperators
open CategoryTheory CategoryTheory.Limits Convexity

namespace SeifertSurfaces.GenusLinking.CircleConstruction
noncomputable section

abbrev CircleSSet := TopCat.toSSet.obj (TopCat.of Circle)
abbrev Op1 := ((integralChains Circle).opcycles 1 : Type)

def edgeClass (s : C(StdSimplex ℝ (Fin 2), Circle)) : Op1 :=
  (CircleSSet.ιChainComplex ((TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).symm s) ≫
    (integralChains Circle).pOpcycles 1) 1

theorem edgeClass_boundary (s : C(StdSimplex ℝ (Fin 3), Circle)) :
    edgeClass (s.comp (simplexFace 0)) - edgeClass (s.comp (simplexFace 1)) +
      edgeClass (s.comp (simplexFace 2)) = 0 := by
  let t := (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋2⦌)).symm s
  have hf (i : Fin 3) : CircleSSet.δ i t =
      (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).symm (s.comp (simplexFace i)) := by
    apply (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).injective
    simpa [t] using singular_face_eq t i
  have h : CircleSSet.ιChainComplex t ≫
      (CircleSSet.chainComplex (ModuleCat.of ℤ ℤ)).d (1 + 1) 1 ≫
      (integralChains Circle).pOpcycles 1 = 0 := by
    change CircleSSet.ιChainComplex t ≫ (integralChains Circle).d 2 1 ≫
      (integralChains Circle).pOpcycles 1 = 0
    simp
  rw [SSet.ιChainComplex_d_assoc] at h
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp] at h
  have he := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ (integralChains Circle).opcycles 1 => f 1) h
  simpa [Fin.sum_univ_succ, hf, edgeClass, sub_eq_add_neg, add_assoc] using he

def affineEdge (a b : ℝ) : C(StdSimplex ℝ (Fin 2), Circle) :=
  ⟨fun z => Circle.exp (a * z.weights 0 + b * z.weights 1), by fun_prop⟩

def affineTriangle (a b c : ℝ) : C(StdSimplex ℝ (Fin 3), Circle) :=
  ⟨fun z => Circle.exp (a * z.weights 0 + b * z.weights 1 + c * z.weights 2),
    by fun_prop⟩

theorem face_weights (i : Fin 3) (z : StdSimplex ℝ (Fin 2)) (j : Fin 3) :
    (simplexFace i z).weights j =
      ∑ k : Fin 2, if i.succAbove k = j then z.weights k else 0 := by
  simp [simplexFace, StdSimplex.weights_map, Finsupp.mapDomain_fintype,
    Finsupp.single_apply]

@[simp] theorem affineTriangle_face_zero (a b c : ℝ) :
    (affineTriangle a b c).comp (simplexFace 0) = affineEdge b c := by
  ext z : 1
  simp [affineTriangle, affineEdge, face_weights, Fin.sum_univ_two, Fin.succAbove]

@[simp] theorem affineTriangle_face_one (a b c : ℝ) :
    (affineTriangle a b c).comp (simplexFace 1) = affineEdge a c := by
  ext z : 1
  simp [affineTriangle, affineEdge, face_weights, Fin.sum_univ_two, Fin.succAbove]

@[simp] theorem affineTriangle_face_two (a b c : ℝ) :
    (affineTriangle a b c).comp (simplexFace 2) = affineEdge a b := by
  ext z : 1
  simp [affineTriangle, affineEdge, face_weights, Fin.sum_univ_two, Fin.succAbove]

theorem affineEdge_triangle (a b c : ℝ) :
    edgeClass (affineEdge b c) - edgeClass (affineEdge a c) +
      edgeClass (affineEdge a b) = 0 := by
  simpa using edgeClass_boundary (affineTriangle a b c)

@[simp] theorem affineEdge_constant_class (a : ℝ) : edgeClass (affineEdge a a) = 0 := by
  have h := affineEdge_triangle a a a
  simpa using h

def loopEdge (k : ℤ) : C(StdSimplex ℝ (Fin 2), Circle) :=
  affineEdge 0 (k * (2 * Real.pi))

theorem affineEdge_period_shift (a b : ℝ) (k : ℤ) :
    affineEdge (a + k * (2 * Real.pi)) (b + k * (2 * Real.pi)) = affineEdge a b := by
  ext z : 1
  have hz : z.weights 0 + z.weights 1 = 1 := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using z.total
  simp only [affineEdge, ContinuousMap.coe_mk]
  apply Circle.exp_eq_exp.mpr
  refine ⟨k, ?_⟩
  calc
    (a + k * (2 * Real.pi)) * z.weights 0 +
        (b + k * (2 * Real.pi)) * z.weights 1 =
      a * z.weights 0 + b * z.weights 1 +
        k * (2 * Real.pi) * (z.weights 0 + z.weights 1) := by ring
    _ = a * z.weights 0 + b * z.weights 1 + k * (2 * Real.pi) := by rw [hz, mul_one]

theorem loopEdge_add (k l : ℤ) :
    edgeClass (loopEdge (k + l)) = edgeClass (loopEdge k) + edgeClass (loopEdge l) := by
  have hf : affineEdge (k * (2 * Real.pi)) ((k + l : ℤ) * (2 * Real.pi)) = loopEdge l := by
    have h := affineEdge_period_shift 0 (l * (2 * Real.pi)) k
    have he : ((k + l : ℤ) : ℝ) * (2 * Real.pi) =
        l * (2 * Real.pi) + k * (2 * Real.pi) := by push_cast; ring
    rw [he]
    simpa only [zero_add, loopEdge] using h
  have ht := affineEdge_triangle 0 (k * (2 * Real.pi)) ((k + l : ℤ) * (2 * Real.pi))
  rw [hf] at ht
  change _ - edgeClass (loopEdge (k + l)) + edgeClass (loopEdge k) = 0 at ht
  apply sub_eq_zero.mp
  calc
    edgeClass (loopEdge (k + l)) - (edgeClass (loopEdge k) + edgeClass (loopEdge l)) =
      -(edgeClass (loopEdge l) - edgeClass (loopEdge (k + l)) + edgeClass (loopEdge k)) := by abel
    _ = 0 := by rw [ht, neg_zero]

@[simp] theorem loopEdge_zero : edgeClass (loopEdge 0) = 0 := by
  simp [loopEdge]

theorem loopEdge_multiple (k : ℤ) : edgeClass (loopEdge k) = k • edgeClass (loopEdge 1) := by
  let f : ℤ →+ Op1 :=
    { toFun := fun k => edgeClass (loopEdge k)
      map_zero' := loopEdge_zero
      map_add' := loopEdge_add }
  have h := f.map_zsmul k (1 : ℤ)
  change edgeClass (loopEdge (k * 1)) = k • edgeClass (loopEdge 1) at h
  simpa only [mul_one] using h

end
end SeifertSurfaces.GenusLinking.CircleConstruction
