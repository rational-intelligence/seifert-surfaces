import CircleRelations
import Mathlib.Topology.TietzeExtension
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped Simplicial BigOperators
open CategoryTheory CategoryTheory.Limits Convexity Set Topology

namespace SeifertSurfaces.GenusLinking.CircleConstruction
noncomputable section

abbrev RealEdge := StdSimplex ℝ (Fin 2)
abbrev RealTriangle := StdSimplex ℝ (Fin 3)

def edgeAtWeight (x : RealTriangle) : RealEdge :=
  StdSimplex.homeomorphI.symm ⟨x.weights 2, x.weights_nonneg 2, x.weights_apply_le_one 2⟩

theorem edgeAtWeight_continuous : Continuous edgeAtWeight := by
  exact StdSimplex.homeomorphI.symm.continuous.comp
    ((StdSimplex.continuous_weights_apply ℝ 2).subtype_mk _)

@[simp] theorem edgeAtWeight_face (z : RealEdge) : edgeAtWeight (simplexFace 0 z) = z := by
  apply StdSimplex.homeomorphI.injective
  apply Subtype.ext
  simp [edgeAtWeight, face_weights, Fin.sum_univ_two, Fin.succAbove,
    StdSimplex.homeomorphI_apply_coe]

theorem triangle_weights_total (x : RealTriangle) :
    x.weights 0 + x.weights 1 + x.weights 2 = 1 := by
  have hx := StdSimplex.total_of_fintype x
  simp only [Fin.sum_univ_succ, Fin.sum_univ_two, Fin.sum_univ_zero,
    add_zero] at hx
  exact (add_assoc _ _ _).trans hx

def triangleSide (i : Fin 3) : Set RealTriangle := {x | x.weights i = 0}
def triangleBoundary : Set RealTriangle := triangleSide 0 ∪ triangleSide 1 ∪ triangleSide 2

theorem triangleSide_closed (i : Fin 3) : IsClosed (triangleSide i) :=
  isClosed_eq (StdSimplex.continuous_weights_apply ℝ i) continuous_const

theorem triangleBoundary_closed : IsClosed triangleBoundary :=
  ((triangleSide_closed 0).union (triangleSide_closed 1)).union (triangleSide_closed 2)

def boundaryLift (F : C(RealEdge, ℝ)) (a : ℝ) (x : RealTriangle) : ℝ :=
  if x.weights 0 = 0 then F (edgeAtWeight x)
  else if x.weights 1 = 0 then a * x.weights 0 + F (.single 1) * x.weights 2
  else a * x.weights 0 + F (.single 0) * x.weights 1

theorem boundaryLift_side0 (F : C(RealEdge, ℝ)) (a : ℝ) (x : RealTriangle)
    (hx : x ∈ triangleSide 0) : boundaryLift F a x = F (edgeAtWeight x) := by
  change x.weights 0 = 0 at hx
  simp [boundaryLift, hx]

theorem edgeAtWeight_zero (x : RealTriangle) (hx : x.weights 2 = 0) :
    edgeAtWeight x = .single 0 := by
  apply StdSimplex.homeomorphI.injective
  simp [edgeAtWeight, hx]

theorem edgeAtWeight_one (x : RealTriangle) (hx : x.weights 2 = 1) :
    edgeAtWeight x = .single 1 := by
  apply StdSimplex.homeomorphI.injective
  simp [edgeAtWeight, hx]

theorem boundaryLift_side1 (F : C(RealEdge, ℝ)) (a : ℝ) (x : RealTriangle)
    (hx : x ∈ triangleSide 1) :
    boundaryLift F a x = a * x.weights 0 + F (.single 1) * x.weights 2 := by
  change x.weights 1 = 0 at hx
  by_cases h0 : x.weights 0 = 0
  · have h2 : x.weights 2 = 1 := by
      have ht := triangle_weights_total x
      simpa [hx, h0] using ht
    simp [boundaryLift, h0, h2, edgeAtWeight_one x h2]
  · simp [boundaryLift, h0, hx]

theorem boundaryLift_side2 (F : C(RealEdge, ℝ)) (a : ℝ) (x : RealTriangle)
    (hx : x ∈ triangleSide 2) :
    boundaryLift F a x = a * x.weights 0 + F (.single 0) * x.weights 1 := by
  change x.weights 2 = 0 at hx
  by_cases h0 : x.weights 0 = 0
  · have h1 : x.weights 1 = 1 := by
      have ht := triangle_weights_total x
      simpa [hx, h0] using ht
    simp [boundaryLift, h0, h1, edgeAtWeight_zero x hx]
  · by_cases h1 : x.weights 1 = 0
    · have h00 : x.weights 0 = 1 := by
        have ht := triangle_weights_total x
        simpa [hx, h1] using ht
      simp [boundaryLift, h0, h1, hx]
    · simp [boundaryLift, h0, h1]

theorem boundaryLift_continuousOn (F : C(RealEdge, ℝ)) (a : ℝ) :
    ContinuousOn (boundaryLift F a) triangleBoundary := by
  have h0 : ContinuousOn (boundaryLift F a) (triangleSide 0) :=
    (F.continuous.comp edgeAtWeight_continuous).continuousOn.congr
      (fun x hx => boundaryLift_side0 F a x hx)
  have h1 : ContinuousOn (boundaryLift F a) (triangleSide 1) :=
    (by fun_prop : Continuous (fun x : RealTriangle =>
      a * x.weights 0 + F (.single 1) * x.weights 2)).continuousOn.congr
      (fun x hx => boundaryLift_side1 F a x hx)
  have h2 : ContinuousOn (boundaryLift F a) (triangleSide 2) :=
    (by fun_prop : Continuous (fun x : RealTriangle =>
      a * x.weights 0 + F (.single 0) * x.weights 1)).continuousOn.congr
      (fun x hx => boundaryLift_side2 F a x hx)
  exact (h0.union_of_isClosed h1 (triangleSide_closed 0) (triangleSide_closed 1)).union_of_isClosed
    h2 ((triangleSide_closed 0).union (triangleSide_closed 1)) (triangleSide_closed 2)

theorem realTriangleFill_exists (F : C(RealEdge, ℝ)) (a : ℝ) :
    ∃ G : C(RealTriangle, ℝ), ∀ x ∈ triangleBoundary, G x = boundaryLift F a x := by
  haveI : T2Space RealTriangle :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).t2Space
  let B : C(triangleBoundary, ℝ) :=
    ⟨fun x => boundaryLift F a x, (boundaryLift_continuousOn F a).domRestrict⟩
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq triangleBoundary_closed B
  refine ⟨G, ?_⟩
  intro x hx
  exact congrArg (fun f : C(triangleBoundary, ℝ) => f ⟨x, hx⟩) hG

theorem geometricEdge_relation (s : C(RealEdge, Circle)) :
    edgeClass s = edgeClass (affineEdge 0 (simplexLog s (.single 1))) -
      edgeClass (affineEdge 0 (simplexLog s (.single 0))) := by
  obtain ⟨G, hG⟩ := realTriangleFill_exists (simplexLog s) 0
  let T : C(RealTriangle, Circle) := Circle.exp.comp G
  have hmem (i : Fin 3) (z : RealEdge) : simplexFace i z ∈ triangleSide i := by
    fin_cases i <;>
      simp [triangleSide, face_weights, Fin.sum_univ_two, Fin.succAbove]
  have h0 : T.comp (simplexFace 0) = s := by
    ext z : 1
    change Circle.exp (G (simplexFace 0 z)) = s z
    rw [hG _ (Or.inl (Or.inl (hmem 0 z))),
      boundaryLift_side0 _ _ _ (hmem 0 z), edgeAtWeight_face, simplexLog_exp]
  have h1 : T.comp (simplexFace 1) = affineEdge 0 (simplexLog s (.single 1)) := by
    ext z : 1
    change Circle.exp (G (simplexFace 1 z)) = _
    rw [hG _ (Or.inl (Or.inr (hmem 1 z))), boundaryLift_side1 _ _ _ (hmem 1 z)]
    simp [affineEdge, face_weights, Fin.sum_univ_two, Fin.succAbove]
  have h2 : T.comp (simplexFace 2) = affineEdge 0 (simplexLog s (.single 0)) := by
    ext z : 1
    change Circle.exp (G (simplexFace 2 z)) = _
    rw [hG _ (Or.inr (hmem 2 z)), boundaryLift_side2 _ _ _ (hmem 2 z)]
    simp [affineEdge, face_weights, Fin.sum_univ_two, Fin.succAbove]
  have h := edgeClass_boundary T
  rw [h0, h1, h2] at h
  apply sub_eq_zero.mp
  calc
    edgeClass s - (edgeClass (affineEdge 0 (simplexLog s (.single 1))) -
        edgeClass (affineEdge 0 (simplexLog s (.single 0)))) =
      edgeClass s - edgeClass (affineEdge 0 (simplexLog s (.single 1))) +
        edgeClass (affineEdge 0 (simplexLog s (.single 0))) := by abel
    _ = 0 := h

def pointRayClass (z : Circle) : Op1 := edgeClass (affineEdge 0 (Complex.arg z))

theorem geometricEdge_winding (s : C(RealEdge, Circle)) :
    edgeClass s = pointRayClass (s (.single 1)) - pointRayClass (s (.single 0)) +
      edgeWinding s • edgeClass (loopEdge 1) := by
  have hshift : affineEdge ((edgeWinding s : ℝ) * (2 * Real.pi))
      (Complex.arg (s (.single 1)) + edgeWinding s * (2 * Real.pi)) =
      affineEdge 0 (Complex.arg (s (.single 1))) := by
    simpa only [zero_add] using
      affineEdge_period_shift 0 (Complex.arg (s (.single 1))) (edgeWinding s)
  have h := affineEdge_triangle 0 (edgeWinding s * (2 * Real.pi))
    (Complex.arg (s (.single 1)) + edgeWinding s * (2 * Real.pi))
  rw [hshift] at h
  change pointRayClass (s (.single 1)) -
      edgeClass (affineEdge 0 (Complex.arg (s (.single 1)) + edgeWinding s * (2 * Real.pi))) +
      edgeClass (loopEdge (edgeWinding s)) = 0 at h
  rw [loopEdge_multiple] at h
  rw [geometricEdge_relation, simplexLog_first, edgeWinding_spec]
  unfold pointRayClass at h ⊢
  apply sub_eq_zero.mp
  calc
    edgeClass (affineEdge 0 (Complex.arg (s (.single 1)) + edgeWinding s * (2 * Real.pi))) -
        edgeClass (affineEdge 0 (Complex.arg (s (.single 0)))) -
        (edgeClass (affineEdge 0 (Complex.arg (s (.single 1)))) -
          edgeClass (affineEdge 0 (Complex.arg (s (.single 0)))) +
          edgeWinding s • edgeClass (loopEdge 1)) =
      -(edgeClass (affineEdge 0 (Complex.arg (s (.single 1)))) -
        edgeClass (affineEdge 0 (Complex.arg (s (.single 1)) + edgeWinding s * (2 * Real.pi))) +
        edgeWinding s • edgeClass (loopEdge 1)) := by abel
    _ = 0 := by rw [h, neg_zero]

end
end SeifertSurfaces.GenusLinking.CircleConstruction
