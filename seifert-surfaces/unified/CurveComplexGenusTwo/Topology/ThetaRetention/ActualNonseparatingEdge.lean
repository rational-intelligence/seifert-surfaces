import CurveComplexGenusTwo.Topology.ThetaRetention.ActualNonseparatingPaths
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex

noncomputable local instance (S : Type) [TopologicalSpace S] : DecidableEq (Vertex S) := by
  classical
  exact inferInstance

/-- A concrete geometric-intersection bound gives the actual nonseparating edge. -/
theorem actual_nonseparating_pair_face
    (S : Type) [TopologicalSpace S]
    (a b : {v : Vertex S // nonseparatingVertex v})
    (hab : geometricIntersection a.val b.val ≤ 1) :
    ({a,b} : Finset {v : Vertex S // nonseparatingVertex v}) ∈
      (nonseparatingComplex S).faces := by
  classical
  have h : ({a.val,b.val} : Finset (Vertex S)) ∈ (curveComplex S 1).faces := by
    refine ⟨by simp, ?_⟩
    intro α hα β hβ hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα hβ
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
    · exact (hne rfl).elim
    · exact hab
    · rw [geometricIntersection_symm_of_chart]
      exact hab
    · exact (hne rfl).elim
  simpa only [nonseparatingComplex, Set.mem_ofPred_eq, Finset.image_insert, Finset.image_singleton] using h

/-- The actual weak-realization edge between two nonseparating curve classes,
with no abstract path-connectivity or contraction premise. -/
noncomputable def actual_nonseparating_edge_path
    (S : Type) [TopologicalSpace S]
    (a b : {v : Vertex S // nonseparatingVertex v})
    (hab : geometricIntersection a.val b.val ≤ 1) :
    Path (nonseparatingVertexPoint S a) (nonseparatingVertexPoint S b) := by
  classical
  let K := nonseparatingComplex S
  have hface := actual_nonseparating_pair_face S a b hab
  let p := (finiteSegmentPath {a,b}
    (finiteSimplexVertex {a,b} a (by simp))
    (finiteSimplexVertex {a,b} b (by simp))).map
    (continuous_faceInclusion_local K {a,b} hface)
  have ha : nonseparatingVertexPoint S a =
      faceInclusion K {a,b} hface (finiteSimplexVertex {a,b} a (by simp)) := by
    apply RealizationPoint.ext
    funext w
    simp [nonseparatingVertexPoint, realizationVertex,
      finiteSimplexVertex_faceInclusion_weight]
  have hb : nonseparatingVertexPoint S b =
      faceInclusion K {a,b} hface (finiteSimplexVertex {a,b} b (by simp)) := by
    apply RealizationPoint.ext
    funext w
    simp [nonseparatingVertexPoint, realizationVertex,
      finiteSimplexVertex_faceInclusion_weight]
  exact p.cast ha hb

end CurveComplexGenusTwo.SourceTopology

#print axioms CurveComplexGenusTwo.SourceTopology.actual_nonseparating_pair_face
#print axioms CurveComplexGenusTwo.SourceTopology.actual_nonseparating_edge_path
