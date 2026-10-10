import CurveComplexGenusTwo.Foundations.NonseparatingRealizationBridge
import CurveComplexGenusTwo.Foundations.EdgeHomotopy

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex

noncomputable def nonseparatingVertexPoint
    (S : Type) [TopologicalSpace S]
    (v : {v : Vertex S // nonseparatingVertex v}) :
    RealizationPoint (nonseparatingComplex S) := by
  classical
  exact realizationVertex (nonseparatingComplex S) v
    ((nonseparatingComplex S).singleton_mem v)

/-- Every actual nonseparating realization point has a path to an actual
nonseparating vertex from its positive barycentric support. -/
theorem actual_nonseparating_point_joined_vertex
    (S : Type) [TopologicalSpace S]
    (x : RealizationPoint (nonseparatingComplex S)) :
    ∃ v, Joined x (nonseparatingVertexPoint S v) := by
  classical
  let K := nonseparatingComplex S
  obtain ⟨v, hv⟩ := exists_mem_openVertexStar K x
  have heq : starVertexPoint K v x hv = nonseparatingVertexPoint S v := by
    apply RealizationPoint.ext
    funext w
    simp [nonseparatingVertexPoint, realizationVertex,
      finiteSimplexVertex_faceInclusion_weight, starVertexPoint, starCone]
  refine ⟨v, ?_⟩
  rw [← heq]
  exact ⟨radialPath K v x hv⟩

/-- Two points sharing a positive nonseparating barycentric coordinate can
be joined through that vertex, using actual weak-realization radial paths. -/
theorem actual_nonseparating_points_joined_shared_vertex
    (S : Type) [TopologicalSpace S]
    (x y : RealizationPoint (nonseparatingComplex S))
    (v : {v : Vertex S // nonseparatingVertex v})
    (hx : 0 < x.weight v) (hy : 0 < y.weight v) : Joined x y := by
  classical
  let K := nonseparatingComplex S
  have hxy := starVertexPoint_eq K v x y hx hy
  exact ⟨(radialPath K v x hx).trans
    ((radialPath K v y hy).symm.cast hxy rfl)⟩

end CurveComplexGenusTwo.SourceTopology

#print axioms CurveComplexGenusTwo.SourceTopology.actual_nonseparating_point_joined_vertex
#print axioms CurveComplexGenusTwo.SourceTopology.actual_nonseparating_points_joined_shared_vertex
