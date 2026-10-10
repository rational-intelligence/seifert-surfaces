import CurveComplexGenusTwo.Topology.ThetaRetention.ActualNonseparatingEdge

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex

/-- A finite sequence of actual curve vertices with intersection at most one
on consecutive terms produces a path by concatenating its realization edges. -/
noncomputable def actual_nonseparating_finite_edge_path
    (S : Type) [TopologicalSpace S]
    (v : ℕ → {v : Vertex S // nonseparatingVertex v}) (n : ℕ)
    (h : ∀ i, i < n → geometricIntersection (v i).val (v (i + 1)).val ≤ 1) :
    Path (nonseparatingVertexPoint S (v 0)) (nonseparatingVertexPoint S (v n)) := by
  induction n with
  | zero => exact Path.refl _
  | succ n ih =>
      exact (ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))).trans
        (actual_nonseparating_edge_path S (v n) (v (n + 1))
          (h n (Nat.lt_succ_self n)))

/-- The radial path is anchored at the genuine source vertex point. -/
noncomputable def actual_nonseparating_radial_path
    (S : Type) [TopologicalSpace S]
    (x : RealizationPoint (nonseparatingComplex S))
    (v : {v : Vertex S // nonseparatingVertex v}) (hx : 0 < x.weight v) :
    Path x (nonseparatingVertexPoint S v) := by
  classical
  have he : nonseparatingVertexPoint S v =
      starVertexPoint (nonseparatingComplex S) v x hx := by
    apply RealizationPoint.ext
    funext w
    simp [nonseparatingVertexPoint, realizationVertex,
      finiteSimplexVertex_faceInclusion_weight, starVertexPoint, starCone]
  exact (radialPath (nonseparatingComplex S) v x hx).cast rfl he

/-- This path joins arbitrary realization points once actual support vertices
have been connected by an explicit finite geometric edge sequence. -/
noncomputable def actual_nonseparating_points_finite_path
    (S : Type) [TopologicalSpace S]
    (x y : RealizationPoint (nonseparatingComplex S))
    (v : ℕ → {v : Vertex S // nonseparatingVertex v}) (n : ℕ)
    (h : ∀ i, i < n → geometricIntersection (v i).val (v (i + 1)).val ≤ 1)
    (hx : 0 < x.weight (v 0)) (hy : 0 < y.weight (v n)) : Path x y :=
  ((actual_nonseparating_radial_path S x (v 0) hx).trans
    (actual_nonseparating_finite_edge_path S v n h)).trans
    (actual_nonseparating_radial_path S y (v n) hy).symm

/-- The same finite geometric construction lies in the original support-zero
locus with its actual subspace topology. -/
noncomputable def source_nonseparating_points_finite_path
    (S : Type) [TopologicalSpace S]
    (x y : NonseparatingLocus S)
    (v : ℕ → {v : Vertex S // nonseparatingVertex v}) (n : ℕ)
    (h : ∀ i, i < n → geometricIntersection (v i).val (v (i + 1)).val ≤ 1)
    (hx : 0 < ((nonseparatingRealizationHomeomorph S).symm x).weight (v 0))
    (hy : 0 < ((nonseparatingRealizationHomeomorph S).symm y).weight (v n)) :
    Path x y := by
  let e := nonseparatingRealizationHomeomorph S
  let p := actual_nonseparating_points_finite_path S (e.symm x) (e.symm y) v n h hx hy
  exact (p.map e.continuous).cast (e.apply_symm_apply x).symm (e.apply_symm_apply y).symm

end CurveComplexGenusTwo.SourceTopology

#print axioms CurveComplexGenusTwo.SourceTopology.actual_nonseparating_finite_edge_path
#print axioms CurveComplexGenusTwo.SourceTopology.actual_nonseparating_radial_path
#print axioms CurveComplexGenusTwo.SourceTopology.actual_nonseparating_points_finite_path
#print axioms CurveComplexGenusTwo.SourceTopology.source_nonseparating_points_finite_path
