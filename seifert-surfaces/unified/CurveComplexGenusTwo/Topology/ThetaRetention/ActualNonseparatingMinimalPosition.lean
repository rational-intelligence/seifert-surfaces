import CurveComplexGenusTwo.Topology.ThetaRetention.ActualNonseparatingFinitePaths
import CurveComplexGenusTwo.Topology.GeometricPosition.FiniteTransverseAssembly

namespace CurveComplex

/-- Actual transverse representatives exist for every pair of source curve
vertices. Thus admissible intersection counts are never an empty set. -/
theorem source_intersection_counts_nonempty
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (α β : Vertex S) : (intersectionCounts α β).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := Quotient.exists_rep α
  obtain ⟨b, hb⟩ := Quotient.exists_rep β
  let r₀ : Bool → EssentialCurve S := fun i => if i then b else a
  obtain ⟨r, hr, ht⟩ := finite_transverse_representatives_by_extension S Bool r₀
  have htf : Transverse (r false).val (r true).val := ht false true (by decide)
  refine ⟨htf.1.toFinset.card, r false, r true, ?_, ?_, htf, rfl⟩
  · simpa [r₀] using (hr false).trans ha
  · simpa [r₀] using (hr true).trans hb

/-- The actual natural-number infimum is attained by actual transverse source
representatives, including the zero-intersection case. -/
theorem source_geometric_intersection_attained
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (α β : Vertex S) :
    ∃ a b : EssentialCurve S,
      Quotient.mk (essentialCurveSetoid S) a = α ∧
      Quotient.mk (essentialCurveSetoid S) b = β ∧
      ∃ h : Transverse a.val b.val,
        h.1.toFinset.card = geometricIntersection α β := by
  have hm : geometricIntersection α β ∈ intersectionCounts α β :=
    Nat.sInf_mem (source_intersection_counts_nonempty S α β)
  obtain ⟨a,b,ha,hb,h,he⟩ := hm
  exact ⟨a,b,ha,hb,h,he.symm⟩

/-- The minimal-position representatives of nonseparating vertices really
have connected complements; no nonseparating representative is supplied as an
extra premise. -/
theorem source_nonseparating_geometric_intersection_attained
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (α β : {v : Vertex S // nonseparatingVertex v}) :
    ∃ a b : EssentialCurve S,
      Quotient.mk (essentialCurveSetoid S) a = α.val ∧
      Quotient.mk (essentialCurveSetoid S) b = β.val ∧
      Nonseparating a.val ∧ Nonseparating b.val ∧
      ∃ h : Transverse a.val b.val,
        h.1.toFinset.card = geometricIntersection α.val β.val := by
  obtain ⟨a,b,ha,hb,h,he⟩ := source_geometric_intersection_attained S α.val β.val
  refine ⟨a,b,ha,hb,?_,?_,h,he⟩
  · have hn := α.property
    rw [← ha] at hn
    exact hn
  · have hn := β.property
    rw [← hb] at hn
    exact hn

end CurveComplex

#print axioms CurveComplex.source_intersection_counts_nonempty
#print axioms CurveComplex.source_geometric_intersection_attained
#print axioms CurveComplex.source_nonseparating_geometric_intersection_attained
