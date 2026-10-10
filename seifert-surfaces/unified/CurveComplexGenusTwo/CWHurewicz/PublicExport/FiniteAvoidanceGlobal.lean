import CurveComplexGenusTwo.CWHurewicz.PublicExport.FiniteAvoidanceCompact
import CurveComplexGenusTwo.CWHurewicz.PublicExport.CompactGlobalBound

namespace CurveComplexGenusTwo.CWHurewicz
open Topology
open scoped unitInterval

/-- A map from a compact source of Euclidean embedding dimension `k` can be
deformed into the `(k+1)`-skeleton, fixing every source point already there. -/
theorem compactSourceDimensionReduction
    {X : Type} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    {S : Type*} [TopologicalSpace S] [CompactSpace S] {k : ℕ}
    (e : S → (Fin k → ℝ)) (he : IsClosedEmbedding e)
    (f : C(S, X)) :
    ∃ g : C(S, ↥(skeletonBelow X (k+1))),
      Nonempty (ContinuousMap.HomotopyRel f
        ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X (k+1)), X)).comp g)
        {z | f z ∈ skeletonBelow X (k+1)}) := by
  obtain ⟨N,hN⟩ := compact_subset_skeletonBelow
    (K := Set.range f) (isCompact_range f.continuous)
  let m : ℕ := max N (k+1)
  have hkm : k < m := by omega
  have hfm (z : S) : f z ∈ skeletonBelow X (m+1) :=
    skeletonBelow_mono (by omega : N ≤ m+1) (hN ⟨z,rfl⟩)
  let fs : C(S, ↥(skeletonBelow X (m+1))) :=
    ⟨fun z => ⟨f z,hfm z⟩, f.continuous.subtype_mk _⟩
  obtain ⟨g,⟨H⟩⟩ := compactSourceDimensionReductionIterated e he hkm fs
  exact ⟨g,⟨H⟩⟩

end CurveComplexGenusTwo.CWHurewicz
