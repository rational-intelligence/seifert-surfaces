import CurveComplexGenusTwo.CWHurewicz.PublicExport.FiniteAvoidanceIteration
import CurveComplexGenusTwo.CWHurewicz.PublicExport.CompactStageSupport

namespace CurveComplexGenusTwo.CWHurewicz
open Topology
open scoped unitInterval

/-- A compact source map in a known finite successor skeleton can be deformed
to the stage just above its Euclidean embedding dimension. Finite cell
support at every intermediate stage is produced from compactness. -/
theorem compactSourceDimensionReductionIterated
    {X : Type} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    {S : Type*} [TopologicalSpace S] [CompactSpace S] {k n : ℕ}
    (e : S → (Fin k → ℝ)) (he : IsClosedEmbedding e) (hkn : k < n)
    (f : C(S, ↥(skeletonBelow X (n+1)))) :
    ∃ g : C(S, ↥(skeletonBelow X (k+1))),
      Nonempty (ContinuousMap.HomotopyRel
        ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X (n+1)), X)).comp f)
        ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X (k+1)), X)).comp g)
        {z | (f z).val ∈ skeletonBelow X (k+1)}) := by
  apply finiteCellDimensionReductionIterated e he hkn
    (fun m _ _ u => ?_) f
  obtain ⟨F,hF,hsupp⟩ := compact_stage_finiteTopCellSupport m
    (K := Set.range u) (isCompact_range u.continuous)
  exact ⟨F,hF,fun z => hsupp (u z) ⟨z,rfl⟩⟩

end CurveComplexGenusTwo.CWHurewicz
