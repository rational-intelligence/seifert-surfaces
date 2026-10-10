import CurveComplexGenusTwo.CWHurewicz.PublicExport.FiniteAvoidanceGlobal

namespace CurveComplexGenusTwo.CWHurewicz
open Topology
open scoped unitInterval

/-- A disk pair map whose boundary lies in the `(k+1)`-skeleton deforms through
based pair maps to a map entirely in that skeleton. -/
theorem relativeDiskMap_compactDimensionReduction
    {X : Type} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    {A : Set X} {k : ℕ} {x : ↥A} {b : CellSphere k}
    (hA : A ⊆ skeletonBelow X (k+1))
    (f : RelativeDiskMap k X A x b) :
    ∃ g : RelativeDiskMap k X A x b,
      Nonempty (RelativeDiskHomotopy f g) ∧
      ∀ z, g.map z ∈ skeletonBelow X (k+1) := by
  haveI : CompactSpace (CellDisk k) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Fin k → ℝ) 1)
  obtain ⟨g,⟨H⟩⟩ := compactSourceDimensionReduction
    (e := (Subtype.val : CellDisk k → (Fin k → ℝ)))
    Metric.isClosed_closedBall.isClosedEmbedding_subtypeVal f.map
  let gm : C(CellDisk k,X) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X (k+1)),X)).comp g
  have hb (t : I) (z : CellSphere k) :
      H (t,diskBoundaryInclusion k z) = f.map (diskBoundaryInclusion k z) :=
    H.prop t _ (hA (f.boundary z))
  have he (z : CellSphere k) :
      gm (diskBoundaryInclusion k z) = f.map (diskBoundaryInclusion k z) :=
    (H.map_one_left _).symm.trans (hb 1 z)
  let gr : RelativeDiskMap k X A x b := {
    map := gm
    boundary := fun z => (he z).symm ▸ f.boundary z
    based := (he b).trans f.based }
  exact ⟨gr, ⟨{
    map := H.toHomotopy.toContinuousMap
    at_zero := H.map_zero_left
    at_one := H.map_one_left
    boundary := fun t z => (hb t z).symm ▸ f.boundary z
    based := fun t => (hb t b).trans f.based }⟩, fun z => (g z).property⟩

/-- In the lower-skeleton pair, the disk map is based-pair nullhomotopic. -/
theorem relativeDiskMap_compactNullhomotopy
    {X : Type} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    {k : ℕ} {x : ↥(skeletonBelow X (k+1))} {b : CellSphere k}
    (f : RelativeDiskMap k X (skeletonBelow X (k+1)) x b) :
    Nonempty (RelativeDiskHomotopy f (RelativeDiskMap.const x b)) := by
  obtain ⟨g,⟨H⟩,hg⟩ := relativeDiskMap_compactDimensionReduction
    Set.Subset.rfl f
  exact ⟨H.trans (g.contractOfRangeSubset hg)⟩

end CurveComplexGenusTwo.CWHurewicz
