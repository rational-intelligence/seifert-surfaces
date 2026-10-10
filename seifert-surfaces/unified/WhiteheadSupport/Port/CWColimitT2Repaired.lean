import WhiteheadSupport.Port.CWWeakSkeletonContinuity

namespace SeifertSurfaces.WhiteheadSupport.Port.CW

universe u v

open _root_.Topology

/-- Hausdorff CW variant of the skeletal mapping property. This is the
source-facing continuity interface while the original protected generic
declaration awaits a separate reviewer verdict. -/
theorem cwInfiniteColimitT2 {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (Y : Type*) [TopologicalSpace Y]
    (f : ∀ n : ℕ, C(↥(skeletonBelow X n), Y))
    (hcompat : ∀ n m (hnm : n ≤ m) (z : ↥(skeletonBelow X n)),
      f n z = f m (skeletonInclusion hnm z)) :
    ∃! h : C(X, Y), ∀ n (z : ↥(skeletonBelow X n)), h z.val = f n z := by
  exact cwInfiniteColimit_of_t2 f hcompat

/-- Hausdorff CW variant for compatible skeletal homotopies. The interval
product uses the weak cover because the interval is locally compact. -/
theorem cwHomotopyColimitT2 {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set X)]
    (f g : C(X, Y))
    (Hn : ∀ n : ℕ,
      ContinuousMap.Homotopy
        (f.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y))
        (g.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y)))
    (hcompat : ∀ n m (hnm : n ≤ m) (t : unitInterval)
      (z : ↥(skeletonBelow X n)),
      Hn n (t, z) = Hn m (t, skeletonInclusion hnm z)) :
    ContinuousMap.Homotopic f g := by
  exact cwHomotopyColimit_of_t2 f g Hn hcompat

end SeifertSurfaces.WhiteheadSupport.Port.CW
