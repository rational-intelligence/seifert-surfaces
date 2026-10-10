import Mathlib

namespace SeifertSurfaces.WhiteheadSupport.Port.WeakTopology

open Set

/-- The weak topology of an arbitrary cover by subspaces. The index type may
be infinite; this is the condition needed for the simultaneous deletion in 6.8. -/
def HasWeakTopologyFromCover {X : Type*} [tX : TopologicalSpace X]
    {I : Type*} (pieces : I → Set X) : Prop :=
  (⋃ i, pieces i = Set.univ) ∧
    tX = ⨆ i, TopologicalSpace.coinduced
      (fun x : pieces i => (x : X)) inferInstance

end SeifertSurfaces.WhiteheadSupport.Port.WeakTopology
