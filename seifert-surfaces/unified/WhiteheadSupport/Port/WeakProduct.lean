import WhiteheadSupport.Port.WeakBasic
import Mathlib.Topology.CompactOpen

namespace SeifertSurfaces.WhiteheadSupport.Port.WeakTopology

open Set

/-- Continuity out of a product can be checked on a weak cover of its first
factor when the second factor is locally compact. -/
theorem continuous_of_weakTopology_product
    {X Y Z I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [LocallyCompactSpace Y]
    (pieces : I → Set X) (hweak : HasWeakTopologyFromCover pieces)
    {f : X × Y → Z}
    (hf : ∀ i, Continuous (fun p : (pieces i) × Y => f (p.1.1, p.2))) :
    Continuous f := by
  have hvertical (x : X) : Continuous (fun y : Y => f (x, y)) := by
    have hx : x ∈ ⋃ i, pieces i := by rw [hweak.1]; trivial
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    convert (hf i).comp
      ((continuous_const : Continuous fun _ : Y => (⟨x, hi⟩ : pieces i)).prodMk continuous_id) using 1
    funext y
    rfl
  let F : X → C(Y, Z) := fun x => ⟨fun y => f (x, y), hvertical x⟩
  have hF : Continuous F := by
    rw [hweak.2, continuous_iSup_dom]
    intro i
    rw [continuous_coinduced_dom]
    have hi : Continuous (fun p : (pieces i) × Y => f (p.1.1, p.2)) := hf i
    have hc := (ContinuousMap.curry ⟨_, hi⟩).continuous
    convert hc using 1
    funext x
    rfl
  convert (ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩) using 1
  funext p
  rfl


end SeifertSurfaces.WhiteheadSupport.Port.WeakTopology
