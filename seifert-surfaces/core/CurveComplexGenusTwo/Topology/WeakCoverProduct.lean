import CurveComplexGenusTwo.Topology.WeakProduct

namespace CurveComplexGenusTwo.Topology

open Set

/-- A weak cover remains weak after taking a product with a locally compact
space. The pieces use the actual subspace topology of the ambient product. -/
theorem weakTopologyFromCover_product
    {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace Y]
    (pieces : I → Set X) (hweak : HasWeakTopologyFromCover pieces) :
    HasWeakTopologyFromCover
      (fun i => {p : X × Y | p.1 ∈ pieces i}) := by
  constructor
  · ext p
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨i, hi⟩ : ∃ i, p.1 ∈ pieces i := by
        have hx : p.1 ∈ ⋃ i, pieces i := by rw [hweak.1]; trivial
        exact mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, hi⟩
  · let tprod : TopologicalSpace (X × Y) := instTopologicalSpaceProd
    let tp (i : I) : TopologicalSpace {p : X × Y | p.1 ∈ pieces i} :=
      @instTopologicalSpaceSubtype (X × Y) _ tprod
    let t : TopologicalSpace (X × Y) :=
      ⨆ i, TopologicalSpace.coinduced
        (fun p : {p : X × Y | p.1 ∈ pieces i} => (p : X × Y)) (tp i)
    change tprod = t
    apply le_antisymm
    · rw [← continuous_id_iff_le]
      apply @continuous_of_weakTopology_product X Y (X × Y) I _ _ t _ pieces hweak id
      intro i
      let Q : Set (X × Y) := {p | p.1 ∈ pieces i}
      have hv : @Continuous (Q) (X × Y) (tp i) t
          (fun p : Q => (p : X × Y)) := by
        apply continuous_iff_coinduced_le.mpr
        exact le_iSup_of_le i le_rfl
      have hm : @Continuous ((pieces i) × Y) Q inferInstance (tp i)
          (fun p : (pieces i) × Y =>
          (⟨((p.1 : X), p.2), p.1.property⟩ : Q)) := by
        exact continuous_induced_rng.mpr
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      convert hv.comp hm using 1
      funext p
      rfl
    · apply iSup_le
      intro i
      have hv : @Continuous {p : X × Y | p.1 ∈ pieces i} (X × Y)
          (tp i) tprod (fun p => (p : X × Y)) := continuous_induced_dom
      exact continuous_iff_coinduced_le.mp hv

end CurveComplexGenusTwo.Topology
