import CurveComplexGenusTwo.Topology.WeakCoverProduct

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

/-- If each closed finite face lands wholly in a cover member, that cover
inherits the weak topology of the actual geometric realization. -/
theorem realization_hasWeakTopologyFromFaceCover
    {V I : Type*} (K : AbstractSimplicialComplex V)
    (pieces : I → Set (RealizationPoint K))
    (hface : ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
      ∃ i, ∀ p : FiniteSimplex σ, faceInclusion K σ hσ p ∈ pieces i) :
    HasWeakTopologyFromCover pieces := by
  constructor
  · ext x
    constructor
    · intro _
      trivial
    · intro _
      rcases faceInclusion_surjective x with ⟨σ, hσ, p, hp⟩
      obtain ⟨i, hi⟩ := hface σ hσ
      exact mem_iUnion.mpr ⟨i, hp ▸ hi p⟩
  · let tX : TopologicalSpace (RealizationPoint K) := realizationTopology K
    let tp (i : I) : TopologicalSpace (pieces i) :=
      @instTopologicalSpaceSubtype (RealizationPoint K) _ tX
    let t : TopologicalSpace (RealizationPoint K) :=
      ⨆ i, TopologicalSpace.coinduced
        (fun x : pieces i => (x : RealizationPoint K)) (tp i)
    change tX = t
    apply le_antisymm
    · apply continuous_id_iff_le.mp
      rw [continuous_def]
      intro U hU
      change ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
        IsOpen ((faceInclusion K σ hσ) ⁻¹' U)
      intro σ hσ
      obtain ⟨i, hi⟩ := hface σ hσ
      have hpi : @Continuous (pieces i) (RealizationPoint K) (tp i) t
          (fun x => (x : RealizationPoint K)) := by
        apply continuous_iff_coinduced_le.mpr
        exact le_iSup_of_le i le_rfl
      have hsi : @Continuous (FiniteSimplex σ) (pieces i) inferInstance (tp i)
          (fun p => (⟨faceInclusion K σ hσ p, hi p⟩ : pieces i)) := by
        apply continuous_induced_rng.mpr
        rw [continuous_def]
        intro W hW
        exact hW σ hσ
      have hc := hpi.comp hsi
      simpa only [Set.preimage, Function.comp_apply, Subtype.coe_mk] using
        hc.isOpen_preimage U hU
    · apply iSup_le
      intro i
      have hpi : @Continuous (pieces i) (RealizationPoint K) (tp i) tX
          (fun x => (x : RealizationPoint K)) := continuous_induced_dom
      exact continuous_iff_coinduced_le.mp hpi

/-- Facewise covers also glue homotopies: the product weak-topology hypothesis
in the infinite-star deletion interface follows automatically. -/
theorem realization_faceCover_product_weak
    {V I : Type*} (K : AbstractSimplicialComplex V)
    (pieces : I → Set (RealizationPoint K))
    (hface : ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
      ∃ i, ∀ p : FiniteSimplex σ, faceInclusion K σ hσ p ∈ pieces i) :
    HasWeakTopologyFromCover
      (fun i => {p : RealizationPoint K × Interval | p.1 ∈ pieces i}) := by
  exact weakTopologyFromCover_product pieces
    (realization_hasWeakTopologyFromFaceCover K pieces hface)

end CurveComplexGenusTwo.Topology
