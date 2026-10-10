import CurveComplexGenusTwo.Foundations.RealizationCW

set_option maxHeartbeats 1000000

namespace CurveComplex

open Set

variable {V : Type*} [DecidableEq V]

/-- Points supported on a specified finite vertex set, whether or not that
whole set is a face. -/
def finiteSupportLocus (K : AbstractSimplicialComplex V) (F : Finset V) :
    Set (RealizationPoint K) :=
  {x | supportFinset K x ⊆ F}

private abbrev FaceWithin (K : AbstractSimplicialComplex V) (F : Finset V) :=
  {σ : Finset V // σ ⊆ F ∧ σ ∈ K.faces}

private theorem finiteFaceWithin (K : AbstractSimplicialComplex V)
    (F : Finset V) : Finite (FaceWithin K F) := by
  classical
  apply Finite.of_injective
    (fun σ : FaceWithin K F => (⟨σ.1,
      Finset.mem_powerset.mpr σ.2.1⟩ : (F.powerset : Finset (Finset V))))
  intro σ τ h
  apply Subtype.ext
  exact congrArg (fun z : (F.powerset : Finset (Finset V)) =>
    (z : Finset V)) h

theorem finiteSupportLocus_eq_iUnion_faces
    (K : AbstractSimplicialComplex V) (F : Finset V) :
    finiteSupportLocus K F =
      ⋃ σ : FaceWithin K F, faceCarrier K σ.1 := by
  ext x
  constructor
  · intro hx
    let σ := supportFinset K x
    have hσ : σ ∈ K.faces := supportFinset_mem_faces K x
    refine Set.mem_iUnion.mpr ⟨⟨σ, hx, hσ⟩, ?_⟩
    exact (mem_faceCarrier_iff_support_subset K σ x).2 Subset.rfl
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨σ, hσ⟩
    exact ((mem_faceCarrier_iff_support_subset K σ.1 x).1 hσ).trans σ.2.1

theorem isCompact_finiteSupportLocus
    (K : AbstractSimplicialComplex V) (F : Finset V) :
    IsCompact (finiteSupportLocus K F) := by
  letI := finiteFaceWithin K F
  rw [finiteSupportLocus_eq_iUnion_faces]
  apply isCompact_iUnion
  intro σ
  rw [faceCarrier_eq_range_faceInclusion K σ.1 σ.2.2]
  exact isCompact_range (continuous_faceInclusion K σ.1 σ.2.2)

/-- Finite coordinate values determine a finite-support point. -/
def finiteSupportCoordinates
    (K : AbstractSimplicialComplex V) (F : Finset V) :
    finiteSupportLocus K F → (F → ℝ) :=
  fun x w => x.1.weight w.1

theorem finiteSupportCoordinates_continuous
    (K : AbstractSimplicialComplex V) (F : Finset V) :
    Continuous (finiteSupportCoordinates K F) := by
  apply continuous_pi
  intro w
  exact (continuous_weight K w.1).comp continuous_subtype_val

theorem finiteSupportCoordinates_injective
    (K : AbstractSimplicialComplex V) (F : Finset V) :
    Function.Injective (finiteSupportCoordinates K F) := by
  intro x y hxy
  apply Subtype.ext
  apply RealizationPoint.ext
  funext w
  by_cases hw : w ∈ F
  · have h := congrArg (fun f : F → ℝ => f ⟨w, hw⟩) hxy
    exact h
  · have hxw : x.1.weight w = 0 := by
      by_contra hn
      exact hw (x.property ((mem_supportFinset_iff K x.1 w).2 hn))
    have hyw : y.1.weight w = 0 := by
      by_contra hn
      exact hw (y.property ((mem_supportFinset_iff K y.1 w).2 hn))
    rw [hxw, hyw]

theorem finiteSupportCoordinates_isClosedEmbedding
    (K : AbstractSimplicialComplex V) (F : Finset V) :
    Topology.IsClosedEmbedding (finiteSupportCoordinates K F) := by
  have hcompact : CompactSpace (finiteSupportLocus K F) :=
    isCompact_iff_compactSpace.mp
      (isCompact_finiteSupportLocus K F)
  letI := hcompact
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (finiteSupportCoordinates_continuous K F)
    (finiteSupportCoordinates_injective K F)
  intro S hS
  exact (hS.isCompact.image
    (finiteSupportCoordinates_continuous K F)).isClosed

/-- To map continuously into a finite-support locus, it suffices to check
each barycentric coordinate of that finite vertex set. -/
theorem continuous_into_finiteSupportLocus_iff
    {A : Type*} [TopologicalSpace A]
    (K : AbstractSimplicialComplex V) (F : Finset V)
    (f : A → finiteSupportLocus K F) :
    Continuous f ↔ ∀ w : F, Continuous (fun a => (f a).1.weight w.1) := by
  rw [(finiteSupportCoordinates_isClosedEmbedding K F).isEmbedding.continuous_iff]
  exact continuous_pi_iff

theorem continuous_of_finite_support_and_coordinates
    {A : Type*} [TopologicalSpace A]
    (K : AbstractSimplicialComplex V) (F : Finset V)
    (f : A → RealizationPoint K)
    (hF : ∀ a, f a ∈ finiteSupportLocus K F)
    (hcoord : ∀ w : F, Continuous (fun a => (f a).weight w.1)) :
    Continuous f := by
  have hsub : Continuous (fun a =>
      (⟨f a, hF a⟩ : finiteSupportLocus K F)) :=
    (continuous_into_finiteSupportLocus_iff K F _).2 hcoord
  exact continuous_subtype_val.comp hsub

end CurveComplex
