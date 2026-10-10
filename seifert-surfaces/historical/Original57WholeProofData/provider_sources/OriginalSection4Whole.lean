import Section4GeometricDefinitions
import Section4GeneralCompression

set_option autoImplicit false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open SeifertSurfaces.MetricFoundations SeifertSurfaces.Complexity
open SeifertSurfaces.OriginalEndpoints.Section4
open SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-! Whole original Section 4 package, source lines 355–567.
All assertion bodies are intentionally sorry. These are source roots, not
conditional numerical consequences with geometric conclusions supplied as inputs.
The Type-0 convention is inherited literally from the approved native genus
and original-6.2 interfaces. -/

/-- Lemma 4.2. "Longitudes" for a link are the surface-framed spanning
longitudes; no false componentwise preferred-longitude constraint is inserted.
The native surface carries all boundary labels and has no closed components. -/
theorem original_4_2 {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (hF : F.Incompressible) :
    BoundaryIncompressible (spanningAsNeat F) := by
  sorry

/-- Lemma 4.3, all clauses in one endpoint: arbitrary independently chosen
minimizers, simultaneous clique disjointness, flagness of IS and every full
integer-genus truncation, and the distance-two common-neighbor assertion. -/
theorem original_4_3 {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (H : Section4.SourceGeometry E) :
    (∀ (N : ℕ) (v : Fin N → Vertices E), Function.Injective v →
      ∀ F : Fin N → IncompressibleSpanningSurface.{0} E,
        (∀ i, classOf E (surfaceImageOf E (F i)) = v i) →
        (∀ i, IsRelativeAreaMinimizer H.metric H.foliation (F i)) →
        (∀ i j, Adjacent E (v i) (v j) → Disjoint (F i).1.image (F j).1.image) ∧
        ((Pairwise (fun i j => Adjacent E (v i) (v j))) →
          Pairwise (fun i j => Disjoint (F i).1.image (F j).1.image))) ∧
    Flag E (complexFaces E) ∧
    (∀ ell : ℤ, (knotGenus E : ℤ) ≤ ell → Flag E (genusTruncation E ell)) ∧
    (∀ u w x : Vertices E, graphDistance E u w = 2 → x ∈ commonNeighbors E u w →
      ∀ S Su Sw : IncompressibleSpanningSurface.{0} E,
        classOf E (surfaceImageOf E S) = x →
        classOf E (surfaceImageOf E Su) = u →
        classOf E (surfaceImageOf E Sw) = w →
        IsRelativeAreaMinimizer H.metric H.foliation S →
        IsRelativeAreaMinimizer H.metric H.foliation Su →
        IsRelativeAreaMinimizer H.metric H.foliation Sw →
        Disjoint S.1.image (Su.1.image ∪ Sw.1.image)) := by
  sorry

/-- Lemma 4.4. Euler accounting for every actual orientation-compatible
cross-glued quotient; the distinguished/discarded formula; strict knot-genus
compression descent and existence of an incompressible terminating descendant.
The well-founded relation is the approved actual retained-step relation. -/
theorem original_4_4 {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) :
    (∀ (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M],
      ∀ A B : CompactNeatSurface M, Transverse A B →
        ∀ X : NormalExchange A B,
          eulerCharacteristic X.output =
            eulerCharacteristic A.surface + eulerCharacteristic B.surface ∧
          (∀ D : ComponentDecomposition X.output,
            eulerCharacteristic D.retained =
              eulerCharacteristic A.surface + eulerCharacteristic B.surface -
                ∑ i, eulerCharacteristic (D.discarded i))) ∧
    (∀ G F : LinkSpanningSurface.{0} E, RetainedCompressionStep E G F →
      surfaceGenus G.surface < surfaceGenus F.surface) ∧
    WellFounded (RetainedCompressionStep E) ∧
    (¬ ∃ S : ℕ → LinkSpanningSurface.{0} E,
      ∀ i, RetainedCompressionStep E (S (i + 1)) (S i)) ∧
    (∀ F : SeifertSurface.{0} E,
      ∃ G : LinkSpanningSurface.{0} E, KnotCompressionHistory E F.toLinkSpanningSurface G ∧
        G.Incompressible) := by
  sorry

/-- Lemma 4.5. A prescribed finite sequence in a general irreducible
oriented smooth three-manifold is replaced step for step. The replacement
starts at the same P, preserves every ambient class including the endpoint,
and its actual supplied compression disks all avoid Q. For a multi-boundary
P, the given history records the chosen boundary-bearing component. -/
theorem original_4_5 (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    (orientation : SmoothVolumeOrientation (𝓡∂ 3) M)
    (hIrreducible : Section4.Irreducible M)
    (P Q : GeneralNeatSurface M)
    (hPconnected : ConnectedSpace P.surface)
    (hPboundary : P.surface.boundary.Nonempty)
    (hQ : Q.Incompressible) (hPQ : Disjoint P.image Q.image)
    (m : ℕ) (S : Fin (m + 1) → GeneralNeatSurface M)
    (hinitial : S 0 = P)
    (steps : ∀ i : Fin m, GeneralRetainedStep (S i.castSucc) (S i.succ)) :
    ∃ Snew : Fin (m + 1) → GeneralNeatSurface M,
      Snew 0 = P ∧
      (∀ i : Fin (m + 1), SmoothAmbientIsotopy.Rel (Snew i).image (S i).image) ∧
      ∃ newSteps : ∀ i : Fin m, GeneralRetainedStep (Snew i.castSucc) (Snew i.succ),
        ∀ i : Fin m, Disjoint (Set.range (newSteps i).disk.toFun) Q.image := by
  sorry

/-- Corollary 4.6 in the standing knot complex. P is allowed to be
compressible. Every actual incompressible descendant, from every finite
retained-compression history, has class equal or adjacent to Q. -/
theorem original_4_6 {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (P : SeifertSurface.{0} E)
    (Q : IncompressibleSpanningSurface.{0} E)
    (hPQ : Disjoint P.image Q.1.image) :
    ∀ R : LinkSpanningSurface.{0} E,
      KnotCompressionHistory E P.toLinkSpanningSurface R →
      ∀ hR : R.Incompressible,
        classOf E (surfaceImageOf E ⟨R, hR⟩) = classOf E (surfaceImageOf E Q) ∨
        Adjacent E (classOf E (surfaceImageOf E ⟨R, hR⟩))
          (classOf E (surfaceImageOf E Q)) := by
  sorry

/-- The assertion attached to Definition 4.7. Genus is the native quotient
invariant, area is the actual full relative-class infimum, and its positive
minimum is attained by a smooth stable minimal representative. -/
theorem original_4_7 {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (H : Section4.SourceGeometry E) :
    ∀ v : Vertices E,
      0 < areaInfimum E H v ∧
      ∃ F : IncompressibleSpanningSurface.{0} E,
        classOf E (surfaceImageOf E F) = v ∧
        IsRelativeAreaMinimizer H.metric H.foliation F ∧
        area H.metric F.1.embedding.toFun = areaInfimum E H v ∧
        MinimalEmbedding E H.ambient (ProperSmoothEmbedding.ofNeat F.1.embedding) ∧
        StableFixedBoundary E H.metric (ProperSmoothEmbedding.ofNeat F.1.embedding) := by
  sorry

/-- Lemma 4.8, all four clauses. There is no FiniteSublevels, compactness,
finite partition, attained minimum, or countability input hypothesis. The
well-order witnesses are conclusions needed to express the ordinal types. -/
theorem original_4_8 {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (H : Section4.SourceGeometry E)
    (hK : KnotIsNontrivial K) :
    (∀ (h : ℕ) (a : PositiveReal),
      {v : Vertices E | vertexGenus E v = h ∧ positiveArea E H v ≤ a}.Finite) ∧
    (∀ h : ℕ,
      IsClosed (fixedGenusAreas E H h) ∧
      DiscreteTopology (fixedGenusAreas E H h) ∧
      ∃ hw : IsWellOrder (fixedGenusAreas E H h) (· < ·),
        @Ordinal.type (fixedGenusAreas E H h) (· < ·) hw ≤ Ordinal.omega0) ∧
    (∃ hw : IsWellOrder (attainedValues E H) (· < ·),
      @Ordinal.type (attainedValues E H) (· < ·) hw ≤ Ordinal.omega0 ^ (2 : Ordinal)) ∧
    (∀ s : Set (attainedValues E H), s.Nonempty → ∃ x ∈ s, ∀ y ∈ s, x ≤ y) ∧
    Countable (Vertices E) := by
  sorry

/-- Lemma 4.9, with actual cyclic-cover frontiers. The original inputs
need not be incompressible or minimizing. The two fixed output classes are
chosen before the universal compact test surface; only their representatives
may vary with Z. Both total outputs and every discarded actual component
are included in the Euler/closedness conclusion. -/
theorem original_4_9 {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (Q : LinkCoordinates K)
    (S A B : SeifertSurface.{0} E)
    (hS : Disjoint S.image (A.image ∪ B.image))
    (hmeet : (A.image ∩ B.image).Nonempty)
    (htransverse : Transverse (seifertAsNeat A) (seifertAsNeat B))
    (hboundary : Disjoint (A.embedding.toFun '' A.surface.boundary)
      (B.embedding.toFun '' B.surface.boundary))
    (hnoDisc : NoDiscPatch (seifertAsNeat A) (seifertAsNeat B)) :
    ∃ C : FrontierConfiguration E Q S A B,
      ∃ Up : FrontierOutput E C true, ∃ Down : FrontierOutput E C false,
        (Disjoint Up.retained.image Down.retained.image ∧
         Disjoint Up.retained.image S.image ∧ Disjoint Up.retained.image A.image ∧
         Disjoint Up.retained.image B.image ∧
         Disjoint Down.retained.image S.image ∧ Disjoint Down.retained.image A.image ∧
         Disjoint Down.retained.image B.image) ∧
        (∀ Z : CompactTestSurface E.Carrier,
          Disjoint (Set.range Z.map) (A.image ∪ B.image) →
          ∃ Pup Pdown : SeifertSurface.{0} E,
            SmoothAmbientIsotopy.Rel Pup.image Up.retained.image ∧
            SmoothAmbientIsotopy.Rel Pdown.image Down.retained.image ∧
            Disjoint Pup.image (Set.range Z.map) ∧
            Disjoint Pdown.image (Set.range Z.map)) ∧
        (eulerCharacteristic Up.total.surface + eulerCharacteristic Down.total.surface =
          eulerCharacteristic A.surface + eulerCharacteristic B.surface) ∧
        (∀ i : Fin Up.discardedCount,
          (Up.discarded i).boundary = ∅ ∧ eulerCharacteristic (Up.discarded i) ≤ 0) ∧
        (∀ i : Fin Down.discardedCount,
          (Down.discarded i).boundary = ∅ ∧ eulerCharacteristic (Down.discarded i) ≤ 0) := by
  sorry

end SeifertSurfaces.OriginalEndpoints
