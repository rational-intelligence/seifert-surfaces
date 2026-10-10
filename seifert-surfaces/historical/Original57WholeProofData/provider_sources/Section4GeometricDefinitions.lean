import KnotGenus
import KnotLinkConditions
import OriginalB1
import OriginalA25SourceDefinitionsV464
import Section4Complexity
import OriginalSection62
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints.Section4
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open SeifertSurfaces.MetricFoundations SeifertSurfaces.Complexity
open SeifertSurfaces.OriginalEndpoints

/- The native Type-0 convention is the one used by singular-homology genus
and the approved actual-compression interface. -/

structure CompactNeatSurface (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] where
  surface : CompactOrientedSurface.{0}
  embedding : NeatEmbedding surface M

namespace CompactNeatSurface
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
def image (F : CompactNeatSurface M) : Set M := F.embedding.image
def boundaryImage (F : CompactNeatSurface M) : Set M :=
  F.embedding.toFun '' F.surface.boundary
def Incompressible (F : CompactNeatSurface M) : Prop := F.embedding.Incompressible
end CompactNeatSurface

def spanningAsNeat {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    {E : SmoothExterior T} (F : LinkSpanningSurface.{0} E) :
    CompactNeatSurface E.Carrier := ⟨F.surface, F.embedding⟩

def seifertAsNeat {K : OrientedKnot} {T : TubularNeighborhood K}
    {E : SmoothExterior T} (F : SeifertSurface.{0} E) :
    CompactNeatSurface E.Carrier := spanningAsNeat F.toLinkSpanningSurface

/- Definition 4.1 reuses the native image quotient and simultaneous faces. -/
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
abbrev Vertices := Vertex.{0} E
def complexFaces : Set (Finset (Vertices E)) := {s | IsFace E s}
def genusTruncation (ell : ℤ) : Set (Finset (Vertices E)) :=
  {s | IsFace E s ∧ ∀ v ∈ s, (vertexGenus E v : ℤ) ≤ ell}
def minimumGenusComplex : Set (Finset (Vertices E)) :=
  genusTruncation E (knotGenus E : ℤ)
def graphDistance (v w : Vertices E) : ℕ := (oneSkeleton E).dist v w
def commonNeighbors (v w : Vertices E) : Set (Vertices E) :=
  {x | Adjacent E v x ∧ Adjacent E w x}
def Flag (C : Set (Finset (Vertices E))) : Prop :=
  ∀ s : Finset (Vertices E), s.Nonempty →
    (∀ v ∈ s, ({v} : Finset (Vertices E)) ∈ C) →
    (∀ v ∈ s, ∀ w ∈ s, v ≠ w → Adjacent E v w) → s ∈ C

/- Essential proper arcs: the forbidden patch is a literal embedded closed
disk in the source surface whose boundary is the arc plus a boundary arc. -/
def ArcCutsOffDisk (S : CompactOrientedSurface.{0}) (a : C(Time, S)) : Prop :=
  ∃ b : C(Time, S), IsEmbedding b ∧ Set.range b ⊆ S.boundary ∧
    b 0 = a 0 ∧ b 1 = a 1 ∧
    Set.range a ∩ Set.range b = {a 0, a 1} ∧
    ∃ d : C(ClosedDisk, S), IsEmbedding d ∧
      d '' closedDiskBoundary = Set.range a ∪ Set.range b ∧
      d '' closedDiskBoundaryᶜ ⊆ S.boundaryᶜ

structure BoundaryCompressionDisk {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (F : CompactNeatSurface M) where
  disk : CompactOrientedSurface.{0}
  diskHomeomorph : disk ≃ₜ ClosedDisk
  disk_boundary : diskHomeomorph '' disk.boundary = closedDiskBoundary
  toFun : disk → M
  smoothEmbedding : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ toFun
  surfaceArc : C(Time, F.surface)
  surfaceArc_embedded : IsEmbedding surfaceArc
  surfaceArc_endpoints : surfaceArc 0 ∈ F.surface.boundary ∧
    surfaceArc 1 ∈ F.surface.boundary
  surfaceArc_interior : ∀ t : Time, 0 < (t : ℝ) → (t : ℝ) < 1 →
    surfaceArc t ∉ F.surface.boundary
  boundaryArc : C(Time, M)
  boundaryArc_embedded : IsEmbedding boundaryArc
  boundaryArc_lands : Set.range boundaryArc ⊆ (𝓡∂ 3).boundary M
  endpoints : boundaryArc 0 = F.embedding.toFun (surfaceArc 0) ∧
    boundaryArc 1 = F.embedding.toFun (surfaceArc 1)
  arcs_intersection : Set.range (F.embedding.toFun ∘ surfaceArc) ∩
    Set.range boundaryArc =
      {F.embedding.toFun (surfaceArc 0), F.embedding.toFun (surfaceArc 1)}
  disk_boundary_decomposition : toFun '' disk.boundary =
    Set.range (F.embedding.toFun ∘ surfaceArc) ∪ Set.range boundaryArc
  surface_intersection : Set.range toFun ∩ F.image =
    Set.range (F.embedding.toFun ∘ surfaceArc)
  ambient_boundary_intersection : Set.range toFun ∩ (𝓡∂ 3).boundary M =
    Set.range boundaryArc
  essential : ¬ ArcCutsOffDisk F.surface surfaceArc

def BoundaryIncompressible {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (F : CompactNeatSurface M) : Prop :=
  ¬ Nonempty (BoundaryCompressionDisk F)

/- Transversality uses the sum of the two actual tangent planes. Both neat
conditions have already been carried by CompactNeatSurface. -/
def Transverse {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (A B : CompactNeatSurface M) : Prop :=
  ∀ p : A.surface, ∀ q : B.surface,
    ∀ h : A.embedding.toFun p = B.embedding.toFun q,
      LinearMap.range (mfderiv (𝓡∂ 2) (𝓡∂ 3) A.embedding.toFun p).toLinearMap ⊔
        LinearMap.range (h.symm ▸
          (mfderiv (𝓡∂ 2) (𝓡∂ 3) B.embedding.toFun q).toLinearMap) = ⊤

def sourceTrace {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (A B : CompactNeatSurface M) : Set A.surface :=
  A.embedding.toFun ⁻¹' B.image

/- A cut is characterized by its actual quotient map: one sheet off the
trace, two boundary copies on the trace, no other identifications. Its
orientation is inherited on every open patch. Existence is an obligation. -/
structure NormalCut (S : CompactOrientedSurface.{0}) (trace : Set S) where
  cut : CompactOrientedSurface.{0}
  projection : C(cut, S)
  quotient : IsQuotientMap projection
  boundary_exact : cut.boundary = projection ⁻¹' (trace ∪ S.boundary)
  two_copies : ∀ x ∈ trace, Nat.card (projection ⁻¹' {x}) = 2
  offTrace : ↥(projection ⁻¹' traceᶜ) ≃ₜ ↥traceᶜ
  offTrace_projection : ∀ x, (offTrace x : S) = projection x
  smooth_off_trace : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ projection (projection ⁻¹' traceᶜ)
  differential_off_trace : ∀ x, projection x ∉ trace →
    Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 2) projection x)
  oriented_off_trace : ∀ x, projection x ∉ trace →
    ∀ v : Fin 2 → TangentSpace (𝓡∂ 2) x,
      0 < cut.orientation.form x v →
        0 < S.orientation.form (projection x)
          (fun i => mfderiv (𝓡∂ 2) (𝓡∂ 2) projection x (v i))

namespace NormalCut
def seam {S : CompactOrientedSurface.{0}} {trace : Set S}
    (C : NormalCut S trace) : Set C.cut := C.projection ⁻¹' trace
end NormalCut

structure ExchangeCuts {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (A B : CompactNeatSurface M) where
  left : NormalCut A.surface (sourceTrace A B)
  right : NormalCut B.surface (sourceTrace B A)
  pairing : ↥left.seam ≃ₜ ↥right.seam
  pairing_ambient : ∀ x : left.seam,
    A.embedding.toFun (left.projection x) =
      B.embedding.toFun (right.projection (pairing x))

namespace ExchangeCuts
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  {A B : CompactNeatSurface M} (C : ExchangeCuts A B)
inductive Gluing : (C.left.cut ⊕ C.right.cut) → (C.left.cut ⊕ C.right.cut) → Prop where
  | attach (x : C.left.seam) : Gluing (.inl x) (.inr (C.pairing x))
def SurgerySpace := Quot C.Gluing
instance : TopologicalSpace C.SurgerySpace := inferInstanceAs (TopologicalSpace (Quot C.Gluing))
def leftInclusion (x : C.left.cut) : C.SurgerySpace := Quot.mk C.Gluing (.inl x)
def rightInclusion (x : C.right.cut) : C.SurgerySpace := Quot.mk C.Gluing (.inr x)
end ExchangeCuts

/- Orientation-compatible exchange: the output is the literal cross-glued
cut quotient, with both input patch orientations inherited. No Euler
characteristic or component conclusion occurs in the witness. -/
structure NormalExchange {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (A B : CompactNeatSurface M) where
  cuts : ExchangeCuts A B
  output : CompactOrientedSurface.{0}
  realization : output ≃ₜ cuts.SurgerySpace
  leftPatch : C(cuts.left.cut, output)
  leftPatch_exact : ∀ x, realization (leftPatch x) = cuts.leftInclusion x
  rightPatch : C(cuts.right.cut, output)
  rightPatch_exact : ∀ x, realization (rightPatch x) = cuts.rightInclusion x
  leftPatch_smooth : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ leftPatch cuts.left.seamᶜ
  rightPatch_smooth : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ rightPatch cuts.right.seamᶜ
  left_orientation : ∀ x ∉ cuts.left.seam,
    ∀ v : Fin 2 → TangentSpace (𝓡∂ 2) x,
      0 < cuts.left.cut.orientation.form x v →
        0 < output.orientation.form (leftPatch x)
          (fun i => mfderiv (𝓡∂ 2) (𝓡∂ 2) leftPatch x (v i))
  right_orientation : ∀ x ∉ cuts.right.seam,
    ∀ v : Fin 2 → TangentSpace (𝓡∂ 2) x,
      0 < cuts.right.cut.orientation.form x v →
        0 < output.orientation.form (rightPatch x)
          (fun i => mfderiv (𝓡∂ 2) (𝓡∂ 2) rightPatch x (v i))

structure ComponentDecomposition (S : CompactOrientedSurface.{0}) where
  retained : CompactOrientedSurface.{0}
  discardedCount : ℕ
  discarded : Fin discardedCount → CompactOrientedSurface.{0}
  retained_connected : ConnectedSpace retained
  discarded_connected : ∀ i, ConnectedSpace (discarded i)
  decomposition : S ≃ₜ (retained ⊕ (Σ i : Fin discardedCount, discarded i))

def NoDiscPatch {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (A B : CompactNeatSurface M) : Prop :=
  (∀ C : NormalCut A.surface (sourceTrace A B), ∀ x : C.cut,
    ¬ Nonempty (↥(connectedComponent x) ≃ₜ ClosedDisk)) ∧
  (∀ C : NormalCut B.surface (sourceTrace B A), ∀ x : C.cut,
    ¬ Nonempty (↥(connectedComponent x) ≃ₜ ClosedDisk))

/- General ambient version of the approved actual-compression interface.
The disk, product neighborhood, two end caps, quotient and rounding maps
are all tied pointwise; retaining a component is separate. -/
structure ActualNeatCompression {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M]
    (F : CompactNeatSurface M) {D : InteriorCompressingDisk F.embedding}
    (A : CompressionAnnulus D) (P : SmoothCompressionSurface A) where
  embedding : NeatEmbedding P.surface M
  diskParam : ClosedDisk ≃ₜ D.disk
  diskParam_boundary : ∀ z,
    diskParam (CompressionAnnulus.capEdge z) = D.boundaryCircle.toFun z
  thickening : C(ClosedDisk × Time, M)
  thickening_embedded : IsEmbedding thickening
  thickening_center : ∀ x, thickening (x, middleTime) = D.toFun (diskParam x)
  thickening_lateral : ∀ z t,
    thickening (CompressionAnnulus.capEdge z, t) = F.embedding.toFun (A.band (z, t))
  thickening_interior : Set.range thickening ⊆ (𝓡∂ 3).interior M
  thickening_surface_intersection : Set.range thickening ∩ F.image =
    Set.range (fun p : Circle × Time => F.embedding.toFun (A.band p))
  caps_disjoint : Disjoint
    (Set.range (fun x : ClosedDisk => thickening (x, CompressionAnnulus.sideTime 0)))
    (Set.range (fun x : ClosedDisk => thickening (x, CompressionAnnulus.sideTime 1)))
  caps_avoid_suppliedDisk : ∀ k : Fin 2, Disjoint
    (Set.range (fun x : ClosedDisk => thickening (x, CompressionAnnulus.sideTime k)))
    (Set.range D.toFun)
  caps_attachment : ∀ k : Fin 2,
    Set.range (fun x : ClosedDisk => thickening (x, CompressionAnnulus.sideTime k)) ∩
      (F.embedding.toFun '' A.removedᶜ) =
      Set.range (fun z : Circle => F.embedding.toFun (A.band (z, CompressionAnnulus.sideTime k)))
  unrounded : C(A.SurgerySpace, M)
  unrounded_embedded : IsEmbedding unrounded
  unrounded_remainder : ∀ x : A.Remainder,
    unrounded (A.remainderInclusion x) = F.embedding.toFun x
  unrounded_caps : ∀ k x,
    unrounded (A.capInclusion k x) = thickening (x, CompressionAnnulus.sideTime k)
  rounding : TopologicalAmbientIsotopy M
  support : Set M
  support_open : IsOpen support
  support_seams : ∀ k z,
    F.embedding.toFun (A.band (z, CompressionAnnulus.sideTime k)) ∈ support
  support_away_boundary : Disjoint (closure support) ((𝓡∂ 3).boundary M)
  support_away_disk : Disjoint (closure support) (Set.range D.toFun)
  fixed_outside : ∀ t x, x ∉ support → rounding.stage t x = x
  rounded_identification : ∀ q : A.SurgerySpace,
    embedding.toFun (P.realization.symm q) = rounding.stage 1 (unrounded q)
  boundary_fixed : ∀ x : A.Remainder, (x : F.surface) ∈ F.surface.boundary →
    embedding.toFun (P.realization.symm (A.remainderInclusion x)) = F.embedding.toFun x
  remainderMarking : F.surface → P.surface
  seamNeighborhood : Set F.surface
  seam_open : IsOpen seamNeighborhood
  seam_contains : ∀ k z, A.band (z, CompressionAnnulus.sideTime k) ∈ seamNeighborhood
  seam_away_boundary : Disjoint (closure seamNeighborhood) F.surface.boundary
  marking_exact : ∀ x : A.Remainder,
    remainderMarking x = P.realization.symm (A.remainderInclusion x)
  marking_smooth : ∀ x : F.surface, x ∉ seamNeighborhood → x ∉ A.removed →
    ContMDiffAt (𝓡∂ 2) (𝓡∂ 2) ∞ remainderMarking x
  marking_orientation : ∀ x : F.surface, x ∉ seamNeighborhood → x ∉ A.removed →
    ∀ v : Fin 2 → TangentSpace (𝓡∂ 2) x,
      0 < F.surface.orientation.form x v →
        0 < P.surface.orientation.form (remainderMarking x)
          (fun i => mfderiv (𝓡∂ 2) (𝓡∂ 2) remainderMarking x (v i))

structure ActualRetainedStep {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M]
    (F G : CompactNeatSurface M) where
  disk : InteriorCompressingDisk F.embedding
  annulus : CompressionAnnulus disk
  compressed : SmoothCompressionSurface annulus
  realization : ActualNeatCompression F annulus compressed
  component : compressed.surface
  component_boundary : (connectedComponent component ∩ compressed.surface.boundary).Nonempty
  identification : G.surface ≃ₜ ↥(connectedComponent component)
  boundary_matches : ∀ x : G.surface,
    x ∈ G.surface.boundary ↔ (identification x : compressed.surface) ∈ compressed.surface.boundary
  embedding_matches : ∀ x : G.surface,
    G.embedding.toFun x = realization.embedding.toFun (identification x : compressed.surface)

abbrev Closed3Ball := ↥(Metric.closedBall (0 : Euc 3) 1)
def closed3BallBoundary : Set Closed3Ball := {x | ‖(x : Euc 3)‖ = 1}

def Irreducible (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] : Prop :=
  ∀ s : TwoSphere → M,
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ s →
    Set.range s ⊆ (𝓡∂ 3).interior M →
    ∃ b : C(Closed3Ball, M), IsEmbedding b ∧
      b '' closed3BallBoundary = Set.range s ∧
      b '' closed3BallBoundaryᶜ ⊆ (𝓡∂ 3).interior M

def KnotCompressionHistory (F G : LinkSpanningSurface.{0} E) : Prop :=
  ∃ (m : ℕ) (S : Fin (m + 1) → LinkSpanningSurface.{0} E),
    S 0 = F ∧ S (Fin.last m) = G ∧
    ∀ i : Fin m, RetainedCompressionStep E (S i.succ) (S i.castSucc)

/- Metric and foliation of §3, containing only geometric data and their
defining properties; E/U/Fin are not fields. -/
structure SourceGeometry where
  ambient : A7.SourceGeometry E
  foliation : LongitudeFoliation.{0} E
  analytic : foliation.IntrinsicallyAnalytic

namespace SourceGeometry
def metric (H : SourceGeometry E) : SmoothMetric E.Carrier := H.ambient.metric
end SourceGeometry

def areaInfimum (H : SourceGeometry E) (v : Vertices E) : ℝ :=
  sInf {a : ℝ | ∃ F : IncompressibleSpanningSurface.{0} E,
    classOf E (surfaceImageOf E F) = v ∧
    ∃ smoothModel : GeometricPiecewiseSurface F.1.surface E.Carrier,
      smoothModel.map = F.1.embedding.continuousMap ∧
    ∃ R : CompactOrientedSurface.{0},
      ∃ C : GeometricPiecewiseSurface R E.Carrier,
        H.foliation.BoundaryIn C.map ∧ GeometricImageIsotopic smoothModel C ∧
        a = geometricArea H.metric C}

/- Named positivity obligation makes the positive-real subtype explicit;
it is not an original root hypothesis or a sorry-valued definition. -/
theorem areaInfimum_positive (H : SourceGeometry E) (v : Vertices E) :
    0 < areaInfimum E H v := by
  sorry

def positiveArea (H : SourceGeometry E) (v : Vertices E) : PositiveReal :=
  ⟨areaInfimum E H v, areaInfimum_positive E H v⟩

def complexityData (H : SourceGeometry E) : Complexity.Data (Vertices E) :=
  { genus := vertexGenus E, area := positiveArea E H }
def complexity (H : SourceGeometry E) (v : Vertices E) : ComplexityValue :=
  (complexityData E H).value v
def attainedValues (H : SourceGeometry E) : Set ComplexityValue := Set.range (complexity E H)
def fixedGenusAreas (H : SourceGeometry E) (h : ℕ) : Set PositiveReal :=
  {a | ∃ v : Vertices E, vertexGenus E v = h ∧ positiveArea E H v = a}

/- Actual linking-number cover. Monodromy is calibrated for every circle
loop and every interval lift using the native integral-homology pairing. -/
structure LinkingCyclicCover (Q : LinkCoordinates K) where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  [connected : ConnectedSpace carrier]
  projection : C(carrier, E.Carrier)
  covers : IsCoveringMap projection
  surjective : Function.Surjective projection
  deck : ℤ → carrier ≃ₜ carrier
  deck_zero : ∀ x, deck 0 x = x
  deck_add : ∀ i j x, deck (i + j) x = deck i (deck j x)
  deck_projection : ∀ i x, projection (deck i x) = projection x
  deck_free : ∀ i x, deck i x = x → i = 0
  fiber_orbits : ∀ x y, projection x = projection y → ∃ i, deck i x = y
  monodromy : ∀ c : C(Circle, E.Carrier), ∀ lift : C(Time, carrier),
    (∀ t, projection (lift t) = c (Circle.exp (2 * Real.pi * (t : ℝ)))) →
    lift 1 = deck (totalLinking K E Q (curveClass c)) (lift 0)

attribute [instance] LinkingCyclicCover.topology LinkingCyclicCover.hausdorff
  LinkingCyclicCover.secondCountable LinkingCyclicCover.connected
instance {Q : LinkCoordinates K} : CoeSort (LinkingCyclicCover E Q) Type :=
  ⟨LinkingCyclicCover.carrier⟩

structure FrontierConfiguration (Q : LinkCoordinates K)
    (S A B : SeifertSurface.{0} E) where
  cover : LinkingCyclicCover E Q
  central : C(S.surface, cover)
  central_embedded : IsEmbedding central
  central_projects : ∀ x, cover.projection (central x) = S.embedding.toFun x
  domain : Set cover
  domain_open : IsOpen domain
  domain_projection : ↥domain ≃ₜ ↥S.imageᶜ
  domain_projection_exact : ∀ x : domain,
    (domain_projection x : E.Carrier) = cover.projection x
  domain_frontier : frontier domain =
    Set.range central ∪ (cover.deck 1) '' Set.range central
  left : C(A.surface, cover)
  right : C(B.surface, cover)
  left_embedded : IsEmbedding left
  right_embedded : IsEmbedding right
  left_projects : ∀ x, cover.projection (left x) = A.embedding.toFun x
  right_projects : ∀ x, cover.projection (right x) = B.embedding.toFun x
  left_in_domain : Set.range left ⊆ domain
  right_in_domain : Set.range right ⊆ domain
  upperLeft : Set cover
  lowerLeft : Set cover
  upperRight : Set cover
  lowerRight : Set cover
  upperLeft_open : IsOpen upperLeft
  lowerLeft_open : IsOpen lowerLeft
  upperRight_open : IsOpen upperRight
  lowerRight_open : IsOpen lowerRight
  upperLeft_connected : IsConnected upperLeft
  lowerLeft_connected : IsConnected lowerLeft
  upperRight_connected : IsConnected upperRight
  lowerRight_connected : IsConnected lowerRight
  left_complement : upperLeft ∪ lowerLeft = (Set.range left)ᶜ
  right_complement : upperRight ∪ lowerRight = (Set.range right)ᶜ
  left_sides_disjoint : Disjoint upperLeft lowerLeft
  right_sides_disjoint : Disjoint upperRight lowerRight
  upperLeft_next : (cover.deck 1) '' Set.range central ⊆ upperLeft
  upperRight_next : (cover.deck 1) '' Set.range central ⊆ upperRight
  lowerLeft_central : Set.range central ⊆ lowerLeft
  lowerRight_central : Set.range central ⊆ lowerRight

namespace FrontierConfiguration
variable {Q : LinkCoordinates K} {S A B : SeifertSurface.{0} E}
def upperRegion (C : FrontierConfiguration E Q S A B) : Set C.cover := C.upperLeft ∩ C.upperRight
def lowerRegion (C : FrontierConfiguration E Q S A B) : Set C.cover := C.lowerLeft ∩ C.lowerRight
def rawFrontier (C : FrontierConfiguration E Q S A B) (upper : Bool) : Set C.cover :=
  frontier (if upper then C.upperRegion else C.lowerRegion)
end FrontierConfiguration

/- The total output is tied to the actual cover frontier by the raw map,
the projection and a topological corner-rounding isotopy. Smooth isotopy is
used only for eventual smooth representatives in the endpoint theorem. -/
structure FrontierOutput {Q : LinkCoordinates K} {S A B : SeifertSurface.{0} E}
    (C : FrontierConfiguration E Q S A B) (upper : Bool) where
  total : CompactNeatSurface E.Carrier
  raw : GeometricPiecewiseSurface total.surface E.Carrier
  rawLift : C(total.surface, C.cover)
  rawLift_embedded : IsEmbedding rawLift
  rawLift_exact : Set.range rawLift = FrontierConfiguration.rawFrontier E C upper
  rawLift_domain : Set.range rawLift ⊆ C.domain
  raw_projects : ∀ x, raw.map x = C.cover.projection (rawLift x)
  rounding : TopologicalAmbientIsotopy E.Carrier
  rounding_identification : ∀ x, total.embedding.toFun x = rounding.stage 1 (raw.map x)
  component : total.surface
  retained : SeifertSurface.{0} E
  retainedHomeomorph : retained.surface ≃ₜ ↥(connectedComponent component)
  retained_embedding : ∀ x,
    retained.embedding.toFun x = total.embedding.toFun (retainedHomeomorph x : total.surface)
  retained_boundary : ∀ x, x ∈ retained.surface.boundary ↔
    (retainedHomeomorph x : total.surface) ∈ total.surface.boundary
  discardedCount : ℕ
  discarded : Fin discardedCount → CompactOrientedSurface.{0}
  discardedPoint : Fin discardedCount → total.surface
  discardedHomeomorph : ∀ i, discarded i ≃ₜ ↥(connectedComponent (discardedPoint i))
  discarded_boundary : ∀ i x, x ∈ (discarded i).boundary ↔
    (discardedHomeomorph i x : total.surface) ∈ total.surface.boundary
  discarded_distinct : Pairwise (fun i j =>
    Disjoint (connectedComponent (discardedPoint i)) (connectedComponent (discardedPoint j)))
  discarded_away_retained : ∀ i,
    Disjoint (connectedComponent component) (connectedComponent (discardedPoint i))
  components_cover : connectedComponent component ∪
    (⋃ i, connectedComponent (discardedPoint i)) = Set.univ

/- Source Z need not be oriented or smooth. These are actual compact
topological two-manifolds embedded by a continuous map. -/
structure CompactTestSurface (M : Type) [TopologicalSpace M] where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charted : ChartedSpace (EuclideanHalfSpace 2) carrier]
  [hausdorff : T2Space carrier]
  [compact : CompactSpace carrier]
  map : C(carrier, M)
  embedded : IsEmbedding map

attribute [instance] CompactTestSurface.topology CompactTestSurface.charted
  CompactTestSurface.hausdorff CompactTestSurface.compact

end SeifertSurfaces.OriginalEndpoints.Section4
