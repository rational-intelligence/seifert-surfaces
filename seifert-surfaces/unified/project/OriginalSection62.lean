import LinkingHomology
import CompressionContracts
import CompressionQuotientSupport
import Lean

/-!
Repair of original Lemma 6.2, references/seifert-surfaces.txt, lines 992–1004.

The rejected predecessor quantified over the weak seam-local
`EmbeddedCompression`.  This file adds an actual realization witness: its cap
maps are the two end slices of an embedded product neighborhood centered on the
supplied disk map, the caps meet the remaining surface only at their attachment
circles, and the actual quotient surgery map is identified pointwise with a neat
embedded output through a boundary-fixed topological rounding isotopy. The intrinsic branch
conclusions and the finite retained-step endpoint are retained verbatim in
strength and labels.
-/

set_option autoImplicit false
noncomputable section
open Set Topology
open scoped Manifold ContDiff BigOperators
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking

namespace SeifertSurfaces.OriginalEndpoints

variable {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T)

/-- An actual compression along the supplied disk, including its product
neighborhood, the unrounded quotient map, and a local rounding isotopy.  This
refines the existing weak native contract without altering it.  These fields
describe construction and maps; no component count, genus, boundary allocation,
or termination conclusion is built into the witness. -/
structure ActualCompressionRealization (F : LinkSpanningSurface.{0} E)
    {D : InteriorCompressingDisk F.embedding} (A : CompressionAnnulus D)
    (P : SmoothCompressionSurface A)
    extends EmbeddedCompression E F D A P where
  /-- Boundary-compatible coordinates for the very same supplied disk. -/
  diskParam : ClosedDisk ≃ₜ D.disk
  diskParam_boundary : ∀ z,
    diskParam (CompressionAnnulus.capEdge z) = D.boundaryCircle.toFun z
  /-- The product regular neighborhood giving the two parallel copies of D. -/
  thickening : C(ClosedDisk × Time, E.Carrier)
  thickening_embedded : IsEmbedding thickening
  thickening_center : ∀ x,
    thickening (x, middleTime) = D.toFun (diskParam x)
  thickening_lateral : ∀ z t,
    thickening (CompressionAnnulus.capEdge z, t) = F.embedding.toFun (A.band (z, t))
  thickening_interior : Set.range thickening ⊆ (𝓡∂ 3).interior E.Carrier
  /-- The neighborhood meets the original surface only along its lateral annulus. -/
  thickening_surface_intersection :
    Set.range thickening ∩ F.image =
      Set.range (fun p : Circle × Time => F.embedding.toFun (A.band p))
  /-- The two end disks are disjoint actual push-offs of the central supplied disk. -/
  caps_disjoint : Disjoint
    (Set.range (fun x : ClosedDisk => thickening (x, CompressionAnnulus.sideTime 0)))
    (Set.range (fun x : ClosedDisk => thickening (x, CompressionAnnulus.sideTime 1)))
  caps_avoid_suppliedDisk : ∀ k : Fin 2, Disjoint
    (Set.range (fun x : ClosedDisk => thickening (x, CompressionAnnulus.sideTime k)))
    (Set.range D.toFun)
  caps_meet_remainder_only_at_attachment : ∀ k : Fin 2,
    Set.range (fun x : ClosedDisk => thickening (x, CompressionAnnulus.sideTime k)) ∩
      (F.embedding.toFun '' A.removedᶜ) =
      Set.range (fun z : Circle => F.embedding.toFun (A.band (z, CompressionAnnulus.sideTime k)))
  /-- The actual surgery map on the very same annulus/two-disk quotient. -/
  unrounded : C(A.SurgerySpace, E.Carrier)
  unrounded_embedded : IsEmbedding unrounded
  unrounded_remainder : ∀ x : A.Remainder,
    unrounded (A.remainderInclusion x) = F.embedding.toFun x
  unrounded_caps : ∀ (k : Fin 2) (x : ClosedDisk),
    unrounded (A.capInclusion k x) = thickening (x, CompressionAnnulus.sideTime k)
  /-- Rounding is topological: a smooth diffeomorphism cannot smooth a corner. -/
  rounding : TopologicalAmbientIsotopy E.Carrier
  roundingSupport : Set E.Carrier
  roundingSupport_open : IsOpen roundingSupport
  roundingSupport_contains_seams : ∀ (k : Fin 2) (z : Circle),
    F.embedding.toFun (A.band (z, CompressionAnnulus.sideTime k)) ∈ roundingSupport
  roundingSupport_away_boundary : Disjoint (closure roundingSupport)
    ((𝓡∂ 3).boundary E.Carrier)
  roundingSupport_away_centralDisk : Disjoint (closure roundingSupport) (Set.range D.toFun)
  rounding_fixed_outside : ∀ t x, x ∉ roundingSupport → rounding.stage t x = x
  rounding_boundary_fixed : ∀ t x, x ∈ (𝓡∂ 3).boundary E.Carrier → rounding.stage t x = x
  /-- Every quotient point of the neat output is the rounded actual surgery point. -/
  rounded_identification : ∀ q : A.SurgerySpace,
    embedding.toFun (P.realization.symm q) = rounding.stage 1 (unrounded q)
  /-- The inherited seam neighborhood has a genuine collar of untouched boundary. -/
  seam_closure_away_boundary : Disjoint (closure seamNeighborhood) F.surface.boundary
  /-- A local marking records the orientation inherited from the original remainder.
  No smoothness is required of the caller's topological annulus or quotient P. -/
  remainderMarking : F.surface → P.surface
  remainderMarking_eq : ∀ x : A.Remainder,
    remainderMarking x = P.realization.symm (A.remainderInclusion x)
  remainderMarking_smooth : ∀ x : F.surface, x ∉ seamNeighborhood → x ∉ A.removed →
    ContMDiffAt (𝓡∂ 2) (𝓡∂ 2) ∞ remainderMarking x
  remainder_orientation : ∀ (x : F.surface), x ∉ seamNeighborhood → x ∉ A.removed →
    ∀ v : Fin 2 → TangentSpace (𝓡∂ 2) x,
      0 < F.surface.orientation.form x v →
        0 < P.surface.orientation.form (remainderMarking x)
          (fun i => mfderiv (𝓡∂ 2) (𝓡∂ 2) remainderMarking x (v i))

/-- The original i-th oriented boundary circle transported by the actual surgery
boundary homeomorphism. -/
def compressionBoundaryPoint (F : LinkSpanningSurface.{0} E)
    {D : InteriorCompressingDisk F.embedding} (A : CompressionAnnulus D)
    (P : SmoothCompressionSurface A) (i : Fin n) (z : Circle) : P.surface :=
  (CompressionQuotientSupport.boundaryHomeomorph A P
    ⟨(F.boundaryCircle i).toFun z, (F.boundaryCircle i).lands_boundary z⟩).val

/-- A spanning surface is the boundary-bearing component of this actual embedded
surgery, with its original boundary labels. -/
def IsRetainedCompressionComponent (F : LinkSpanningSurface.{0} E)
    {D : InteriorCompressingDisk F.embedding} (A : CompressionAnnulus D)
    (P : SmoothCompressionSurface A) (J : ActualCompressionRealization E F A P)
    (b : P.surface) (G : LinkSpanningSurface.{0} E) : Prop :=
  ∃ e : G.surface ≃ₜ ↥(connectedComponent b),
    (∀ x : G.surface, x ∈ G.surface.boundary ↔
      (e x : P.surface) ∈ P.surface.boundary) ∧
    (∀ x : G.surface,
      G.embedding.toFun x = J.embedding.toFun (e x : P.surface)) ∧
    (∀ i z, (e ((G.boundaryCircle i).toFun z) : P.surface) =
      compressionBoundaryPoint E F A P i z)

/-- One genuine compression followed by retention of its boundary component. -/
def RetainedCompressionStep (G F : LinkSpanningSurface.{0} E) : Prop :=
  ConnectedSpace F.surface ∧
  ∃ (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D)
    (P : SmoothCompressionSurface A)
    (J : ActualCompressionRealization E F A P) (b : P.surface),
    (connectedComponent b ∩ P.surface.boundary).Nonempty ∧
    IsRetainedCompressionComponent E F A P J b G

/-- All conclusions about one actual compression. -/
def CompressionConclusion (F : LinkSpanningSurface.{0} E)
    {D : InteriorCompressingDisk F.embedding} (A : CompressionAnnulus D)
    (P : SmoothCompressionSurface A)
    (J : ActualCompressionRealization E F A P) : Prop :=
  boundaryCount P.surface = n ∧
  (∀ i z, J.embedding.toFun (compressionBoundaryPoint E F A P i z) =
    F.embedding.toFun ((F.boundaryCircle i).toFun z)) ∧
  (A.Separating →
    componentCount P.surface = 2 ∧
    (∃! k : ConnectedComponents P.surface,
      ∃ x : P.surface, x ∈ P.surface.boundary ∧ ConnectedComponents.mk x = k) ∧
    ∃ C B : SurgeryComponent P,
      Disjoint (connectedComponent C.point) (connectedComponent B.point) ∧
      connectedComponent C.point ∪ connectedComponent B.point = Set.univ ∧
      C.surface.boundary.Nonempty ∧
      B.surface.boundary = ∅ ∧
      (∀ x : P.surface, x ∈ P.surface.boundary →
        x ∈ connectedComponent C.point) ∧
      (∀ i z, compressionBoundaryPoint E F A P i z ∈ connectedComponent C.point) ∧
      boundaryCount C.surface = n ∧
      surfaceGenus C.surface < surfaceGenus F.surface ∧
      ∃ G : LinkSpanningSurface.{0} E,
        IsRetainedCompressionComponent E F A P J C.point G ∧
        ConnectedSpace G.surface ∧ boundaryCount G.surface = n ∧
        surfaceGenus G.surface < surfaceGenus F.surface) ∧
  (¬ A.Separating →
    ConnectedSpace P.surface ∧
    surfaceGenus P.surface + 1 = surfaceGenus F.surface ∧
    surfaceGenus P.surface < surfaceGenus F.surface ∧
    ∃ (b : P.surface) (G : LinkSpanningSurface.{0} E),
      IsRetainedCompressionComponent E F A P J b G ∧
      ConnectedSpace G.surface ∧ boundaryCount G.surface = n ∧
      surfaceGenus G.surface + 1 = surfaceGenus F.surface ∧
      surfaceGenus G.surface < surfaceGenus F.surface)


end SeifertSurfaces.OriginalEndpoints
