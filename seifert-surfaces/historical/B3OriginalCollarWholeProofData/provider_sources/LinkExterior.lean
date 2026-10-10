import Foundations
import Mathlib.Topology.Homotopy.Basic

/-!
# Actual link exteriors and oriented spanning surfaces

The boundary of an oriented link spanning surface consists of one oriented
curve on each tube torus. Each curve has positive core degree one; its meridian
coefficient is forced by the existence of the oriented spanning surface, not
set equal to zero independently on every component. Establishing the precise
surface-framed linking formula (26) is an outstanding homological bridge.
-/

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations

universe u
noncomputable section

def tubeDiskOpen : TopologicalSpace.Opens (Euc 2) :=
  ⟨Metric.ball (0 : Euc 2) 2, Metric.isOpen_ball⟩

abbrev TubeDisk := ↥tubeDiskOpen
abbrev TubeDomain := Circle × TubeDisk

/- A framed smooth tubular neighborhood. The radius-two chart supplies an
actual extension past the radius-one torus used to form the exterior. -/
structure TubularNeighborhood {n : ℕ} (L : OrientedLink n) where
  tube : Fin n → TubeDomain → ThreeSphere
  smoothEmbedding : ∀ i, Manifold.IsSmoothEmbedding
    ((𝓡 1).prod 𝓘(ℝ, Euc 2)) (𝓡 3) ∞ (tube i)
  core : ∀ i z, tube i (z, ⟨0, Metric.mem_ball_self zero_lt_two⟩) = L.component i z
  image_open : ∀ i, IsOpen (Set.range (tube i))
  disjoint : Pairwise (fun i j => Disjoint (Set.range (tube i)) (Set.range (tube j)))

namespace TubularNeighborhood

variable {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L)

def openTube (i : Fin n) : Set ThreeSphere :=
  T.tube i '' {p : TubeDomain | ‖(p.2 : Euc 2)‖ < 1}

def shell (i : Fin n) : Set ThreeSphere :=
  T.tube i '' {p : TubeDomain | ‖(p.2 : Euc 2)‖ = 1}

/- The literal exterior subset of the standard three-sphere. -/
def exteriorSet : Set ThreeSphere := (⋃ i, T.openTube i)ᶜ

abbrev Carrier := ↥T.exteriorSet

theorem exterior_isCompact : IsCompact T.exteriorSet := by
  apply IsClosed.isCompact
  apply IsOpen.isClosed_compl
  apply isOpen_iUnion
  intro i
  apply T.smoothEmbedding i |>.isEmbedding.isInducing.isOpenMap (T.image_open i)
  exact isOpen_lt (continuous_norm.comp continuous_snd.subtype_val) continuous_const

theorem shells_in_exterior (i : Fin n) : T.shell i ⊆ T.exteriorSet := by
  rintro x ⟨p, hp, rfl⟩ hx
  obtain ⟨j, q, hq, heq⟩ := Set.mem_iUnion.mp hx
  by_cases hij : i = j
  · subst j
    have hqp := (T.smoothEmbedding i).isEmbedding.injective heq
    have := hqp ▸ hq
    exact (lt_irrefl (1 : ℝ)) (hp ▸ this)
  · have hd := T.disjoint hij
    exact Set.disjoint_left.mp hd ⟨p, rfl⟩ ⟨q, heq⟩

end TubularNeighborhood

/- Smooth boundary structure on the actual complement of the open tubes.
Existence is a separate theorem obligation, rather than an assumed consequence
of a freely chosen manifold or an arbitrary boundary predicate. -/
structure SmoothExterior {n : ℕ} {L : OrientedLink n} (T : TubularNeighborhood L) where
  [charted : ChartedSpace (EuclideanHalfSpace 3) T.Carrier]
  [smooth : IsManifold (𝓡∂ 3) ∞ T.Carrier]
  [compact : CompactSpace T.Carrier]
  [secondCountable : SecondCountableTopology T.Carrier]
  inclusion : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞
    (Subtype.val : T.Carrier → ThreeSphere)
  boundary_image : (Subtype.val : T.Carrier → ThreeSphere) ''
    ((𝓡∂ 3).boundary T.Carrier) = ⋃ i, T.shell i


namespace SmoothExterior

variable {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}

/- Type synonym tagging the chosen smooth structure on the literal exterior.
Its underlying points and topology are those of `T.Carrier`. -/
def Carrier (_E : SmoothExterior T) : Type := T.Carrier

instance (E : SmoothExterior T) : TopologicalSpace E.Carrier :=
  inferInstanceAs (TopologicalSpace T.Carrier)

instance (E : SmoothExterior T) : ChartedSpace (EuclideanHalfSpace 3) E.Carrier := E.charted
instance (E : SmoothExterior T) : IsManifold (𝓡∂ 3) ∞ E.Carrier := E.smooth
instance (E : SmoothExterior T) : CompactSpace E.Carrier := E.compact
instance (E : SmoothExterior T) : SecondCountableTopology E.Carrier := E.secondCountable
instance (E : SmoothExterior T) : T2Space E.Carrier := inferInstanceAs (T2Space T.Carrier)

def toSphere (E : SmoothExterior T) : E.Carrier → ThreeSphere := Subtype.val

/- The i-th boundary torus is the actual radius-one tube shell. -/
def boundaryTorus (E : SmoothExterior T) (i : Fin n) : Set E.Carrier :=
  {x | E.toSphere x ∈ T.shell i}


end SmoothExterior

/- An oriented spanning surface for an n-component link, with no closed
component, one oriented boundary circle on each torus, and positive longitudinal
core degree one.  Connectedness is not part of the general link definition. -/
structure LinkSpanningSurface {n : ℕ} {L : OrientedLink n}
    {T : TubularNeighborhood L} (E : SmoothExterior T) where
  surface : CompactOrientedSurface.{u}
  embedding : NeatEmbedding surface E.Carrier
  no_closed_components : surface.NoClosedComponents
  boundaryCircle : Fin n → surface.OrientedBoundaryCircle
  boundary_covers : (⋃ i, Set.range (boundaryCircle i).toFun) = surface.boundary
  boundary_disjoint : Pairwise (fun i j => Disjoint
    (Set.range (boundaryCircle i).toFun) (Set.range (boundaryCircle j).toFun))
  coordinates : Fin n → C(Circle, TubeDomain)
  on_shell : ∀ i z, ‖((coordinates i z).2 : Euc 2)‖ = 1
  boundary_tube : ∀ i z,
    E.toSphere (embedding.toFun ((boundaryCircle i).toFun z)) =
      T.tube i (coordinates i z)
  longitudinal_degree_one : ∀ i,
    ContinuousMap.Homotopic
      (⟨fun z => (coordinates i z).1,
        continuous_fst.comp (coordinates i).continuous⟩ : C(Circle, Circle))
      (ContinuousMap.id Circle)

namespace LinkSpanningSurface

variable {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
  {E : SmoothExterior T}

def image (F : LinkSpanningSurface.{u} E) : Set E.Carrier := F.embedding.image

def Incompressible (F : LinkSpanningSurface.{u} E) : Prop :=
  F.embedding.Incompressible

theorem boundary_on_torus (F : LinkSpanningSurface.{u} E) (i : Fin n) :
    Set.range (fun z => F.embedding.toFun ((F.boundaryCircle i).toFun z)) ⊆
      E.boundaryTorus i := by
  rintro x ⟨z, rfl⟩
  change E.toSphere (F.embedding.toFun ((F.boundaryCircle i).toFun z)) ∈ T.shell i
  rw [F.boundary_tube i z]
  exact ⟨F.coordinates i z, F.on_shell i z, rfl⟩

/- For a knot, the one boundary circle and no-closed-component condition force
connectedness; this is not inserted as an axiom for general link surfaces. -/
theorem connected_for_knot {K : OrientedKnot} {T : TubularNeighborhood K}
    {E : SmoothExterior T} (F : LinkSpanningSurface.{u} E) :
    ConnectedSpace F.surface := by
  classical
  let b : Circle → F.surface := (F.boundaryCircle 0).toFun
  have hb : Continuous b := (F.boundaryCircle 0).smoothEmbedding.isEmbedding.continuous
  have hboundary : F.surface.boundary = Set.range b := by
    rw [← F.boundary_covers]
    ext x
    simp [b]
  let z : Circle := 1
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨b z, Set.eq_univ_of_forall ?_⟩
  intro x
  obtain ⟨y, hy, hycomp⟩ := F.no_closed_components x
  have hsub : Set.range b ⊆ connectedComponent (b z) :=
    (isPreconnected_range hb).subset_connectedComponent ⟨z, rfl⟩
  have hyb : y ∈ connectedComponent (b z) := hsub (hboundary ▸ hy)
  rw [connectedComponent_eq hyb, ← connectedComponent_eq hycomp]
  exact mem_connectedComponent

end LinkSpanningSurface

/- Definition 4.1's surface object, before incompressibility and quotienting.
The knot is fixed, the oriented boundary is a single longitudinal circle, and
the embedding is genuinely neat. -/
structure SeifertSurface {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) extends LinkSpanningSurface.{u} E where
  [connected : ConnectedSpace surface]

attribute [instance] SeifertSurface.connected

end
end SeifertSurfaces.Foundations
