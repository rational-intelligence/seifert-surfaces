import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.PathConnected

/-!
# Source-facing smooth foundations for Seifert surfaces

The source is the original 48-page PDF, extracted to
`references/seifert-surfaces.txt`, Sections 1, 4.1 and 6.3.
All theorem bodies are formalization obligations, not verified proofs.
The definitions below have concrete topological and differential content.
-/

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations

universe u v
noncomputable section

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev ThreeSphere := ↥(Metric.sphere (0 : Euc 4) 1)
abbrev Time := Set.Icc (0 : ℝ) 1

/- A chosen smooth volume form records an orientation of a smooth manifold.
Smoothness is expressed in every extended chart, after pulling tangent vectors
back by the chart inverse; bare pointwise choices of orientations would not
express an orientation of the manifold. -/
structure SmoothVolumeOrientation {n : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (Euc n) H) (M : Type u)
    [TopologicalSpace M] [ChartedSpace H M] where
  form : ∀ x : M, TangentSpace I x [⋀^Fin n]→ₗ[ℝ] ℝ
  nowhere_zero : ∀ x, form x ≠ 0
  smooth_coefficients : ∀ p : M,
    ContDiffOn ℝ ∞
      (fun y : Euc n =>
        form ((extChartAt I p).symm y)
          (fun i => mfderivWithin 𝓘(ℝ, Euc n) I (extChartAt I p).symm
            (extChartAt I p).target y
            ((tangentSpaceCastModel 𝓘(ℝ, Euc n) y).symm
              (EuclideanSpace.single i 1))))
      (extChartAt I p).target

/- The inward normal coordinate of a tangent vector at a boundary point.
This is a chart expression, rather than a fictitious tangent space to the
boundary subtype, whose manifold structure still needs a separate bridge. -/
def inwardCoordinate {n : ℕ} [NeZero n] {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    (x : M) (w : TangentSpace (𝓡∂ n) x) : ℝ :=
  (tangentSpaceCastModel 𝓘(ℝ, Euc n) ((extChartAt (𝓡∂ n) x) x)
    (mfderiv (𝓡∂ n) 𝓘(ℝ, Euc n) (extChartAt (𝓡∂ n) x) x w)) 0

/- An actual compact smooth surface with boundary, without a connectedness
assumption.  A link spanning surface is allowed to be disconnected. -/
structure CompactOrientedSurface where
  carrier : Type u
  [topology : TopologicalSpace carrier]
  [charted : ChartedSpace (EuclideanHalfSpace 2) carrier]
  [smooth : IsManifold (𝓡∂ 2) ∞ carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  [compact : CompactSpace carrier]
  orientation : SmoothVolumeOrientation (𝓡∂ 2) carrier

attribute [instance] CompactOrientedSurface.topology CompactOrientedSurface.charted
  CompactOrientedSurface.smooth CompactOrientedSurface.hausdorff
  CompactOrientedSurface.secondCountable CompactOrientedSurface.compact

instance : CoeSort CompactOrientedSurface (Type u) := ⟨CompactOrientedSurface.carrier⟩

namespace CompactOrientedSurface

def boundary (S : CompactOrientedSurface.{u}) : Set S := (𝓡∂ 2).boundary S

/- Every connected component meets the boundary.  In particular a sphere or
other closed component cannot be adjoined to a link spanning surface. -/
def NoClosedComponents (S : CompactOrientedSurface.{u}) : Prop :=
  ∀ x : S, ∃ y ∈ S.boundary, y ∈ connectedComponent x

/- A parametrized boundary circle in the induced boundary orientation.
The outward-first convention is encoded by a negative inward coordinate and
a positive evaluation of the surface orientation form. -/
structure OrientedBoundaryCircle (S : CompactOrientedSurface.{u}) where
  toFun : Circle → S
  smoothEmbedding : Manifold.IsSmoothEmbedding (𝓡 1) (𝓡∂ 2) ∞ toFun
  lands_boundary : ∀ z, toFun z ∈ S.boundary
  positive : ∀ t : ℝ,
    let x := toFun (Circle.exp t)
    let w := mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 2) (fun r => toFun (Circle.exp r)) t
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1)
    ∃ outward : TangentSpace (𝓡∂ 2) x,
      inwardCoordinate x outward < 0 ∧
      0 < S.orientation.form x ![outward, w]

end CompactOrientedSurface

/- Actual neat embedding data: smooth immersion and topological embedding,
exact boundary preimage, and transversality to the ambient boundary. -/
structure NeatEmbedding (S : CompactOrientedSurface.{u}) (M : Type v)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] where
  toFun : S → M
  smoothEmbedding : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ toFun
  boundary_preimage : toFun ⁻¹' ((𝓡∂ 3).boundary M) = S.boundary
  boundary_transverse : ∀ x ∈ S.boundary,
    ∃ w : TangentSpace (𝓡∂ 2) x,
      inwardCoordinate (toFun x) (mfderiv (𝓡∂ 2) (𝓡∂ 3) toFun x w) ≠ 0

namespace NeatEmbedding

variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]

def image (f : NeatEmbedding S M) : Set M := Set.range f.toFun

def continuousMap (f : NeatEmbedding S M) : C(S, M) :=
  ⟨f.toFun, f.smoothEmbedding.isEmbedding.continuous⟩

/- Incompressibility in the source introduction is actual injectivity of the
inclusion-induced homomorphism on fundamental groups, at every basepoint.
This expresses componentwise incompressibility when `S` is disconnected. -/
def Incompressible (f : NeatEmbedding S M) : Prop :=
  ∀ x : S, Function.Injective (FundamentalGroup.map f.continuousMap x)

theorem image_isCompact (f : NeatEmbedding S M) : IsCompact f.image := by
  exact isCompact_range f.smoothEmbedding.isEmbedding.continuous

theorem image_inter_boundary (f : NeatEmbedding S M) :
    f.image ∩ (𝓡∂ 3).boundary M = f.toFun '' S.boundary := by
  ext y
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, by rwa [← f.boundary_preimage], rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, by rwa [← f.boundary_preimage] at hx⟩

end NeatEmbedding

/- A finite nonempty smooth oriented link in the actual standard 3-sphere.
Each component has the standard orientation from `Circle.exp`; orientations
can be reversed by changing the parametrization. -/
structure OrientedLink (n : ℕ) where
  nonempty : 0 < n
  component : Fin n → Circle → ThreeSphere
  smoothEmbedding : ∀ i,
    Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 3) ∞ (component i)
  disjoint : Pairwise (fun i j => Disjoint (Set.range (component i))
    (Set.range (component j)))

abbrev OrientedKnot := OrientedLink 1

/- A smooth family of ambient diffeomorphisms of a manifold with boundary,
starting at the identity and preserving the boundary setwise. The parameter
domain is the closed interval with its 1-dimensional half-space smooth model.
The product therefore uses a genuine corner model, not a boundaryless model. -/
structure SmoothAmbientIsotopy (M : Type v)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] where
  stage : Time → Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞
  smooth_family : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
    (fun p : Time × M => stage p.1 p.2)
  initial : ∀ x, stage 0 x = x
  boundary_setwise : ∀ t, (stage t) '' ((𝓡∂ 3).boundary M) = (𝓡∂ 3).boundary M

namespace SmoothAmbientIsotopy

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

def Rel (A B : Set M) : Prop :=
  ∃ H : SmoothAmbientIsotopy M, (H.stage 1) '' A = B

theorem rel_refl : ∀ A : Set M, Rel A A := by
  intro A
  refine ⟨{
    stage := fun _ => Diffeomorph.refl (𝓡∂ 3) M ∞
    smooth_family := contMDiff_snd
    initial := fun _ => rfl
    boundary_setwise := fun _ => Set.image_id _ }, ?_⟩
  exact Set.image_id _

theorem rel_symm : ∀ A B : Set M, Rel A B → Rel B A := by
  rintro A B ⟨H, hH⟩
  let rev : Time → Time := fun t => ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
  have hrev : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ rev := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨(continuous_const.sub continuous_subtype_val).subtype_mk _, ?_⟩
    exact contMDiff_const.sub contMDiff_subtypeVal_Icc
  have rev_zero : rev 0 = 1 := by apply Subtype.ext; norm_num [rev]
  have rev_one : rev 1 = 0 := by apply Subtype.ext; norm_num [rev]
  refine ⟨{
    stage := fun t => (H.stage (rev t)).trans (H.stage 1).symm
    smooth_family := (H.stage 1).symm.contMDiff.comp (H.smooth_family.comp
      ((hrev.comp contMDiff_fst).prodMk contMDiff_snd))
    initial := by
      intro x
      change (H.stage 1).symm (H.stage (rev 0) x) = x
      rw [rev_zero, Diffeomorph.symm_apply_apply]
    boundary_setwise := by
      intro t
      change (fun x => (H.stage 1).symm (H.stage (rev t) x)) '' _ = _
      rw [← Set.image_image, H.boundary_setwise]
      exact (congrArg (fun s => (H.stage 1).symm '' s)
        (H.boundary_setwise 1)).symm.trans
        ((H.stage 1).toEquiv.symm_image_image _) }, ?_⟩
  change (fun x => (H.stage 1).symm (H.stage (rev 1) x)) '' B = A
  simp only [rev_one, H.initial]
  rw [← hH]
  exact (H.stage 1).toEquiv.symm_image_image A

theorem rel_trans : ∀ A B C : Set M, Rel A B → Rel B C → Rel A C := by
  rintro A B C ⟨H, hH⟩ ⟨K, hK⟩
  refine ⟨{
    stage := fun t => (H.stage t).trans (K.stage t)
    smooth_family := K.smooth_family.comp
      (contMDiff_fst.prodMk H.smooth_family)
    initial := by
      intro x
      change K.stage 0 (H.stage 0 x) = x
      rw [H.initial, K.initial]
    boundary_setwise := by
      intro t
      change (fun x => K.stage t (H.stage t x)) '' _ = _
      rw [← Set.image_image, H.boundary_setwise, K.boundary_setwise] }, ?_⟩
  change (fun x => K.stage 1 (H.stage 1 x)) '' A = C
  rw [← Set.image_image, hH, hK]

end SmoothAmbientIsotopy

/- The topological ambient category is kept separate for genuinely cornered
surface images. This structure asserts homeomorphisms and continuity, never
smooth diffeomorphisms or smooth corner-rounding equivalence. -/
structure TopologicalAmbientIsotopy (M : Type v)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] where
  stage : Time → M ≃ₜ M
  continuous_family : Continuous (fun p : Time × M => stage p.1 p.2)
  initial : ∀ x, stage 0 x = x
  boundary_setwise : ∀ t, (stage t) '' ((𝓡∂ 3).boundary M) = (𝓡∂ 3).boundary M

namespace SmoothAmbientIsotopy

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/- Canonical forgetting of smoothness; no reverse category bridge is assumed. -/
def toTopological (H : SmoothAmbientIsotopy M) : TopologicalAmbientIsotopy M where
  stage t := (H.stage t).toHomeomorph
  continuous_family := H.smooth_family.continuous
  initial := H.initial
  boundary_setwise := H.boundary_setwise

/- Joint smoothness of the inverse family is needed by symmetry of the
smooth ambient relation; it is an explicit parameterized inverse theorem debt. -/

end SmoothAmbientIsotopy

/- Actual π₁ injectivity is invariant under postcomposition by a smooth
ambient diffeomorphism. This is the algebraic invariant needed by transport. -/
theorem incompressible_postcompose_diffeomorph
    {S : CompactOrientedSurface.{u}} {M : Type v}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (f : NeatEmbedding S M) (e : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞) :
    (∀ x : S, Function.Injective (FundamentalGroup.map
      (⟨e ∘ f.toFun, e.toHomeomorph.continuous.comp
        f.smoothEmbedding.isEmbedding.continuous⟩ : C(S, M)) x)) ↔
      f.Incompressible := by
  let E : C(M, M) := ⟨e, e.toHomeomorph.continuous⟩
  let I : C(M, M) := ⟨e.symm, e.symm.toHomeomorph.continuous⟩
  have hE : ∀ b : M, Function.Injective (FundamentalGroup.map E b) := by
    intro b
    let inverse : FundamentalGroup M (E b) → FundamentalGroup M b := fun p =>
      (Path.Homotopic.Quotient.map p I).cast
        (e.symm_apply_apply b).symm (e.symm_apply_apply b).symm
    have hi : Function.LeftInverse inverse (FundamentalGroup.map E b) := by
      intro p
      change inverse (Path.Homotopic.Quotient.map p E) = p
      refine Quotient.inductionOn p ?_
      intro p
      change Path.Homotopic.Quotient.mk
        (((p.map E.continuous).map I.continuous).cast
          (e.symm_apply_apply b).symm (e.symm_apply_apply b).symm) =
        Path.Homotopic.Quotient.mk p
      congr 1
      ext t
      exact e.symm_apply_apply (p t)
    exact hi.injective
  have hcomp : ∀ x : S, ∀ p : FundamentalGroup S x,
      FundamentalGroup.map (E.comp f.continuousMap) x p =
        FundamentalGroup.map E (f.toFun x) (FundamentalGroup.map f.continuousMap x p) := by
    intro x p
    exact Path.Homotopic.Quotient.map_comp
  change (∀ x : S, Function.Injective (FundamentalGroup.map (E.comp f.continuousMap) x)) ↔ _
  constructor
  · intro h x p q hpq
    apply h x
    rw [hcomp, hcomp, hpq]
  · intro h x p q hpq
    apply h x
    apply hE (f.toFun x)
    rwa [← hcomp, ← hcomp]

/- Normal isotopy keeps the source surface fixed and every stage neat.
Boundary points may move in the ambient boundary. -/
structure SmoothNormalIsotopy (S : CompactOrientedSurface.{u}) (M : Type v)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (f g : NeatEmbedding S M) where
  stage : Time → NeatEmbedding S M
  smooth_family : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 2)) (𝓡∂ 3) ∞
    (fun p : Time × S => (stage p.1).toFun p.2)
  initial : (stage 0).toFun = f.toFun
  final : (stage 1).toFun = g.toFun

/- Compact neat isotopy extension is a named geometric obligation, not a
silently interchangeable homotopy relation. -/

end
end SeifertSurfaces.Foundations
