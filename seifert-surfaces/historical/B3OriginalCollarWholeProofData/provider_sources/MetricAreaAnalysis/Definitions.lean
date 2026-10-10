import AreaHelpers
import Mathlib

open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle

noncomputable section
namespace SeifertSurfaces.MetricFoundations.AreaAnalysis
open Foundations
universe u v

abbrev surfaceChart {S : CompactOrientedSurface.{u}} (p : S) := extChartAt (𝓡∂ 2) p

/-- Full relatively open overlap, independent of every measurable partition piece. -/
def chartOverlap {S : CompactOrientedSurface.{u}} (p q : S) : Set (Euc 2) :=
  (surfaceChart p).target ∩ (surfaceChart p).symm ⁻¹' (surfaceChart q).source

def chartTransition {S : CompactOrientedSurface.{u}} (p q : S) : Euc 2 → Euc 2 :=
  surfaceChart q ∘ (surfaceChart p).symm

def chartTransitionDerivative {S : CompactOrientedSurface.{u}} (p q : S)
    (y : Euc 2) : Euc 2 →L[ℝ] Euc 2 :=
  fderivWithin ℝ (chartTransition p q) (chartOverlap p q) y

/-- A finite cover with compact chart-subordinate enlargement of each open member. -/
structure CompactChartCover (S : CompactOrientedSurface.{u}) where
  count : ℕ
  center : Fin count → S
  openSet : Fin count → Set S
  compactSet : Fin count → Set S
  isOpen : ∀ k, IsOpen (openSet k)
  open_subset : ∀ k, openSet k ⊆ compactSet k
  isCompact : ∀ k, IsCompact (compactSet k)
  subordinate : ∀ k, compactSet k ⊆ (surfaceChart (center k)).source
  covers : (⋃ k, openSet k) = univ

def compactCoverPiece {S : CompactOrientedSurface.{u}} (C : CompactChartCover S)
    (k : Fin C.count) : Set S := disjointed C.openSet k

def commonPiece {S : CompactOrientedSurface.{u}} (P Q : ChartPartition S)
    (i : Fin P.count) (j : Fin Q.count) : Set S := P.piece i ∩ Q.piece j

def interiorCoordinateDomain {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (r : R) (p : S) : Set (Euc 2) :=
  (surfaceChart r).target ∩ (surfaceChart r).symm ⁻¹'
    ((R.boundary)ᶜ ∩ a ⁻¹' (surfaceChart p).source)

def interiorCoordinateMap {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (r : R) (p : S) : Euc 2 → Euc 2 := surfaceChart p ∘ a ∘ (surfaceChart r).symm

def interiorCoordinateDerivative {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (r : R) (p : S) (y : Euc 2) : Euc 2 →L[ℝ] Euc 2 :=
  fderiv ℝ (interiorCoordinateMap a r p) y

def mixedInteriorPiece {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (P : ChartPartition R) (Q : ChartPartition S)
    (i : Fin P.count) (j : Fin Q.count) : Set R :=
  P.piece i ∩ a ⁻¹' Q.piece j ∩ (R.boundary)ᶜ

/-- A smooth left inverse of a Euclidean immersion, without an ambient right inverse. -/
structure EuclideanLocalLeftInverse (F : Euc 2 → Euc 3) (x : Euc 2)
    (D : Set (Euc 2)) where
  source : Set (Euc 2)
  target : Set (Euc 3)
  map : Euc 3 → Euc 2
  open_source : IsOpen source
  source_mem : x ∈ source
  source_subset : source ⊆ D
  open_target : IsOpen target
  target_mem : F x ∈ target
  smooth : ContDiffOn ℝ ∞ map target
  mapsTo : MapsTo F source target
  left_inverse : ∀ z ∈ source, map (F z) = z

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- Literal approved within-chart differential, with the Euclidean tangent cast. -/
def coordinateDifferential {S : CompactOrientedSurface.{u}} (F : S → M)
    (p : S) (y : Euc 2) :
    Euc 2 →ₗ[ℝ] TangentSpace (𝓡∂ 3) (F ((surfaceChart p).symm y)) :=
  (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) (F ∘ (surfaceChart p).symm)
    (surfaceChart p).target y).toLinearMap.comp
      (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm.toLinearMap

def tangentTransport {x y : M} (h : x = y) (w : TangentSpace (𝓡∂ 3) x) :
    TangentSpace (𝓡∂ 3) y := h ▸ w

def coordinateIntegral (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F : S → M) (p : S) (s : Set S) : ℝ :=
  ∫ y in (surfaceChart p) '' s, coordinateAreaDensity g F p y

/-- The common-image homeomorphism is built from the two actual range homeomorphisms. -/
def sameImageHomeomorph {S R : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (h : ProperSmoothEmbedding R M)
    (heq : f.image = h.image) : R ≃ₜ S :=
  h.embedding.toHomeomorph.trans
    ((Homeomorph.setCongr heq.symm).trans f.embedding.toHomeomorph.symm)

def embeddingCoordinateMap {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (x : S) : Euc 2 → Euc 3 :=
  extChartAt (𝓡∂ 3) (f.toFun x) ∘ f.toFun ∘ (surfaceChart x).symm

/-- Concrete interior chart data and its Euclidean local left inverse. -/
structure EmbeddingInteriorLocalInverse {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (x : S) where
  domain : Set (Euc 2)
  open_domain : IsOpen domain
  base_mem : surfaceChart x x ∈ domain
  domain_subset : domain ⊆ interior (surfaceChart x).target
  ambient_mem : MapsTo (f.toFun ∘ (surfaceChart x).symm) domain
    ((extChartAt (𝓡∂ 3) (f.toFun x)).source ∩ ((𝓡∂ 3).boundary M)ᶜ)
  chart_smooth : ContDiffOn ℝ ∞ (embeddingCoordinateMap f x) domain
  derivative_injective : Function.Injective
    (fderiv ℝ (embeddingCoordinateMap f x) (surfaceChart x x))
  inverse : EuclideanLocalLeftInverse (embeddingCoordinateMap f x) (surfaceChart x x) domain

end SeifertSurfaces.MetricFoundations.AreaAnalysis
