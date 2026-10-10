import GeometricCategory
import MetricAreaAnalysis.SameImage

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle
namespace SeifertSurfaces.MetricFoundations.AreaCertificates
open Foundations AreaAnalysis
universe u v
noncomputable section

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- Literal common-range homeomorphism of the supplied geometric pair. -/
def geometricSameImageHomeomorph {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (heq : F.image = G.image) : R ≃ₜ S :=
  G.embedding.toHomeomorph.trans
    ((Homeomorph.setCongr heq.symm).trans F.embedding.toHomeomorph.symm)

def imageInteriorCoordinateDomain {S R : CompactOrientedSurface.{u}}
    {f : S → M} {g : R → M} (a : R ≃ₜ S)
    (cF : SmoothImageChart S f) (cG : SmoothImageChart R g) :
    Set (EuclideanHalfSpace 2) :=
  cG.chart.target ∩ cG.chart.symm ⁻¹' (R.boundaryᶜ ∩ a ⁻¹' cF.chart.source)

def imageCoordinateTransition {S R : CompactOrientedSurface.{u}}
    {f : S → M} {g : R → M} (a : R ≃ₜ S)
    (cF : SmoothImageChart S f) (cG : SmoothImageChart R g) :
    EuclideanHalfSpace 2 → EuclideanHalfSpace 2 := cF.chart ∘ a ∘ cG.chart.symm

def imageChartEuclideanTarget {S : CompactOrientedSurface.{u}}
    {f : S → M} (c : SmoothImageChart S f) : Set (Euc 2) :=
  (𝓡∂ 2) '' c.chart.target

def imageChartAmbientCoordinates {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (c : SmoothImageChart S F.map)
    (y₀ : EuclideanHalfSpace 2) : Euc 2 → Euc 3 :=
  extChartAt (𝓡∂ 3) (F.map (c.chart.symm y₀)) ∘ F.map ∘ c.chart.symm ∘ (𝓡∂ 2).symm

/-- Actual Euclidean immersion inverse data at an interior image-chart point. -/
structure SmoothImageLocalInverse {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (c : SmoothImageChart S F.map)
    (y₀ : EuclideanHalfSpace 2) where
  domain : Set (Euc 2)
  domain_open : IsOpen domain
  base_mem : (𝓡∂ 2) y₀ ∈ domain
  domain_subset : domain ⊆ interior (imageChartEuclideanTarget c)
  ambient_mem : MapsTo (F.map ∘ c.chart.symm ∘ (𝓡∂ 2).symm) domain
    ((extChartAt (𝓡∂ 3) (F.map (c.chart.symm y₀))).source ∩
      ((𝓡∂ 3).boundary M)ᶜ)
  chart_smooth : ContDiffOn ℝ ∞ (imageChartAmbientCoordinates F c y₀) domain
  derivative_injective : Function.Injective
    (fderiv ℝ (imageChartAmbientCoordinates F c y₀) ((𝓡∂ 2) y₀))
  inverse : EuclideanLocalLeftInverse (imageChartAmbientCoordinates F c y₀)
    ((𝓡∂ 2) y₀) domain

def seamVertexSet {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M) : Set S :=
  ⋃ k, {F.seam.arc k 0, F.seam.arc k 1}

def seamArcInteriorSet {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (k : Fin F.seam.arcCount) : Set S :=
  F.seam.arc k '' {t : Time | 0 < (t : ℝ) ∧ (t : ℝ) < 1}

def oppositePieceSourceSet {S R : CompactOrientedSurface.{u}}
    (G : GeometricPiecewiseSurface R M) (a : R ≃ₜ S) (E : Set S)
    (i : Fin G.pieceCount) (j : Fin (G.domain i).count) : Set (G.domain i) :=
  (G.domain i).interior ∩ (G.parametrization i) ⁻¹' (a ⁻¹' E) ∩
    ((G.domain i).chart j).map.source

def oppositePieceCoordinates {S R : CompactOrientedSurface.{u}}
    (G : GeometricPiecewiseSurface R M) (a : R ≃ₜ S) (E : Set S)
    (i : Fin G.pieceCount) (j : Fin (G.domain i).count) : Set (Euc 2) :=
  ((G.domain i).chart j).map '' oppositePieceSourceSet G a E i j

def pieceBoundaryCoordinates {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) : Set (Euc 2) :=
  ((F.domain i).chart j).map '' ((F.domain i).boundary ∩ ((F.domain i).chart j).map.source)

def sectorToSourceDomain {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) : Set (Euc 2) :=
  interior ((F.domain i).chart j).map.target ∩
    ((F.domain i).chart j).map.symm ⁻¹' ((F.parametrization i) ⁻¹' (surfaceChart p).source)

def sectorToSourceCoordinates {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) : Euc 2 → Euc 2 :=
  surfaceChart p ∘ F.parametrization i ∘ ((F.domain i).chart j).map.symm

def sectorToSourceDerivative {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) (y : Euc 2) : Euc 2 →L[ℝ] Euc 2 :=
  fderivWithin ℝ (sectorToSourceCoordinates F i j p) (sectorToSourceDomain F i j p) y

/-- Actual inverse through the supplied parametrization's range homeomorphism.
The value outside that range is a totalization and is outside the partial target. -/
def sourceToSectorCoordinates {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) (y : Euc 2) : Euc 2 := by
  classical
  exact if hy : (surfaceChart p).symm y ∈ Set.range (F.parametrization i) then
    ((F.domain i).chart j).map
      ((F.parametrization_embedding i).toHomeomorph.symm ⟨(surfaceChart p).symm y, hy⟩)
  else 0

def pieceAmbientCoordinateDifferential {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (y : Euc 2) :
    Euc 2 →ₗ[ℝ] TangentSpace (𝓡∂ 3) (sectorCoordinateMap (F.map ∘ F.parametrization i) j y) :=
  (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3)
    (sectorCoordinateMap (F.map ∘ F.parametrization i) j)
    ((F.domain i).chart j).map.target y).toLinearMap.comp
      (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm.toLinearMap

end
end SeifertSurfaces.MetricFoundations.AreaCertificates
