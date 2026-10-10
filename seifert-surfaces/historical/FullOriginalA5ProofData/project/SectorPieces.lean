import BoundaryFoliation
import Mathlib.Topology.PartialHomeomorph.Defs
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped Manifold ContDiff
open Set Topology MeasureTheory
namespace SeifertSurfaces.MetricFoundations
open Foundations
universe u v
noncomputable section

def sectorUnit (t : ℝ) : Euc 2 := !₂[Real.cos t, Real.sin t]
def planarSector (θ : ℝ) : Set (Euc 2) :=
  {x | ∃ (r : ℝ), r ≥ 0 ∧ ∃ t ∈ Icc (0 : ℝ) θ, x = r • sectorUnit t}
def sectorBoundary (θ : ℝ) : Set (Euc 2) :=
  {x | ∃ (r : ℝ), r ≥ 0 ∧ (x = r • sectorUnit 0 ∨ x = r • sectorUnit θ)}

/-- Interior charts use a disc; boundary/corner charts use a sector. Every
opening in (0,2pi), including reflex openings, is admitted. -/
structure SectorModel where
  interiorChart : Bool
  angle : ℝ
  angle_positive : 0 < angle
  angle_lt_two_pi : angle < 2 * Real.pi
  radius : ℝ
  radius_positive : 0 < radius

def SectorModel.domain (A : SectorModel) : Set (Euc 2) :=
  Metric.ball 0 A.radius ∩ if A.interiorChart then univ else planarSector A.angle
def SectorModel.boundary (A : SectorModel) : Set (Euc 2) :=
  A.domain ∩ if A.interiorChart then ∅ else sectorBoundary A.angle

/-- Sector charts are partial homeomorphisms onto actual planar regions.
Unlike a quadrant immersion, their target can have a reflex tangent cone. -/
structure SectorChart (P : Type u) [TopologicalSpace P] where
  map : PartialHomeomorph P (Euc 2)
  source_open : IsOpen map.source
  model : SectorModel
  target_eq : map.target = model.domain

structure CompactSectorPiece where
  carrier : Type u
  [topology : TopologicalSpace carrier]
  [compact : CompactSpace carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  boundary : Set carrier
  count : ℕ
  chart : Fin count → SectorChart carrier
  covers : (⋃ i, (chart i).map.source) = univ
  boundary_charts : ∀ i,
    (chart i).map '' (boundary ∩ (chart i).map.source) = (chart i).model.boundary
  transition_c1 : ∀ i j, ContDiffOn ℝ 1
    ((chart j).map ∘ (chart i).map.symm)
    ((chart i).map.target ∩ (chart i).map.symm ⁻¹' (chart j).map.source)
  transition_smooth_interior : ∀ i j, ContDiffOn ℝ ∞
    ((chart j).map ∘ (chart i).map.symm)
    (interior ((chart i).map.target) ∩ (chart i).map.symm ⁻¹' (chart j).map.source)
attribute [instance] CompactSectorPiece.topology CompactSectorPiece.compact
  CompactSectorPiece.hausdorff CompactSectorPiece.secondCountable
instance : CoeSort CompactSectorPiece (Type u) := ⟨CompactSectorPiece.carrier⟩
instance sectorMeasurable (P : CompactSectorPiece.{u}) : MeasurableSpace P := borel P
def CompactSectorPiece.interior (P : CompactSectorPiece.{u}) : Set P := P.boundaryᶜ

structure SectorChartPartition (P : CompactSectorPiece.{u}) where
  count : ℕ
  chartIndex : Fin count → Fin P.count
  piece : Fin count → Set P
  measurable : ∀ i, MeasurableSet (piece i)
  subordinate : ∀ i, piece i ⊆ (P.chart (chartIndex i)).map.source
  disjoint : Pairwise (fun i j => Disjoint (piece i) (piece j))
  covers : (⋃ i, piece i) = univ
theorem sectorChartPartition_exists (P : CompactSectorPiece.{u}) :
    Nonempty (SectorChartPartition P) := by
  classical
  letI : BorelSpace P := ⟨rfl⟩
  refine ⟨⟨P.count, id, disjointed (fun i => (P.chart i).map.source),
    ?_, ?_, disjoint_disjointed (fun i => (P.chart i).map.source), ?_⟩⟩
  · intro i
    rw [disjointed_eq_inter_compl]
    exact (P.chart i).source_open.measurableSet.inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        (P.chart j).source_open.measurableSet.compl)
  · intro i
    exact disjointed_subset (fun j => (P.chart j).map.source) i
  · simpa only [iUnion_disjointed] using P.covers
def canonicalSectorPartition (P : CompactSectorPiece.{u}) : SectorChartPartition P :=
  Classical.choice (sectorChartPartition_exists P)

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

def sectorCoordinateMap {P : CompactSectorPiece.{u}} (f : P → M) (j : Fin P.count) :
    Euc 2 → M := f ∘ (P.chart j).map.symm
def sectorCoordinateGram (g : SmoothMetric M) {P : CompactSectorPiece.{u}}
    (f : P → M) (j : Fin P.count) (y : Euc 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  let d := mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3)
    (sectorCoordinateMap f j) (P.chart j).map.target y
  fun k l => g.inner (sectorCoordinateMap f j y)
    (d ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single k 1)))
    (d ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single l 1)))
def sectorCoordinateDensity (g : SmoothMetric M) {P : CompactSectorPiece.{u}}
    (f : P → M) (j : Fin P.count) (y : Euc 2) : ℝ :=
  Real.sqrt (sectorCoordinateGram g f j y).det
def sectorPartitionArea (g : SmoothMetric M) {P : CompactSectorPiece.{u}}
    (f : P → M) (C : SectorChartPartition P) : ℝ :=
  ∑ i, ∫ y in (P.chart (C.chartIndex i)).map '' (C.piece i),
    sectorCoordinateDensity g f (C.chartIndex i) y
def sectorArea (g : SmoothMetric M) {P : CompactSectorPiece.{u}} (f : P → M) : ℝ :=
  sectorPartitionArea g f (canonicalSectorPartition P)

def sectorEdgeTangent {P : CompactSectorPiece.{u}} (f : P → M)
    (j : Fin P.count) (t : ℝ) : TangentSpace (𝓡∂ 3) (sectorCoordinateMap f j 0) :=
  mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) (sectorCoordinateMap f j)
    (P.chart j).map.target 0
    ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) (0 : Euc 2)).symm (sectorUnit t))

end
end SeifertSurfaces.MetricFoundations
