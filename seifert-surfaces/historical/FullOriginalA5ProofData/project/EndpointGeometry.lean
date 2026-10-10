import AppendixACoordinates
import AppendixASupport
import C2Analytic
import Foundations

noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.AppendixC

universe u v
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]

/-- A genuine smooth coordinate chart in the two-sided ambient extension. -/
structure SmoothAmbientChart (N : Type u) [TopologicalSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] where
  chart : OpenPartialHomeomorph N E3
  smooth : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ chart chart.source
  inverse_smooth : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ chart.symm chart.target

def chartDifferential (c : SmoothAmbientChart N) (p : N) :
    TangentSpace 𝓘(ℝ, E3) p →L[ℝ] E3 :=
  (NormedSpace.fromTangentSpace (c.chart p)).toContinuousLinearMap.comp
    (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart p)

def inverseChartDifferential (c : SmoothAmbientChart N) (y : E3) :
    E3 →L[ℝ] TangentSpace 𝓘(ℝ, E3) (c.chart.symm y) :=
  (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y).comp
    (NormedSpace.fromTangentSpace y).symm.toContinuousLinearMap

/-- The supplied Riemannian metric itself, pulled into the supplied chart.
There is no unrelated coordinate-metric witness. -/
def actualChartTensor (h : AmbientMetric N) (c : SmoothAmbientChart N) : MetricTensor :=
  fun y i j => h.inner (c.chart.symm y)
    (inverseChartDifferential c y (coordinateVector 3 i))
    (inverseChartDifferential c y (coordinateVector 3 j))

/-- Minimality of an actual immersion. In each actual ambient chart the
normal component of the metric trace of its covariant acceleration vanishes.
The explicit immersion condition excludes singular or constant parametrizations. -/
def IsMinimalPatch (h : AmbientMetric N) (Φ : E2 → N) (D : Set E2) : Prop :=
  ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E3) ∞ Φ D ∧
  (∀ x ∈ D, Function.Injective (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) Φ x)) ∧
  ∀ c : SmoothAmbientChart N,
    IsMinimalParametrizationOn (actualChartTensor h c) (c.chart ∘ Φ)
      (D ∩ Φ ⁻¹' c.chart.source)

def levelCoordinates (y : E3) : E2 :=
  y 1 • coordinateVector 2 0 + y 2 • coordinateVector 2 1

def levelVector (v : E3) : E2 := levelCoordinates v

def levelInclusion : E2 →L[ℝ] E3 :=
  (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)).smulRight (coordinateVector 3 1) +
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)).smulRight (coordinateVector 3 2)

/-- The local collar of (2), as an actual chart of the ambient extension,
with exact region/boundary identification and the actual warped metric.
No Hessian inequality is assumed; it is a derived geometry obligation. -/
structure WarpedBoundaryCollar (h : AmbientMetric N) (M : Set N) where
  coordinates : SmoothAmbientChart N
  radial : N → ℝ
  radial_smooth : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ) ∞ radial coordinates.chart.source
  radial_coordinate : ∀ p ∈ coordinates.chart.source, radial p = coordinates.chart p 0
  region_identification : ∀ p ∈ coordinates.chart.source, p ∈ M ↔ 0 ≤ radial p
  boundary_identification : ∀ p ∈ coordinates.chart.source,
    p ∈ frontier M ↔ radial p = 0
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  target_radial_range : ∀ y ∈ coordinates.chart.target, |y 0| < epsilon
  phi : ℝ → ℝ
  phi_smooth : ContDiff ℝ ∞ phi
  phi_zero : phi 0 = 1
  phi_positive : ∀ r ∈ Ioo (-epsilon) epsilon, 0 < phi r
  phi_decreasing : ∀ r ∈ Icc (0 : ℝ) epsilon, deriv phi r ≤ 0
  phi_strict_at_boundary : deriv phi 0 < 0
  levelMetric : E2 → Matrix (Fin 2) (Fin 2) ℝ
  levelMetric_smooth : ∀ i j, ContDiff ℝ ∞ (fun z => levelMetric z i j)
  levelMetric_symmetric : ∀ z i j, levelMetric z i j = levelMetric z j i
  levelMetric_positive : ∀ z (v : E2), v ≠ 0 →
    0 < ∑ i : Fin 2, ∑ j : Fin 2, levelMetric z i j * v i * v j
  warped_metric : ∀ y ∈ coordinates.chart.target, ∀ v w : E3,
    coordinateInner (actualChartTensor h coordinates) y v w =
      v 0 * w 0 + phi (y 0) ^ 2 *
        (∑ i : Fin 2, ∑ j : Fin 2,
          levelMetric (levelCoordinates y) i j * levelVector v i * levelVector w j)

/-- The tangent plane to the actual embedded level surface r=0, obtained
from the same collar chart, rather than stipulated to equal ker dr. -/
def boundaryTangentPlane {h : AmbientMetric N} {M : Set N}
    (C : WarpedBoundaryCollar h M) (p : N)
    (hp : p ∈ C.coordinates.chart.source) :
    Submodule ℝ (TangentSpace 𝓘(ℝ, E3) p) :=
  let d := inverseChartDifferential C.coordinates (C.coordinates.chart p)
  (C.coordinates.chart.left_inv hp) ▸
    LinearMap.range (d.comp levelInclusion).toLinearMap

end SeifertSurfaces.OriginalEndpoints
