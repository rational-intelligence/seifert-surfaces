import B1TangencyPositive

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

def jacobian (F : E2 → E2) (x : E2) : Mat2 :=
  fun i j => (fderiv ℝ F x (coordinateVector 2 j)) i

def densityLeading (a : E2 → Mat2) (F : E2 → E2) (x : E2) : Mat2 :=
  |Matrix.det (jacobian F x)|⁻¹ •
    (jacobian F x * a x * (jacobian F x).transpose)
def densityDrift (b : E2 → E2) (F : E2 → E2) (x : E2) : E2 :=
  |Matrix.det (jacobian F x)|⁻¹ • matrixAction (jacobian F x) (b x)

structure BoundaryIsothermalPatch {D : B1OriginalData g J} {s : Circle}
    {W : CollarWindow D s} (N : PositiveNormalization W) where
  sourceR : ℝ
  sourceR_pos : 0 < sourceR
  sourceR_inside : sourceR < N.R / 2
  targetR : ℝ
  targetR_pos : 0 < targetR
  chart : PartialHomeomorph E2 E2
  source_contains : closedHalfDisc sourceR ⊆ chart.source
  target_contains : closedHalfDisc targetR ⊆ chart.target
  base : chart 0 = 0
  forward_C1 : ContDiffOn ℝ 1 chart chart.source
  inverse_C1 : ContDiffOn ℝ 1 chart.symm chart.target
  forward_det : ∀ x ∈ chart.source, Matrix.det (jacobian chart x) ≠ 0
  inverse_det : ∀ z ∈ chart.target, Matrix.det (jacobian chart.symm z) ≠ 0
  alpha : ℝ≥0
  alpha_pos : 0 < alpha
  alpha_lt_one : alpha < 1
  forward_holder : ∀ i j, ∃ C : ℝ≥0,
    HolderOnWith C alpha (fun x => jacobian chart x i j) (closedHalfDisc sourceR)
  inverse_holder : ∀ i j, ∃ C : ℝ≥0,
    HolderOnWith C alpha (fun z => jacobian chart.symm z i j) (closedHalfDisc targetR)
  forward_boundary : ∀ x ∈ closedHalfDisc sourceR, (chart x) 1 = 0 ↔ x 1 = 0
  forward_interior : ∀ x ∈ halfDisc sourceR, 0 < (chart x) 1
  inverse_half_disc : ∀ z ∈ closedHalfDisc targetR, chart.symm z ∈ closedHalfDisc sourceR
  inverse_interior : ∀ z ∈ halfDisc targetR, chart.symm z ∈ halfDisc sourceR
  inverse_flat : ∀ z ∈ flatArc targetR, chart.symm z ∈ flatArc sourceR
  biLipschitz : ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
    ∀ x ∈ closedHalfDisc sourceR, ∀ y ∈ closedHalfDisc sourceR,
      lo * dist x y ≤ dist (chart x) (chart y) ∧ dist (chart x) (chart y) ≤ hi * dist x y
  conformalInverseMetric : ∀ x ∈ closedHalfDisc sourceR, ∃ lambda : ℝ,
    0 < lambda ∧ (N.normalizedA x)⁻¹ =
      lambda • ((jacobian chart x).transpose * jacobian chart x)

namespace BoundaryIsothermalPatch
variable {D : B1OriginalData g J} {s : Circle} {W : CollarWindow D s}
variable {N : PositiveNormalization W}
def vhat (F : BoundaryIsothermalPatch N) (z : E2) : ℝ := N.v (F.chart.symm z)
def bhat (F : BoundaryIsothermalPatch N) (z : E2) : E2 :=
  densityDrift N.normalizedB F.chart (F.chart.symm z)
end BoundaryIsothermalPatch

/- Local boundary-preserving C1,alpha coordinates for g=a^-1, from the
source's Lichtenstein route [9, Thm 4.1, m=1]. No differentiability of DF is claimed. -/
end SeifertSurfaces.OriginalEndpoints.B1Tangency
