import B1CollarWindow_v468
import A5MinimizerConsequences

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

theorem native_fixed_boundary_forget_v475
    {S Q : CompactOrientedSurface.{v}}
    {F : GeometricPiecewiseSurface S E.Carrier}
    {C : GeometricPiecewiseSurface Q E.Carrier}
    (h : FixedBoundaryImageIsotopic E F C) : GeometricImageIsotopic F C := by
  obtain ⟨e,stage,hcont,htrack,hzero,hone,hfixed⟩ := h
  exact ⟨e,stage,hcont,htrack,hzero,hone⟩

theorem native_relative_fixed_comparison_v475
    (A : IncompressibleSpanningSurface.{v} E)
    (hminimum : IsRelativeAreaMinimizer g J A) :
    ∃ F : GeometricPiecewiseSurface A.1.surface E.Carrier,
      F.map = ProperSmoothEmbedding.continuousMap
        (ProperSmoothEmbedding.ofNeat A.1.embedding) ∧
      ∀ Q : CompactOrientedSurface.{v},
      ∀ C : GeometricPiecewiseSurface Q E.Carrier,
        FixedBoundaryImageIsotopic E F C → geometricArea g F ≤ geometricArea g C := by
  obtain ⟨hboundary,F,hF,hmin⟩ := hminimum
  refine ⟨F,hF,?_⟩
  intro Q C hC
  have hB : J.BoundaryIn C.map := by
    obtain ⟨a,ha⟩ := hboundary
    refine ⟨a,?_⟩
    rw [hC.boundary_image_eq,hF]
    exact ha
  rw [smooth_piecewise_area g (ProperSmoothEmbedding.ofNeat A.1.embedding) F hF]
  exact hmin Q C hB (native_fixed_boundary_forget_v475 hC)

theorem actual_relative_fixed_comparisons_v475 (D : B1OriginalData g J) :
    (∃ F : GeometricPiecewiseSurface D.A.1.surface E.Carrier,
      F.map = ProperSmoothEmbedding.continuousMap
        (ProperSmoothEmbedding.ofNeat D.A.1.embedding) ∧
      ∀ Q : CompactOrientedSurface.{v},
      ∀ C : GeometricPiecewiseSurface Q E.Carrier,
        FixedBoundaryImageIsotopic E F C → geometricArea g F ≤ geometricArea g C) ∧
    (∃ F : GeometricPiecewiseSurface D.B.1.surface E.Carrier,
      F.map = ProperSmoothEmbedding.continuousMap
        (ProperSmoothEmbedding.ofNeat D.B.1.embedding) ∧
      ∀ Q : CompactOrientedSurface.{v},
      ∀ C : GeometricPiecewiseSurface Q E.Carrier,
        FixedBoundaryImageIsotopic E F C → geometricArea g F ≤ geometricArea g C) := by
  exact ⟨native_relative_fixed_comparison_v475 D.A D.A_relative_minimum,
    native_relative_fixed_comparison_v475 D.B D.B_relative_minimum⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_relative_fixed_comparisons_v475
