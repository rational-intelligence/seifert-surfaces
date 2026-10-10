import A5ReconstructedMinimizer

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- Full original competitor membership gives the exact smooth-area
comparison, independent of the chosen native piecewise presentation. -/
theorem FixedBoundaryMinimizer.smooth_area_le
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {S R Q : CompactOrientedSurface.{u}} {g : SmoothMetric E.Carrier}
    {F : GeometricPiecewiseSurface S E.Carrier}
    {Fprime : GeometricPiecewiseSurface R E.Carrier}
    (hminimum : FixedBoundaryMinimizer E g F Fprime)
    (f : ProperSmoothEmbedding Q E.Carrier)
    (C : GeometricPiecewiseSurface Q E.Carrier)
    (hC : C.map = f.continuousMap)
    (hclass : FixedBoundaryImageIsotopic E F C) :
    geometricArea g Fprime ≤ area g f.toFun := by
  rw [← smooth_piecewise_area g f C hC]
  exact hminimum.area_le C hclass

/-- Consume nearby genuine geometric competitors to obtain precisely the
original fixed-boundary second variation inequality. The remaining geometry
is isolated as membership in the full original class, without changing it. -/
theorem reconstructed_second_variation_of_nearby_original_competitors
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {S R : CompactOrientedSurface.{u}} {g : SmoothMetric E.Carrier}
    {F : GeometricPiecewiseSurface S E.Carrier}
    {Fprime : GeometricPiecewiseSurface R E.Carrier}
    (hminimum : FixedBoundaryMinimizer E g F Fprime)
    (Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime)
    (H : ℝ → ProperSmoothEmbedding Q.source E.Carrier)
    (hzero : (H 0).toFun = Q.embedding.toFun)
    (hcompetitors : ∀ᶠ t in 𝓝 (0 : ℝ), ∃ C : GeometricPiecewiseSurface Q.source E.Carrier,
      C.map = (H t).continuousMap ∧ FixedBoundaryImageIsotopic E F C)
    (harea : ContDiffAt ℝ 2 (fun t => area g (H t).toFun) 0) :
    0 ≤ deriv (deriv (fun t => area g (H t).toFun)) 0 := by
  obtain ⟨_, _, _, _, hsame⟩ := smooth_source_reconstruction_is_original_minimizer E g F Fprime hminimum Q
  apply second_deriv_nonnegative_of_local_min _ harea.continuousAt
  change ∀ᶠ t in 𝓝 (0 : ℝ), area g (H 0).toFun ≤ area g (H t).toFun
  filter_upwards [hcompetitors] with t ht
  obtain ⟨C, hC, hclass⟩ := ht
  rw [hzero, hsame]
  exact hminimum.smooth_area_le (H t) C hC hclass

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
