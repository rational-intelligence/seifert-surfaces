import B1FixedBoundaryIdentity_v475

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

theorem native_relative_fixed_minimum_v475
    (A : IncompressibleSpanningSurface.{v} E)
    (hminimum : IsRelativeAreaMinimizer g J A) :
    ∃ F : GeometricPiecewiseSurface A.1.surface E.Carrier,
      F.map = ProperSmoothEmbedding.continuousMap
        (ProperSmoothEmbedding.ofNeat A.1.embedding) ∧
      FixedBoundaryMinimizer E g F F := by
  obtain ⟨F,hF,hcompare⟩ := native_relative_fixed_comparison_v475 A hminimum
  have hself := native_fixed_boundary_image_isotopic_refl_v475 F
  refine ⟨F,hF,hself,?_⟩
  unfold fixedBoundaryInfimum
  have hmember : geometricArea g F ∈ {a : ℝ |
      ∃ Q : CompactOrientedSurface.{v}, ∃ C : GeometricPiecewiseSurface Q E.Carrier,
        FixedBoundaryImageIsotopic E F C ∧ a = geometricArea g C} :=
    ⟨A.1.surface,F,hself,rfl⟩
  apply le_antisymm
  · apply le_csInf ⟨_,hmember⟩
    rintro a ⟨Q,C,hC,rfl⟩
    exact hcompare Q C hC
  · apply csInf_le _ hmember
    refine ⟨0,?_⟩
    rintro a ⟨Q,C,hC,rfl⟩
    exact geometricArea_nonnegative g C

theorem actual_relative_fixed_minima_v475 (D : B1OriginalData g J) :
    (∃ F : GeometricPiecewiseSurface D.A.1.surface E.Carrier,
      F.map = ProperSmoothEmbedding.continuousMap
        (ProperSmoothEmbedding.ofNeat D.A.1.embedding) ∧
      FixedBoundaryMinimizer E g F F) ∧
    (∃ F : GeometricPiecewiseSurface D.B.1.surface E.Carrier,
      F.map = ProperSmoothEmbedding.continuousMap
        (ProperSmoothEmbedding.ofNeat D.B.1.embedding) ∧
      FixedBoundaryMinimizer E g F F) := by
  exact ⟨native_relative_fixed_minimum_v475 D.A D.A_relative_minimum,
    native_relative_fixed_minimum_v475 D.B D.B_relative_minimum⟩

theorem native_fixed_minimum_family_stationarity_v475
    {S Q : CompactOrientedSurface.{v}} {F : GeometricPiecewiseSurface S E.Carrier}
    (hminimum : FixedBoundaryMinimizer E g F F)
    (H : ℝ → GeometricPiecewiseSurface Q E.Carrier)
    (hadmissible : ∀ t, FixedBoundaryImageIsotopic E F (H t))
    (hinitial : (H 0).image = F.image)
    {variation : ℝ} (hvariation : HasDerivAt (fun t => geometricArea g (H t)) variation 0) :
    variation = 0 := by
  have hmin : IsLocalMin (fun t => geometricArea g (H t)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change geometricArea g (H 0) ≤ geometricArea g (H t)
    rw [piecewiseArea_same_image g (H 0) F hinitial]
    exact hminimum.area_le (H t) (hadmissible t)
  exact hmin.hasDerivAt_eq_zero hvariation

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_relative_fixed_minima_v475
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_fixed_minimum_family_stationarity_v475
