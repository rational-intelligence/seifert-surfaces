import Section4GeometricDefinitions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
noncomputable section
open Set Topology MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints.Section4
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.GenusLinking

theorem geometric_area_nonnegative {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    (g : SmoothMetric M) {S : CompactOrientedSurface.{0}}
    (C : GeometricPiecewiseSurface S M) : 0 ≤ geometricArea g C := by
  unfold geometricArea
  apply Finset.sum_nonneg
  intro i _
  unfold sectorArea sectorPartitionArea
  apply Finset.sum_nonneg
  intro j _
  exact setIntegral_nonneg_of_ae
    (Filter.Eventually.of_forall (fun _ => Real.sqrt_nonneg _))

theorem area_infimum_values_bddBelow {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (H : SourceGeometry E) (v : Vertices E) :
    BddBelow {a : ℝ | ∃ F : IncompressibleSpanningSurface.{0} E,
      classOf E (surfaceImageOf E F) = v ∧
      ∃ smoothModel : GeometricPiecewiseSurface F.1.surface E.Carrier,
        smoothModel.map = F.1.embedding.continuousMap ∧
      ∃ R : CompactOrientedSurface.{0}, ∃ C : GeometricPiecewiseSurface R E.Carrier,
        H.foliation.BoundaryIn C.map ∧ GeometricImageIsotopic smoothModel C ∧
        a = geometricArea H.metric C} := by
  refine ⟨0, ?_⟩
  rintro a ⟨F, _, f, _, R, C, _, _, rfl⟩
  exact geometric_area_nonnegative H.metric C

theorem area_infimum_le_competitor {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (H : SourceGeometry E) (v : Vertices E)
    (F : IncompressibleSpanningSurface.{0} E)
    (hr : classOf E (surfaceImageOf E F) = v)
    (f : GeometricPiecewiseSurface F.1.surface E.Carrier)
    (hf : f.map = F.1.embedding.continuousMap)
    {S : CompactOrientedSurface.{0}} (C : GeometricPiecewiseSurface S E.Carrier)
    (hJ : H.foliation.BoundaryIn C.map) (hi : GeometricImageIsotopic f C) :
    areaInfimum E H v ≤ geometricArea H.metric C := by
  apply csInf_le (area_infimum_values_bddBelow E H v)
  exact ⟨F, hr, f, hf, S, C, hJ, hi, rfl⟩

theorem relative_minimizer_of_attains_infimum {K : OrientedKnot}
    {T : TubularNeighborhood K} (E : SmoothExterior T) (H : SourceGeometry E)
    (v : Vertices E) (F : IncompressibleSpanningSurface.{0} E)
    (hr : classOf E (surfaceImageOf E F) = v)
    (f : GeometricPiecewiseSurface F.1.surface E.Carrier)
    (hf : f.map = F.1.embedding.continuousMap)
    (hJ : H.foliation.BoundaryIn F.1.embedding.toFun)
    (harea : area H.metric F.1.embedding.toFun = areaInfimum E H v) :
    IsRelativeAreaMinimizer H.metric H.foliation F := by
  refine ⟨hJ, f, hf, ?_⟩
  intro S C hC hi
  rw [harea]
  exact area_infimum_le_competitor E H v F hr f hf C hC hi

theorem a6_competitor_values_bddBelow {K : OrientedKnot}
    {T : TubularNeighborhood K} (E : SmoothExterior T) (H : SourceGeometry E)
    (m : A7.A6Minimizer E H.ambient H.foliation) :
    BddBelow {a : ℝ | ∃ R : CompactOrientedSurface.{0},
      ∃ C : GeometricPiecewiseSurface R E.Carrier,
        H.foliation.BoundaryIn C.map ∧ GeometricImageIsotopic m.initial C ∧
        a = geometricArea H.metric C} := by
  refine ⟨0, ?_⟩
  rintro a ⟨R, C, _, _, rfl⟩
  exact geometric_area_nonnegative H.metric C

theorem a6_area_le_competitor {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (H : SourceGeometry E)
    (m : A7.A6Minimizer E H.ambient H.foliation)
    {S : CompactOrientedSurface.{0}} (C : GeometricPiecewiseSurface S E.Carrier)
    (hJ : H.foliation.BoundaryIn C.map) (hi : GeometricImageIsotopic m.initial C) :
    area H.metric m.embedding.toFun ≤ geometricArea H.metric C := by
  change area H.ambient.metric m.embedding.toFun ≤ geometricArea H.ambient.metric C
  rw [m.area_attainment]
  exact csInf_le (a6_competitor_values_bddBelow E H m) ⟨S, C, hJ, hi, rfl⟩

theorem a6_native_area_infimum_eq_of_class_correspondence {K : OrientedKnot}
    {T : TubularNeighborhood K} (E : SmoothExterior T) (H : SourceGeometry E)
    (m : A7.A6Minimizer E H.ambient H.foliation) (v : Vertices E)
    (hnative : {a : ℝ | ∃ F : IncompressibleSpanningSurface.{0} E,
      classOf E (surfaceImageOf E F) = v ∧
      ∃ smoothModel : GeometricPiecewiseSurface F.1.surface E.Carrier,
        smoothModel.map = F.1.embedding.continuousMap ∧
      ∃ R : CompactOrientedSurface.{0}, ∃ C : GeometricPiecewiseSurface R E.Carrier,
        H.foliation.BoundaryIn C.map ∧ GeometricImageIsotopic smoothModel C ∧
        a = geometricArea H.metric C} =
      {a : ℝ | ∃ R : CompactOrientedSurface.{0},
        ∃ C : GeometricPiecewiseSurface R E.Carrier,
          H.foliation.BoundaryIn C.map ∧ GeometricImageIsotopic m.initial C ∧
          a = geometricArea H.metric C}) :
    area H.metric m.embedding.toFun = areaInfimum E H v := by
  rw [areaInfimum, hnative]
  exact m.area_attainment

end SeifertSurfaces.OriginalEndpoints.Section4
