import MetricAreaAnalysis.SameImage

open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle

namespace SeifertSurfaces.MetricFoundations
open Foundations
universe u v
noncomputable section

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- Distinct final consumer with the first protected analytic endpoint's exact head. -/
theorem coordinateDensity_integrable_via_chartCover (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S M)
    (P : ChartPartition S) (i : Fin P.count) :
    IntegrableOn (coordinateAreaDensity g f.toFun (P.center i))
      ((extChartAt (𝓡∂ 2) (P.center i)) '' (P.piece i)) := by
  exact AreaAnalysis.coordinateDensity_integrable_measurableChartSubset g f.toFun f.smooth
    (P.center i) (P.piece i) (P.measurable i) (P.subordinate i)

theorem partitionArea_independent_via_commonRefinement (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S M)
    (P Q : ChartPartition S) : partitionArea g f.toFun P = partitionArea g f.toFun Q := by
  have hsum := AreaAnalysis.partitionArea_pairwise_sum g f.toFun f.smooth P Q
  rw [hsum.1, hsum.2, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact AreaAnalysis.coordinateIntegral_overlap g f.toFun f.smooth (P.center i)
    (Q.center j) _ (AreaAnalysis.commonPiece_measurable P Q i j)
    (AreaAnalysis.commonPiece_subordinate P Q i j)

theorem area_positive_via_chartBall (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} [Nonempty S] (f : ProperSmoothEmbedding S M) :
    0 < area g f.toFun := by
  classical
  let p : S := Classical.arbitrary S
  obtain ⟨z, hz⟩ := interior_extChartAt_target_nonempty (𝓡∂ 2) p
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (isOpen_interior.mem_nhds hz)
  have htarget : Metric.closedBall z r ⊆ (AreaAnalysis.surfaceChart p).target :=
    hball.trans interior_subset
  let s : Set S := (AreaAnalysis.surfaceChart p).source ∩
    (AreaAnalysis.surfaceChart p) ⁻¹' Metric.ball z r
  have hs : MeasurableSet s := AreaAnalysis.extChart_source_preimage_measurable p _
    Metric.isOpen_ball.measurableSet
  have hsub : s ⊆ (AreaAnalysis.surfaceChart p).source := inter_subset_left
  have himage : (AreaAnalysis.surfaceChart p) '' s = Metric.ball z r := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      have hyt := htarget (Metric.ball_subset_closedBall hy)
      refine ⟨(AreaAnalysis.surfaceChart p).symm y, ?_,
        (AreaAnalysis.surfaceChart p).right_inv hyt⟩
      exact ⟨(AreaAnalysis.surfaceChart p).map_target hyt, by
        change AreaAnalysis.surfaceChart p ((AreaAnalysis.surfaceChart p).symm y) ∈ Metric.ball z r
        rwa [(AreaAnalysis.surfaceChart p).right_inv hyt]⟩
  have hpos : 0 < AreaAnalysis.coordinateIntegral g f.toFun p s := by
    unfold AreaAnalysis.coordinateIntegral
    change 0 < ∫ y in (AreaAnalysis.surfaceChart p) '' s,
      coordinateAreaDensity g f.toFun p y
    rw [himage]
    exact AreaAnalysis.coordinateBall_integral_pos g f p z r hr htarget
  exact hpos.trans_le (AreaAnalysis.coordinateSubset_integral_le_partitionArea g f
    (canonicalPartition S) p s hs hsub)

theorem area_reparametrization_via_interiorTransport (g : SmoothMetric M)
    {S R : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S M)
    (e : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) R S ∞) :
    area g (f.toFun ∘ e) = area g f.toFun := by
  exact AreaAnalysis.interiorSourceMap_finite_sum_transport g f.toFun (f.toFun ∘ e)
    f.smooth (f.smooth.comp e.contMDiff) e.toHomeomorph (e.preimage_boundary (by simp))
    e.contMDiff.contMDiffOn (fun _ => rfl) (canonicalPartition R) (canonicalPartition S)

/-- H28: exact original same-image endpoint under a distinct name. -/
theorem area_same_image_via_interiorTransport (g : SmoothMetric M)
    {S R : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S M)
    (h : ProperSmoothEmbedding R M) (heq : f.image = h.image) :
    area g f.toFun = area g h.toFun := by
  exact (AreaAnalysis.interiorSourceMap_finite_sum_transport g f.toFun h.toFun
    f.smooth h.smooth (AreaAnalysis.sameImageHomeomorph f h heq)
    (AreaAnalysis.sameImage_homeomorph_boundary f h heq)
    (AreaAnalysis.sameImage_homeomorph_interior_smooth f h heq)
    (fun x => (AreaAnalysis.sameImage_homeomorph_matches f h heq x).symm)
    (canonicalPartition R) (canonicalPartition S)).symm

end
end SeifertSurfaces.MetricFoundations
