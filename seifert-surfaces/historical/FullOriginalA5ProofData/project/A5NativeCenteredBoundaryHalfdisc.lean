import A5NativeBoundaryC1Coordinates
import A5CenteredC1Halfdisc

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
universe u

/-- The actual approved boundary C1 chart admits a centered regular
Euclidean half-disc in an actual ambient coordinate chart. This consumes
only its stated fields and preserves the original map pointwise. -/
theorem native_boundary_C1_chart_centered_halfdisc
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (C : BoundaryC1ImageChart S E.Carrier F.map)
    (x : S) (hx : x ∈ C.chart.source) (hxb : x ∈ S.boundary)
    (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (F.map x) ∈ c.chart.source) :
    ∃ d : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2),
      d.source = univ ∧ d.target = univ ∧ d (C.chart x) = 0 ∧ d.symm 0 = C.chart x ∧
      (∀ z, (𝓡∂ 2) (d z) = (𝓡∂ 2) z - (𝓡∂ 2) (C.chart x)) ∧
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ d d.source ∧
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ d.symm d.target ∧
      ∃ ρ : ℝ, 0 < ρ ∧
        (∀ z ∈ closedHalfDisc ρ,
          d.symm ((𝓡∂ 2).symm z) ∈ C.chart.target ∧
          E.toSphere (F.map (C.chart.symm (d.symm ((𝓡∂ 2).symm z)))) ∈ c.chart.source) ∧
        ContDiffOn ℝ 1
          (c.chart ∘ E.toSphere ∘ F.map ∘ C.chart.symm ∘ d.symm ∘ (𝓡∂ 2).symm)
          (closedHalfDisc ρ) ∧
        Function.Injective (fderivWithin ℝ
          (c.chart ∘ E.toSphere ∘ F.map ∘ C.chart.symm ∘ d.symm ∘ (𝓡∂ 2).symm)
          (closedHalfDisc ρ) 0) := by
  obtain ⟨V,hV,hxV,hsub,hmap,hreg,hrank⟩ :=
    native_boundary_C1_image_coordinate_patch E F C x hx c hc
  have hab : ((𝓡∂ 2) (C.chart x)) 0 = 0 := by
    have hh : C.chart x ∈ ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ C.chart.target := by
      rw [← C.boundary_image]
      exact ⟨x,⟨hxb,hx⟩,rfl⟩
    have hb := (ModelWithCorners.isBoundaryPoint_iff (I := 𝓡∂ 2)).mp hh.1
    rw [extChartAt_self_apply,frontier_range_modelWithCornersEuclideanHalfSpace] at hb
    exact hb.symm
  obtain ⟨d,hds,hdt,hda,hdia,hdf,hd,hdi,ρ,hρ,hρmap,hf,hfi⟩ :=
    C1_halfspace_image_centered_halfdisc
      (c.chart ∘ E.toSphere ∘ F.map ∘ C.chart.symm) V hV hreg
      (C.chart x) hxV hab (hrank _ hxV)
  exact ⟨d,hds,hdt,hda,hdia,hdf,hd,hdi,ρ,hρ,
    fun z hz => ⟨hsub (hρmap hz),hmap (hρmap hz)⟩,hf,hfi⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
