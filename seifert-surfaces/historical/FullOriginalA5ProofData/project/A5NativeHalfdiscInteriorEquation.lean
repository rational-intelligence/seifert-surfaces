import A5MetricGraphInteriorFromImageCover
import A5BoundaryChartComposition

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
universe u

/-- The interior of an actual native boundary graph satisfies its actual
smooth minimal graph equation, using only the paid native interior cover. -/
theorem native_halfdisc_metric_graph_interior_equation
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : AmbientMetric ThreeSphere) (G : NativeMetricGraph h)
    (e : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (hb : e '' (S.boundary ∩ e.source) =
      ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ e.target)
    (P : E3 →L[ℝ] E2) (hPo : P G.origin = 0)
    (hPp : ∀ v, P (G.plane v) = v) (hPn : P G.normal = 0)
    (r : ℝ) (hrG : r < G.radius)
    (hdata : ∀ z ∈ closedHalfDisc r,
      (𝓡∂ 2).symm z ∈ e.target ∧
      E.toSphere (F.map (e.symm ((𝓡∂ 2).symm z))) ∈ G.coordinates.chart.source ∧
      graphMap G.origin G.plane G.normal G.height z =
        G.coordinates.chart (E.toSphere (F.map (e.symm ((𝓡∂ 2).symm z)))))
    (hcover : ∀ x, x ∉ S.boundary →
      ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source)
    (hpieces : ∀ i j, IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target)) :
    ContDiffOn ℝ ∞ G.height (openHalfDisc r) ∧
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) (openHalfDisc r) := by
  let d : OpenPartialHomeomorph (EuclideanHalfSpace 2) E2 := {
    toFun := (𝓡∂ 2)
    invFun := (𝓡∂ 2).symm
    source := {z | 0 < ((𝓡∂ 2) z) 0}
    target := {z | 0 < z 0}
    map_source' := fun _ hz => hz
    map_target' := fun z hz => by
      change 0 < z 0 at hz
      change 0 < ((𝓡∂ 2) ((𝓡∂ 2).symm z)) 0
      rw [(𝓡∂ 2).right_inv (by rw [range_modelWithCornersEuclideanHalfSpace]; exact hz.le)]
      exact hz
    left_inv' := fun z _ => (𝓡∂ 2).left_inv z
    right_inv' := fun z hz => by
      change 0 < z 0 at hz
      exact (𝓡∂ 2).right_inv (by rw [range_modelWithCornersEuclideanHalfSpace]; exact hz.le)
    open_source := isOpen_lt continuous_const
      ((EuclideanSpace.proj 0).continuous.comp (𝓡∂ 2).continuous)
    open_target := isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
    continuousOn_toFun := (𝓡∂ 2).continuous.continuousOn
    continuousOn_invFun := (𝓡∂ 2).continuous_symm.continuousOn }
  let V := (𝓡∂ 2) ⁻¹' Metric.ball (0 : E2) r
  have hV : IsOpen V := Metric.isOpen_ball.preimage (𝓡∂ 2).continuous
  let er := (e.symm.restrOpen V hV).symm
  let ep := er.trans d
  have her (y : EuclideanHalfSpace 2) (hy : y ∈ er.target) :
      (𝓡∂ 2) y ∈ closedHalfDisc r :=
    ⟨Metric.ball_subset_closedBall hy.2,y.property⟩
  have hmaps : MapsTo (E.toSphere ∘ F.map) ep.source G.coordinates.chart.source := by
    intro y hy
    have hz := her (er y) (er.map_source hy.1)
    have hd := (hdata _ hz).2.1
    rw [(𝓡∂ 2).left_inv] at hd
    change E.toSphere (F.map (e.symm (e y))) ∈ G.coordinates.chart.source at hd
    rw [e.left_inv hy.1.1] at hd
    exact hd
  have he : ∀ y ∈ ep.source,
      ep y = P (G.coordinates.chart (E.toSphere (F.map y))) := by
    intro y hy
    have hz := her (er y) (er.map_source hy.1)
    have hg := (hdata _ hz).2.2
    rw [(𝓡∂ 2).left_inv] at hg
    change graphMap G.origin G.plane G.normal G.height ((𝓡∂ 2) (e y)) =
      G.coordinates.chart (E.toSphere (F.map (e.symm (e y)))) at hg
    rw [e.left_inv hy.1.1] at hg
    rw [← hg]
    simp only [graphMap,map_add,map_smul,hPo,hPp,hPn,smul_zero,zero_add,add_zero]
    rfl
  have htarget : openHalfDisc r ⊆ ep.target := by
    intro z hz
    have hpos : 0 < z 0 := hz.2
    have hzR : z ∈ range (𝓡∂ 2) := by
      rw [range_modelWithCornersEuclideanHalfSpace]; exact hpos.le
    refine ⟨hz.2,(hdata z (openHalfDisc_subset_closedHalfDisc r hz)).1,?_⟩
    change (𝓡∂ 2) ((𝓡∂ 2).symm z) ∈ Metric.ball 0 r
    rw [(𝓡∂ 2).right_inv hzR]
    exact hz.1
  have hboundary : ∀ z ∈ openHalfDisc r, ep.symm z ∉ S.boundary := by
    intro z hz hzB
    have hzT := htarget hz
    have hh : e (ep.symm z) ∈ ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ e.target := by
      rw [← hb]
      exact ⟨ep.symm z,⟨hzB,(ep.map_target hzT).1.1⟩,rfl⟩
    have heq : e (ep.symm z) = (𝓡∂ 2).symm z := e.right_inv hzT.2.1
    rw [heq] at hh
    have hzero := (model_halfspace_boundary_iff _).mp hh.1
    have hpos : 0 < z 0 := hz.2
    rw [(𝓡∂ 2).right_inv (by rw [range_modelWithCornersEuclideanHalfSpace]; exact hpos.le)] at hzero
    exact (ne_of_gt hz.2) hzero
  apply native_metric_graph_smooth_minimal_of_image_cover E F h G ep P he hmaps
    (openHalfDisc r) (openHalfDisc_isOpen r) htarget
  · intro z hz
    exact (Metric.mem_ball.mp hz.1).trans hrG
  · intro z hz
    exact (hdata z (openHalfDisc_subset_closedHalfDisc r hz)).2.2
  · exact hboundary
  · intro z hz
    exact hcover _ (hboundary z hz)
  · exact hpieces

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
