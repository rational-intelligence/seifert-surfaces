import A5PaidBoundaryBootstrapCompatibility
import A5NativeHalfdiscInteriorEquation

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

/-- Actual native C1 boundary image geometry, the smooth longitude and the
native interior minimal image cover give an actual native smooth boundary
image chart. The scalar graph is regularized by the proved original
same-function Dirichlet bootstrap after constructing its metric operator. -/
theorem native_boundary_C1_image_chart_to_smooth
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (J : LongitudeFoliation.{u} E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (hF : J.BoundaryIn F.map)
    (C : BoundaryC1ImageChart S E.Carrier F.map)
    (x : S) (hx : x ∈ C.chart.source) (hxb : x ∈ S.boundary)
    (h : AmbientMetric ThreeSphere)
    (hcover : ∀ y, y ∉ S.boundary →
      ∃ C : SmoothImageChart S F.map, y ∈ C.chart.source)
    (hpieces : ∀ i j, IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target)) :
    ∃ D : SmoothImageChart S F.map, x ∈ D.chart.source := by
  obtain ⟨e,hxe,hex,heb,G,P,r,g,hr,hrG,hPo,hPp,hPn,hdata,hb⟩ :=
    native_boundary_C1_image_straightened_metric_data E J F hF C x hx hxb h
  obtain ⟨hs,hm⟩ := native_halfdisc_metric_graph_interior_equation
    E F h G e heb P hPo hPp hPn r hrG hdata hcover hpieces
  obtain ⟨control,hsolution⟩ := native_metric_graph_boundary_dirichlet_context
    G r hr hrG g hb hs hm
  have hr2 : 0 < r / 2 := half_pos hr
  have hrr : r / 2 < r := half_lt_self hr
  have hsmooth : ContDiffOn ℝ ∞ G.height (closedHalfDisc (r / 2)) :=
    smooth_of_C1_weak_uniformlyElliptic_dirichlet r hr control.jetDomain
      (G.operator control) g G.height hsolution (r / 2) hr2 hrr
  let V := (𝓡∂ 2) ⁻¹' Metric.ball (0 : E2) r
  have hV : IsOpen V := Metric.isOpen_ball.preimage (𝓡∂ 2).continuous
  let er := (e.symm.restrOpen V hV).symm
  have hxr : x ∈ er.source := by
    refine ⟨hxe,?_⟩
    change (𝓡∂ 2) (e x) ∈ Metric.ball 0 r
    rw [hex]
    exact Metric.mem_ball_self hr
  have hcenter : (𝓡∂ 2) (er x) = 0 := by
    change (𝓡∂ 2) (e x) = 0
    rw [hex]
    rfl
  have hbr : er '' (S.boundary ∩ er.source) =
      ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ er.target := by
    ext y
    constructor
    · rintro ⟨z,⟨hzB,hz⟩,rfl⟩
      have hzb : e z ∈ ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ e.target := by
        rw [← heb]
        exact ⟨z,⟨hzB,hz.1⟩,rfl⟩
      exact ⟨hzb.1,er.map_source hz⟩
    · intro hy
      have heB : y ∈ e '' (S.boundary ∩ e.source) := heb.symm ▸ ⟨hy.1,hy.2.1⟩
      obtain ⟨z,⟨hzB,hze⟩,hzy⟩ := heB
      refine ⟨z,⟨hzB,⟨hze,?_⟩⟩,hzy⟩
      change e z ∈ V
      rw [hzy]
      exact hy.2.2
  have hdata' (y : EuclideanHalfSpace 2) (hy : y ∈ er.target) :
      E.toSphere (F.map (er.symm y)) ∈ G.coordinates.chart.source ∧
      graphMap G.origin G.plane G.normal G.height ((𝓡∂ 2) y) =
        G.coordinates.chart (E.toSphere (F.map (er.symm y))) := by
    have hh := (hdata ((𝓡∂ 2) y) ⟨Metric.ball_subset_closedBall hy.2,y.property⟩).2
    rw [(𝓡∂ 2).left_inv] at hh
    exact hh
  obtain ⟨D,hDx,_⟩ := native_boundary_image_chart_of_smooth_metric_halfdisc
    E F er x hxr hcenter hbr h G P hPo hPp hPn (r / 2) hr2 hsmooth
    (fun y hy => (hdata' y hy).1) (fun y hy _ => (hdata' y hy).2)
  exact ⟨D,hDx⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
