import A5NativeVertexFullRemoval
import A5SmoothImageProjection

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- Full interior isolated-point removal for the literal native image:
actual piece minimality and smooth image charts at every other nearby point
suffice. The common projection, all tangent matching, punctured topology,
C¹ graph and elliptic point removal are constructed internally. -/
theorem native_interior_image_chart_of_punctured_image_cover
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : AmbientMetric ThreeSphere) (x : S)
    (V : Set S) (hV : IsOpen V) (hxV : x ∈ V) (hVboundary : V ⊆ S.boundaryᶜ)
    (c : SmoothAmbientChart ThreeSphere) (hc : E.toSphere (F.map x) ∈ c.chart.source)
    (hpieces : ∀ i j, IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target))
    (hcover : ∀ z ∈ V, z ≠ x → ∃ C : SmoothImageChart S F.map, z ∈ C.chart.source) :
    ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source ∧ C.chart.source ⊆ V := by
  apply native_interior_vertex_full_removal E F h x V hV hxV hVboundary c hc hpieces hcover
  · intro i j k l z w hz hw heq hzs hne hchart
    let y := F.parametrization i (((F.domain i).chart j).map.symm z)
    obtain ⟨C, hyC⟩ := hcover y hzs hne
    obtain ⟨d, hyd, _, hs, hr⟩ := native_image_chart_plane_parametrization S F.map C y hyC (hVboundary hzs)
    have h1 := native_sector_tangent_matches_smooth_plane_chart E F d hs hr i j z hz hyd c hchart
    have hkd : F.parametrization k (((F.domain k).chart l).map.symm w) ∈ d.source :=
      heq ▸ hyd
    have hkc : E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization k) l w) ∈ c.chart.source := by
      change E.toSphere (F.map (F.parametrization k _)) ∈ _
      rw [← heq]
      exact hchart
    have h2 := native_sector_tangent_matches_smooth_plane_chart E F d hs hr k l w hw hkd c hkc
    rw [← heq] at h2
    exact h1.trans h2.symm
  · intro P z hz hne _ hchart htrans
    obtain ⟨C, hzC⟩ := hcover z hz hne
    have hzcover : z ∈ ⋃ i, range (F.parametrization i) := by rw [F.covers]; trivial
    obtain ⟨i, v, hv⟩ := mem_iUnion.mp hzcover
    have hvcover : v ∈ ⋃ j, ((F.domain i).chart j).map.source := by rw [(F.domain i).covers]; trivial
    obtain ⟨j, hvj⟩ := mem_iUnion.mp hvcover
    let y := ((F.domain i).chart j).map v
    have hy : y ∈ ((F.domain i).chart j).map.target := ((F.domain i).chart j).map.map_source hvj
    have hyz : F.parametrization i (((F.domain i).chart j).map.symm y) = z := by
      rw [((F.domain i).chart j).map.left_inv hvj, hv]
    apply native_smooth_image_projection_local_homeomorph E F z (hVboundary hz) C hzC c hchart P i j y hy hyz
    apply htrans i j y hy
    exact congrArg F.map hyz

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
