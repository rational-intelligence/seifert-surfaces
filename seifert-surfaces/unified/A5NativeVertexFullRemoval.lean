import A5NativeVertexChartConstruction
import A5NativeVertexTopology
import A5NativeInteriorProjection

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- Native isolated-vertex removal constructs its own common projection,
isolated fiber, local homeomorphism and C¹ metric graph. The punctured
ordinary-seam geometry is the sole remaining local geometry input. -/
theorem native_interior_vertex_full_removal
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : AmbientMetric ThreeSphere) (x : S)
    (V : Set S) (hV : IsOpen V) (hxV : x ∈ V) (hVboundary : V ⊆ S.boundaryᶜ)
    (c : SmoothAmbientChart ThreeSphere) (hc : E.toSphere (F.map x) ∈ c.chart.source)
    (hpieces : ∀ i j, IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target))
    (hcover : ∀ z ∈ V, z ≠ x → ∃ C : SmoothImageChart S F.map, z ∈ C.chart.source)
    (htangent : ∀ i j k l z w,
      z ∈ ((F.domain i).chart j).map.target → w ∈ ((F.domain k).chart l).map.target →
      F.parametrization i (((F.domain i).chart j).map.symm z) =
        F.parametrization k (((F.domain k).chart l).map.symm w) →
      F.parametrization i (((F.domain i).chart j).map.symm z) ∈ V →
      F.parametrization i (((F.domain i).chart j).map.symm z) ≠ x →
      E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j z) ∈ c.chart.source →
      (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z).toLinearMap.range =
      (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization k) l)
        ((F.domain k).chart l).map.target w).toLinearMap.range)
    (hregularSeam : ∀ (P : E3 →L[ℝ] E2) (z : S), z ∈ V → z ≠ x → z ∈ F.seam.carrier →
      E.toSphere (F.map z) ∈ c.chart.source →
      (∀ i j y, y ∈ ((F.domain i).chart j).map.target →
        sectorCoordinateMap (F.map ∘ F.parametrization i) j y = F.map z →
        Function.Bijective (P.comp (fderivWithin ℝ
          (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
          ((F.domain i).chart j).map.target y))) →
      IsLocalHomeomorphOn (P ∘ c.chart ∘ E.toSphere ∘ F.map) {z}) :
    ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source ∧ C.chart.source ⊆ V := by
  obtain ⟨P, height, hsep, U, hU, hxU, hmaps, hp, hh, hinj, htrans, hfiber⟩ :=
    native_projection_isolated_fiber_all_charts E F x c hc
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have hxint : x ∈ (𝓡∂ 2).interior S :=
    ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mpr (hVboundary hxV)
  have hlocal : IsLocalHomeomorphOn (P ∘ c.chart ∘ E.toSphere ∘ F.map) (W \ {x}) := by
    intro z hz
    by_cases hs : z ∈ F.seam.carrier
    · exact hregularSeam P z hz.1.2 hz.2 hs (hmaps hz.1.1)
        (htrans z hz.1.1) z (mem_singleton z)
    · exact native_off_seam_projection_local_homeomorph E F z
        (fun hm => hm.elim hs (hVboundary hz.1.2)) c (hmaps hz.1.1) P
        (htrans z hz.1.1) z (mem_singleton z)
  have hcenter := native_interior_projection_across_vertex S x hxint
    (P ∘ c.chart ∘ E.toSphere ∘ F.map) W hW hxW
    (hp.mono inter_subset_left) (fun z hz he => hfiber z hz.1 he) hlocal
    (height ∘ c.chart ∘ E.toSphere ∘ F.map) (hh.mono inter_subset_left)
    (hinj.mono inter_subset_left)
  obtain ⟨e, hxe, he⟩ := hcenter x (mem_singleton x)
  let er := e.restrOpen W hW
  have hxer : x ∈ er.source := ⟨hxe, hxW⟩
  have her (z : S) : er z = P (c.chart (E.toSphere (F.map z))) := congrFun he.symm z
  have hm : MapsTo (E.toSphere ∘ F.map) er.source c.chart.source := fun z hz => hmaps hz.2.1
  obtain ⟨C, hxC, hC⟩ := native_vertex_chart_from_punctured_image_charts E F h x c P height hsep
    er hxer (hVboundary hxV) her hm
    (fun i j z hz hzs => htrans _ hzs.2.1 i j z hz rfl)
    (fun i j k l z w hz hw heq hzs hne => htangent i j k l z w hz hw heq hzs.2.2 hne
      (hm hzs)) hpieces (fun z hz hne => hcover z hz.2.2 hne)
  exact ⟨C, hxC, fun z hz => (hC hz).2.2⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
