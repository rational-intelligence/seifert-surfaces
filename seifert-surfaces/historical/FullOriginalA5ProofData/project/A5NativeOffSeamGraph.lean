import A5NativePieceGraphRegularity

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

theorem native_piece_chart_interior_image_open
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) :
    IsOpen (F.parametrization i '' ((F.domain i).interior ∩ ((F.domain i).chart j).map.source)) := by
  have hQ : IsOpen ((F.domain i).interior ∩ ((F.domain i).chart j).map.source) :=
    (AreaCertificates.sector_piece_boundary_closed (F.domain i)).isOpen_compl.inter
      ((F.domain i).chart j).source_open
  obtain ⟨V, hV, hpre⟩ := (F.parametrization_embedding i).isInducing.isOpen_iff.mp hQ
  have heq : F.parametrization i '' ((F.domain i).interior ∩ ((F.domain i).chart j).map.source) =
      (F.parametrization i '' (F.domain i).interior) ∩ V := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
      change z ∈ F.parametrization i ⁻¹' V
      rw [hpre]
      exact hz
    · rintro ⟨⟨z, _, rfl⟩, hzV⟩
      refine ⟨z, ?_, rfl⟩
      rw [← hpre]
      exact hzV
  rw [heq]
  exact (AreaCertificates.geometric_piece_interior_image_open F i).inter hV

/-- The literal finite native cover constructs the local piece and chart
around every point off the seam. Together with actual piece minimality,
this gives smoothness and minimality on the full off-seam graph region. -/
theorem native_graph_smooth_minimal_off_seam
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : AmbientMetric ThreeSphere) (G : NativeMetricGraph h)
    (e : OpenPartialHomeomorph S E2) (P : E3 →L[ℝ] E2) (a : E2)
    (he : ∀ x ∈ e.source, e x = P (G.coordinates.chart (E.toSphere (F.map x))))
    (ha : P G.origin = a)
    (hmaps : MapsTo (E.toSphere ∘ F.map) e.source G.coordinates.chart.source)
    (hpieces : ∀ i j, IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target))
    (htrans : ∀ i j z, z ∈ interior ((F.domain i).chart j).map.target →
      F.parametrization i (((F.domain i).chart j).map.symm z) ∈ e.source →
      Function.Bijective (P.comp (fderivWithin ℝ
        (G.coordinates.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z)))
    (U : Set E2) (hU : IsOpen U)
    (hUe : ∀ y ∈ U, a + y ∈ e.target)
    (hoff : ∀ y ∈ U, e.symm (a + y) ∉ F.seam.carrier ∪ S.boundary)
    (hgraph : ∀ y ∈ U, graphMap G.origin G.plane G.normal G.height y =
      G.coordinates.chart (E.toSphere (F.map (e.symm (a + y))))) :
    ContDiffOn ℝ ∞ G.height U ∧
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) U := by
  have hlocal (y : E2) (hy : y ∈ U) : ∃ V : Set E2, IsOpen V ∧ y ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ G.height V ∧
      IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
        (graphMap G.origin G.plane G.normal G.height) V := by
    have hcover : e.symm (a + y) ∈ ⋃ i, range (F.parametrization i) := by rw [F.covers]; trivial
    obtain ⟨i, v, hv⟩ := mem_iUnion.mp hcover
    have hvi : v ∈ (F.domain i).interior := by
      intro hb
      exact hoff y hy (hv ▸ F.piece_boundary i ⟨v, hb, rfl⟩)
    have hjcover : v ∈ ⋃ j, ((F.domain i).chart j).map.source := by
      rw [(F.domain i).covers]
      trivial
    obtain ⟨j, hvj⟩ := mem_iUnion.mp hjcover
    let A := F.parametrization i '' ((F.domain i).interior ∩ ((F.domain i).chart j).map.source)
    have hA : IsOpen A := native_piece_chart_interior_image_open F i j
    let V := U ∩ (fun z => e.symm (a + z)) ⁻¹' A
    have hV : IsOpen V :=
      (e.symm.continuousOn.comp (continuousOn_const.add continuousOn_id) hUe).isOpen_inter_preimage hU hA
    have hyv : y ∈ V := ⟨hy, ⟨v, ⟨hvi, hvj⟩, hv⟩⟩
    have hp := native_graph_regular_minimal_on_piece_interior E F h G e P a he ha hmaps
      i j (hpieces i j) (htrans i j) V hV (fun z hz => hUe z hz.1)
      (fun z hz => hz.2) (fun z hz => hgraph z hz.1)
    exact ⟨V, hV, hyv, inter_subset_left, hp.1, hp.2⟩
  have hs : ContDiffOn ℝ ∞ G.height U := by
    intro y hy
    obtain ⟨V, hV, hyv, _, hheight, _⟩ := hlocal y hy
    exact (hheight.contDiffAt (hV.mem_nhds hyv)).contDiffWithinAt
  refine ⟨hs, ?_, ?_⟩
  · exact (contDiffOn_const.add G.plane.contDiff.contDiffOn).add (hs.smul_const G.normal)
  · intro y hy
    obtain ⟨V, _, hyv, _, _, hmin⟩ := hlocal y hy
    exact hmin.2 y hyv

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
