import A5NativeGraphOpenSides
import A5NativePieceProjectionGraph
import AreaSectorInteriorSupport

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- The native piece embedding constructs the continuous coordinate lift
on a graph side. Actual piece minimality then supplies both smoothness and
minimality of that same graph side. No derivative or regularity of the lift
is assumed. -/
theorem native_graph_regular_minimal_on_piece_interior
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : AmbientMetric ThreeSphere) (G : NativeMetricGraph h)
    (e : OpenPartialHomeomorph S E2) (P : E3 →L[ℝ] E2) (a : E2)
    (he : ∀ x ∈ e.source, e x = P (G.coordinates.chart (E.toSphere (F.map x))))
    (ha : P G.origin = a)
    (hmaps : MapsTo (E.toSphere ∘ F.map) e.source G.coordinates.chart.source)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (hminimal : IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target))
    (htrans : ∀ z ∈ interior ((F.domain i).chart j).map.target,
      F.parametrization i (((F.domain i).chart j).map.symm z) ∈ e.source →
      Function.Bijective (P.comp (fderivWithin ℝ
        (G.coordinates.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z)))
    (U : Set E2) (hU : IsOpen U)
    (hUe : ∀ y ∈ U, a + y ∈ e.target)
    (hpiece : ∀ y ∈ U, e.symm (a + y) ∈ F.parametrization i ''
      ((F.domain i).interior ∩ ((F.domain i).chart j).map.source))
    (hgraph : ∀ y ∈ U, graphMap G.origin G.plane G.normal G.height y =
      G.coordinates.chart (E.toSphere (F.map (e.symm (a + y))))) :
    ContDiffOn ℝ ∞ G.height U ∧
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) U := by
  classical
  let b := ((F.domain i).chart j).map
  let Φ := E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j
  let Ω := interior b.target ∩ (F.parametrization i ∘ b.symm) ⁻¹' e.source
  have hΩ : IsOpen Ω :=
    ((F.parametrization i).continuous.comp_continuousOn
      (b.symm.continuousOn.mono interior_subset)).isOpen_inter_preimage
        isOpen_interior e.open_source
  have hex (y : E2) (hy : y ∈ U) : ∃ z ∈ interior b.target,
      sectorCoordinateMap (F.map ∘ F.parametrization i) j z = F.map (e.symm (a + y)) := by
    obtain ⟨v, hv, hvy⟩ := hpiece y hy
    refine ⟨b v, ?_, ?_⟩
    · rw [← AreaCertificates.sector_chart_piece_interior]
      exact ⟨v, hv, rfl⟩
    · change F.map (F.parametrization i (b.symm (b v))) = _
      rw [b.left_inv hv.2, hvy]
  let q (y : E2) := if hy : y ∈ U then (hex y hy).choose else 0
  have hq (y : E2) (hy : y ∈ U) : q y ∈ interior b.target ∧
      sectorCoordinateMap (F.map ∘ F.parametrization i) j (q y) = F.map (e.symm (a + y)) := by
    simpa only [q, dite_eq_left hy] using (hex y hy).choose_spec
  have hqs (y : E2) (hy : y ∈ U) : F.parametrization i (b.symm (q y)) = e.symm (a + y) :=
    F.embedding.injective (hq y hy).2
  have hqΩ : MapsTo q U Ω := by
    intro y hy
    refine ⟨(hq y hy).1, ?_⟩
    change F.parametrization i (b.symm (q y)) ∈ e.source
    rw [hqs y hy]
    exact e.map_target (hUe y hy)
  have hqcont : ContinuousOn q U :=
    continuous_coordinate_lift_of_embedded_image b (F.map ∘ F.parametrization i)
      (F.piece_topological_embedding i) U (fun y => F.map (e.symm (a + y))) q
      (F.map.continuous.comp_continuousOn (e.symm.continuousOn.comp
        (continuousOn_const.add continuousOn_id) hUe))
      (fun y hy => interior_subset (hq y hy).1) (fun y hy => (hq y hy).2)
  apply native_graph_open_side_of_continuous_lift G Φ (interior b.target) Ω U hΩ hU hminimal
    (fun z hz => ⟨hz.1, hmaps hz.2⟩) P q hqcont hqΩ
  · intro z hz
    have hC := (native_piece_chart_C1_rank_at E F i j z (interior_subset hz.1)
      G.coordinates (hmaps hz.2)).1
    have hd := (hC.contDiffAt (mem_interior_iff_mem_nhds.mp hz.1)).differentiableAt (by norm_num)
    have hfd : fderiv ℝ (fun y => P (G.coordinates.chart (Φ y) - G.origin)) z =
        P.comp (fderiv ℝ (G.coordinates.chart ∘ Φ) z) :=
      (P.hasFDerivAt.comp z (hd.hasFDerivAt.sub_const G.origin)).fderiv
    rw [hfd]
    change Function.Bijective (P.comp (fderiv ℝ (G.coordinates.chart ∘ Φ) z))
    have hD : fderivWithin ℝ (G.coordinates.chart ∘ Φ) b.target z =
        fderiv ℝ (G.coordinates.chart ∘ Φ) z :=
      fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hz.1)
    rw [← hD]
    exact htrans z hz.1 hz.2
  · intro y hy
    change P (G.coordinates.chart (E.toSphere
      (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q y))) - G.origin) = y
    rw [(hq y hy).2, map_sub, ← he _ (e.map_target (hUe y hy)), e.right_inv (hUe y hy), ha]
    abel
  · intro y hy
    change graphMap G.origin G.plane G.normal G.height y =
      G.coordinates.chart (E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q y)))
    rw [(hq y hy).2]
    exact hgraph y hy

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
