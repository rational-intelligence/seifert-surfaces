import A5NativeInteriorDensity
import A5GraphMinimalityClosure

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- Smoothness obtained by regularity preserves actual metric minimality
across any closed exceptional set whose complement is dense. -/
theorem native_metric_graph_minimal_on_open_of_dense
    {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] {h : AmbientMetric N}
    (G : NativeMetricGraph h) (U W : Set E2) (hU : IsOpen U) (hUG : U ⊆ G.disc)
    (hW : W ⊆ U) (hdense : U ⊆ closure W) (hsmooth : ContDiffOn ℝ ∞ G.height U)
    (hminimal : IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) W) :
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) U := by
  obtain ⟨hgs, hsymm, hpos⟩ := native_graph_actual_chart_metric G
  let g : CoordinateMetric G.coordinates.chart.target :=
    ⟨actualChartTensor h G.coordinates, hgs, hsymm, hpos⟩
  let Φ := graphMap G.origin G.plane G.normal G.height
  have hΦ : ContDiffOn ℝ ∞ Φ U :=
    (contDiffOn_const.add G.plane.contDiff.contDiffOn).add (hsmooth.smul_const G.normal)
  obtain ⟨P, hP, hn⟩ := native_metric_graph_exists_projection G
  apply coordinate_minimality_of_dense_projected_patch G.coordinates.chart.target
    G.coordinates.chart.open_target g U W hU hW hdense Φ hΦ
    (fun x hx => G.graph_in_chart (by
      have hh : dist x 0 < G.radius := hUG hx
      change dist x 0 ≤ 2 * G.radius
      linarith [G.radius_pos])) P _ hminimal
  intro x hx
  have hu := (hsmooth.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hd : HasFDerivAt Φ (G.plane + (fderiv ℝ G.height x).smulRight G.normal) x :=
    (G.plane.hasFDerivAt.const_add G.origin).add (hu.hasFDerivAt.smul_const G.normal)
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  change P (G.plane v + fderiv ℝ G.height x v • G.normal) = v
  rw [map_add, map_smul, hP, hn, smul_zero, add_zero]

/-- Once the native graph is smooth on an open region, piece minimality
forces its minimality throughout that region, including all seams. The
required dense open set is constructed from the native finite-piece cover. -/
theorem native_metric_graph_minimal_on_open_of_pieces
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
    (U : Set E2) (hU : IsOpen U) (hUG : U ⊆ G.disc)
    (hUe : ∀ y ∈ U, a + y ∈ e.target)

    (hgraph : ∀ y ∈ U, graphMap G.origin G.plane G.normal G.height y =
      G.coordinates.chart (E.toSphere (F.map (e.symm (a + y)))))
    (hsmooth : ContDiffOn ℝ ∞ G.height U) :
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) U := by
  let W := {y ∈ U | e.symm (a + y) ∉ F.seam.carrier ∪ S.boundary}
  have hoffopen : IsOpen (F.seam.carrier ∪ S.boundary)ᶜ :=
    ((AreaCertificates.geometric_seam_carrier_closed F).union
      ((𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by simp))).isOpen_compl
  have hW : IsOpen W :=
    (e.symm.continuousOn.comp (continuousOn_const.add continuousOn_id) hUe).isOpen_inter_preimage
      hU hoffopen
  have hminimal := (native_graph_smooth_minimal_off_seam E F h G e P a he ha hmaps
    hpieces htrans W hW (fun y hy => hUe y hy.1) (fun y hy => hy.2)
    (fun y hy => hgraph y hy.1)).2
  exact native_metric_graph_minimal_on_open_of_dense G U W hU hUG
    (fun _ hy => hy.1) (native_projected_piece_interiors_dense F e a U hU hUe) hsmooth hminimal

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
