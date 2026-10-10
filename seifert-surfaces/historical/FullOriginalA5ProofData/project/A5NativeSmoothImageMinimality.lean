import A5NativeSmoothPieceMinimality
import A5NativeInteriorDensity
import A5RegularMinimalityClosure

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- Every actual smooth regular plane chart of the native piecewise image
is minimal in every ambient chart. Native piece minimality suffices; neither
seam minimality nor a preferred transverse projection is supplied. -/
theorem native_smooth_image_chart_minimal_of_pieces
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (h : AmbientMetric ThreeSphere) (e : OpenPartialHomeomorph S E2)
    (U : Set E2) (hU : IsOpen U) (hUe : U ⊆ e.target)
    (hf : ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞ (F.map ∘ e.symm) U)
    (hrank : ∀ x ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ, E2) (𝓡∂ 3) (F.map ∘ e.symm) x))
    (hpieces : ∀ i j, IsMinimalPatch h
      (E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      (interior ((F.domain i).chart j).map.target)) :
    IsMinimalPatch h (E.toSphere ∘ F.map ∘ e.symm) U := by
  have hinc : Manifold.IsImmersion (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := by
    let : ChartedSpace (EuclideanHalfSpace 3) T.Carrier := E.charted
    let : IsManifold (𝓡∂ 3) ∞ T.Carrier := E.smooth
    exact E.inclusion.isImmersion
  refine ⟨hinc.contMDiff.comp_contMDiffOn hf, ?_, ?_⟩
  · intro x hx
    rw [mfderiv_comp x (hinc.contMDiff.mdifferentiable (by simp) _)
      ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))]
    exact (hinc.mfderiv_injective (by simp) _).comp (hrank x hx)
  · intro c
    let V := U ∩ (E.toSphere ∘ F.map ∘ e.symm) ⁻¹' c.chart.source
    have hV : IsOpen V :=
      (hinc.contMDiff.comp_contMDiffOn hf).continuousOn.isOpen_inter_preimage hU c.chart.open_source
    let W := {y ∈ V | e.symm y ∉ F.seam.carrier ∪ S.boundary}
    have hdense : V ⊆ closure W := by
      simpa only [zero_add] using native_projected_piece_interiors_dense F e 0 V hV
        (fun y hy => by simpa only [zero_add] using hUe hy.1)
    obtain ⟨hfs, hfr⟩ := native_sphere_coordinate_smooth_rank E (F.map ∘ e.symm) V hV
      (hf.mono inter_subset_left) (fun y hy => hrank y hy.1) c (fun y hy => hy.2)
    have hminW : IsMinimalParametrizationOn (actualChartTensor h c)
        (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) W := by
      refine ⟨hfs.mono (fun y hy => hy.1), ?_⟩
      intro y hy
      have hcover : e.symm y ∈ ⋃ i, range (F.parametrization i) := by rw [F.covers]; trivial
      obtain ⟨i, v, hv⟩ := mem_iUnion.mp hcover
      have hvi : v ∈ (F.domain i).interior := by
        intro hb
        exact hy.2 (hv ▸ F.piece_boundary i ⟨v, hb, rfl⟩)
      have hjcover : v ∈ ⋃ j, ((F.domain i).chart j).map.source := by
        rw [(F.domain i).covers]
        trivial
      obtain ⟨j, hvj⟩ := mem_iUnion.mp hjcover
      let A := F.parametrization i '' ((F.domain i).interior ∩ ((F.domain i).chart j).map.source)
      have hA : IsOpen A := native_piece_chart_interior_image_open F i j
      let B := V ∩ e.symm ⁻¹' A
      have hB : IsOpen B :=
        (e.symm.continuousOn.mono (fun _ hz => hUe hz.1)).isOpen_inter_preimage hV hA
      have hyB : y ∈ B := ⟨hy.1, ⟨v, ⟨hvi, hvj⟩, hv⟩⟩
      have hm := native_smooth_image_minimal_on_piece_interior E F h e B hB
        (fun z hz => hUe hz.1.1) (hf.mono (fun z hz => hz.1.1))
        (fun z hz => hrank z hz.1.1) i j (hpieces i j) (fun z hz => hz.2) c
        (fun z hz => hz.1.2)
      exact hm.2 y hyB
    obtain ⟨hgs, hsymm, hpos⟩ :=
      SeifertSurfaces.OriginalEndpoints.A4GeometryBridges.actual_chart_tensor_metric_properties h c
    let g : CoordinateMetric c.chart.target := ⟨actualChartTensor h c, hgs, hsymm, hpos⟩
    exact coordinate_minimality_of_dense_regular_patch c.chart.target c.chart.open_target g
      V W hV hdense (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) hfs
      (fun z hz => c.chart.map_source hz.2) hfr hminW

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
