import A5NativeProjectionAllCharts
import A5InteriorInvarianceOfDomain
import AreaSectorInteriorSupport

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- A transverse projection is a local homeomorphism at an actual interior
point of a native piece. The source neighborhood is taken in the whole
surface and its openness comes from the native component condition. -/
theorem native_piece_interior_projection_local_homeomorph
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (y : Euc 2)
    (hy : y ∈ interior ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j y) ∈ c.chart.source)
    (P : Euc 3 →L[ℝ] Euc 2)
    (hP : Function.Bijective (P.comp (fderivWithin ℝ
      (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target y))) :
    IsLocalHomeomorphOn (P ∘ c.chart ∘ E.toSphere ∘ F.map)
      {F.parametrization i (((F.domain i).chart j).map.symm y)} := by
  let b := ((F.domain i).chart j).map
  let H := c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j
  let a := b.symm y
  let x := F.parametrization i a
  have hyb : y ∈ b.target := interior_subset hy
  have ha : a ∈ (F.domain i).interior ∩ b.source :=
    AreaCertificates.sector_chart_inverse_interior (F.domain i) j hy
  obtain ⟨hH, _⟩ := native_piece_chart_C1_rank_at E F i j y hyb c hc
  have hHAt : ContDiffAt ℝ 1 H y := hH.contDiffAt (mem_interior_iff_mem_nhds.mp hy)
  have hd : fderivWithin ℝ H b.target y = fderiv ℝ H y :=
    fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hy)
  have hPH : ContDiffAt ℝ 1 (P ∘ H) y := P.contDiff.contDiffAt.comp y hHAt
  have hPD : Function.Bijective (fderiv ℝ (P ∘ H) y) := by
    rw [(P.hasFDerivAt.comp y (hHAt.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    change Function.Bijective (P.comp (fderivWithin ℝ H b.target y)) at hP
    rwa [hd] at hP
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ (P ∘ H) y)
    (LinearMap.ker_eq_bot.mpr hPD.1) (LinearMap.range_eq_top.mpr hPD.2)
  have hder : HasFDerivAt (P ∘ H) (L : Euc 2 →L[ℝ] Euc 2) y :=
    (hPH.differentiableAt (by norm_num)).hasFDerivAt
  let e := hPH.toOpenPartialHomeomorph (P ∘ H) hder (by norm_num)
  have hey : y ∈ e.source := hPH.mem_toOpenPartialHomeomorph_source hder (by norm_num)
  let Q := (F.domain i).interior ∩ b.source ∩ b ⁻¹' e.source ∩
    (E.toSphere ∘ F.map ∘ F.parametrization i) ⁻¹' c.chart.source
  have hQ : IsOpen Q := by
    apply IsOpen.inter
    · simpa only [CompactSectorPiece.interior, inter_assoc] using
        (AreaCertificates.sector_piece_boundary_closed (F.domain i)).isOpen_compl.inter
          (b.continuousOn.isOpen_inter_preimage ((F.domain i).chart j).source_open e.open_source)
    · exact c.chart.open_source.preimage
        (continuous_subtype_val.comp (F.piece_topological_embedding i).continuous)
  have haQ : a ∈ Q := by
    refine ⟨⟨ha, ?_⟩, hc⟩
    change b (b.symm y) ∈ e.source
    rw [b.right_inv hyb]
    exact hey
  obtain ⟨V, hV, hpre⟩ := (F.parametrization_embedding i).isInducing.isOpen_iff.mp hQ
  let U := F.parametrization i '' (F.domain i).interior ∩ V
  have hU : IsOpen U := (AreaCertificates.geometric_piece_interior_image_open F i).inter hV
  have hxU : x ∈ U := ⟨⟨a, ha.1, rfl⟩, by change a ∈ (F.parametrization i) ⁻¹' V; rw [hpre]; exact haQ⟩
  have hlocal (z : S) (hz : z ∈ U) : ∃ v ∈ Q, F.parametrization i v = z := by
    obtain ⟨v, _, hv⟩ := hz.1
    exact ⟨v, by rw [← hpre]; change F.parametrization i v ∈ V; rw [hv]; exact hz.2, hv⟩
  have hmap : MapsTo (E.toSphere ∘ F.map) U c.chart.source := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hlocal z hz
    exact hv.2
  have hcont : ContinuousOn (P ∘ c.chart ∘ E.toSphere ∘ F.map) U :=
    P.continuous.comp_continuousOn (c.chart.continuousOn.comp
      (continuous_subtype_val.comp F.map.continuous).continuousOn hmap)
  have hinj : InjOn (P ∘ c.chart ∘ E.toSphere ∘ F.map) U := by
    intro z hz w hw he
    obtain ⟨v, hv, rfl⟩ := hlocal z hz
    obtain ⟨t, ht, rfl⟩ := hlocal w hw
    have hev : e (b v) = P (c.chart (E.toSphere (F.map (F.parametrization i v)))) := by
      change P (H (b v)) = _
      dsimp [H, sectorCoordinateMap]
      rw [b.left_inv hv.1.1.2]
    have het : e (b t) = P (c.chart (E.toSphere (F.map (F.parametrization i t)))) := by
      change P (H (b t)) = _
      dsimp [H, sectorCoordinateMap]
      rw [b.left_inv ht.1.1.2]
    have hvt := b.injOn hv.1.1.2 ht.1.1.2
      (e.injOn hv.1.2 ht.1.2 (by rw [hev, het]; exact he))
    rw [hvt]
  have hx : x ∈ (𝓡∂ 2).interior S :=
    ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mpr
      (AreaCertificates.sector_source_point_avoids_boundary F i j hy)
  exact native_interior_local_homeomorph_of_injective S x hx U hU hxU _ hcont hinj

/-- Away from the actual seam and actual source boundary, the native cover
provides an interior piece chart. Thus the common projection is already a
local homeomorphism there, without an A2 or minimality premise. -/
theorem native_off_seam_projection_local_homeomorph
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (x : S) (hx : x ∉ F.seam.carrier ∪ S.boundary)
    (c : SmoothAmbientChart ThreeSphere) (hc : E.toSphere (F.map x) ∈ c.chart.source)
    (P : Euc 3 →L[ℝ] Euc 2)
    (htrans : ∀ i j y, y ∈ ((F.domain i).chart j).map.target →
      sectorCoordinateMap (F.map ∘ F.parametrization i) j y = F.map x →
      Function.Bijective (P.comp (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target y))) :
    IsLocalHomeomorphOn (P ∘ c.chart ∘ E.toSphere ∘ F.map) {x} := by
  have hxcover : x ∈ ⋃ i, range (F.parametrization i) := by rw [F.covers]; trivial
  obtain ⟨i, a, ha⟩ := mem_iUnion.mp hxcover
  have hai : a ∈ (F.domain i).interior := by
    intro hb
    exact hx (ha ▸ F.piece_boundary i ⟨a, hb, rfl⟩)
  have hacover : a ∈ ⋃ j, ((F.domain i).chart j).map.source := by rw [(F.domain i).covers]; trivial
  obtain ⟨j, haj⟩ := mem_iUnion.mp hacover
  let y := ((F.domain i).chart j).map a
  have hy : y ∈ interior ((F.domain i).chart j).map.target := by
    rw [← AreaCertificates.sector_chart_piece_interior]
    exact ⟨a, ⟨hai, haj⟩, rfl⟩
  have heq : sectorCoordinateMap (F.map ∘ F.parametrization i) j y = F.map x := by
    dsimp [sectorCoordinateMap, y]
    rw [((F.domain i).chart j).map.left_inv haj, ha]
  have hroot := native_piece_interior_projection_local_homeomorph E F i j y hy c
    (by rw [heq]; exact hc) P (htrans i j y (interior_subset hy) heq)
  simpa only [y, ((F.domain i).chart j).map.left_inv haj, ha] using hroot

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
