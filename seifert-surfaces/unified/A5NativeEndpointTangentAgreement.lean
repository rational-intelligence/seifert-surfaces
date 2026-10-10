import A5NativeIncidentCoordinateFields
import A5NativeProjectionAllCharts

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- A native finite sector surface whose punctured neighborhood already has
smooth image charts has a single actual tangent plane at the puncture. This
holds at boundary endpoints as well as interior vertices, without assuming
that the whole neighborhood is already a graph. -/
theorem native_incident_tangents_agree_at_punctured_image_endpoint
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (x : S) (V : Set S) (hV : IsOpen V) (hxV : x ∈ V)
    (hcover : ∀ y ∈ V, y ≠ x → ∃ C : SmoothImageChart S F.map, y ∈ C.chart.source)
    (c : SmoothAmbientChart ThreeSphere) (hc : E.toSphere (F.map x) ∈ c.chart.source) :
    ∀ i j k l z w,
      z ∈ ((F.domain i).chart j).map.target →
      w ∈ ((F.domain k).chart l).map.target →
      F.parametrization i (((F.domain i).chart j).map.symm z) = x →
      F.parametrization k (((F.domain k).chart l).map.symm w) = x →
      (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z).toLinearMap.range =
      (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization k) l)
        ((F.domain k).chart l).map.target w).toLinearMap.range := by
  classical
  obtain ⟨P, height, hsep, U, hU, hxU, hmaps, hp, hh, hinj, htrans, hfiber⟩ :=
    native_projection_isolated_fiber_all_charts E F x c hc
  let I := {i : Fin F.pieceCount // x ∈ range (F.parametrization i)}
  choose a ha using fun i : I => i.property
  have hex (i : I) : ∃ j, a i ∈ ((F.domain i.val).chart j).map.source := by
    have h : a i ∈ ⋃ j, ((F.domain i.val).chart j).map.source := by
      rw [(F.domain i.val).covers]; trivial
    exact mem_iUnion.mp h
  choose j hj using hex
  have hfields (i : I) := native_incident_differential_field E F i.val (j i) (a i) (hj i) c
    (by rw [ha i]; exact hc)
  choose Ui hUi hxi q hqa hqm hqe hDc using hfields
  have hxi' (i : I) : x ∈ Ui i := ha i ▸ hxi i
  obtain ⟨U₀,hU₀,hxU₀,havoid,_,_⟩ := native_incident_sector_chart_neighborhood F x
  let W := ((U ∩ V) ∩ U₀) ∩ ⋂ i, Ui i
  have hW : IsOpen W := ((hU.inter hV).inter hU₀).inter (isOpen_iInter_of_finite hUi)
  have hxW : x ∈ W := ⟨⟨⟨hxU,hxV⟩,hxU₀⟩,mem_iInter.mpr hxi'⟩
  obtain ⟨A,hAn,hAc,hAW⟩ := exists_mem_nhds_isClosed_subset (hW.mem_nhds hxW)
  let R (i : I) := range (F.parametrization i.val) ∩ A
  have hRsub (i : I) : R i ⊆ range (F.parametrization i.val) ∩ Ui i :=
    fun y hy => ⟨hy.1,mem_iInter.mp (hAW hy.2).2 i⟩
  have hRc (i : I) : IsClosed (R i) :=
    (isCompact_range (F.parametrization i.val).continuous).isClosed.inter hAc
  have hRcover : (⋃ i, R i) ∈ 𝓝 x := by
    apply mem_of_superset hAn
    intro y hy
    have h : y ∈ ⋃ i, range (F.parametrization i) := by rw [F.covers]; trivial
    obtain ⟨i,hi⟩ := mem_iUnion.mp h
    have hix : x ∈ range (F.parametrization i) := by
      by_contra hn
      have hem : y ∈ (∅ : Set S) := havoid i hn ▸ ⟨hi,(hAW hy).1.2⟩
      exact hem
    exact mem_iUnion.mpr ⟨⟨i,hix⟩,hi,hy⟩
  have hRx (i : I) : x ∈ R i := ⟨i.property,mem_of_mem_nhds hAn⟩
  have hRacc (i : I) : x ∈ closure (R i \ {x}) := by
    apply mem_closure_iff_nhds.mpr
    intro B hB
    obtain ⟨y,hyB,hyR,hyx⟩ := mem_closure_iff_nhds.mp
      (native_piece_image_point_accumulates F i.val x i.property) (B ∩ A) (inter_mem hB hAn)
    exact ⟨y,hyB.1,⟨hyR,hyB.2⟩,hyx⟩
  let D (i : I) (y : S) := fderivWithin ℝ
    (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i.val) (j i))
    ((F.domain i.val).chart (j i)).map.target (q i y)
  have hD (i : I) : ContinuousWithinAt (D i) (R i) x := by
    have hh := (hDc i).mono (hRsub i)
    rwa [ha i] at hh
  have hP (i : I) (y : S) (hy : y ∈ R i) : Function.Bijective (P.comp (D i y)) := by
    apply htrans y (hAW hy.2).1.1.1 i.val (j i) (q i y) (hqm i (hRsub i hy))
    change F.map (F.parametrization i.val (((F.domain i.val).chart (j i)).map.symm (q i y))) = F.map y
    rw [hqe i y (hRsub i hy)]
  have hmatch (i k : I) (y : S) (hi : y ∈ R i) (hk : y ∈ R k) (hne : y ≠ x) :
      (D i y).toLinearMap.range = (D k y).toLinearMap.range := by
    obtain ⟨C,hC⟩ := hcover y (hAW hi.2).1.1.2 hne
    have hqi := hRsub i hi
    have hqk := hRsub k hk
    apply native_incident_tangents_eq_of_smooth_image_chart E F C
      i.val (j i) k.val (j k) (q i y) (q k y) (hqm i hqi) (hqm k hqk)
      ((hqe i y hqi).trans (hqe k y hqk).symm)
    · rw [hqe i y hqi]; exact hC
    · change E.toSphere (F.map (F.parametrization i.val _)) ∈ c.chart.source
      rw [hqe i y hqi]
      exact hmaps (hAW hi.2).1.1.1
  have hsame := finite_native_incident_tangent_limits_agree S x R hRc hRcover hRx hRacc
    D hD P hP hmatch
  have hchoice (i : I) : q i x = ((F.domain i.val).chart (j i)).map (a i) := by
    have hh := hqa i
    rw [ha i] at hh
    exact hh
  have hcompare (i : I) (k : Fin (F.domain i.val).count) (z : Euc 2)
      (hz : z ∈ ((F.domain i.val).chart k).map.target)
      (hez : F.parametrization i.val (((F.domain i.val).chart k).map.symm z) = x) :
      (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i.val) k)
        ((F.domain i.val).chart k).map.target z).toLinearMap.range = (D i x).toLinearMap.range := by
    have hs : ((F.domain i.val).chart k).map.symm z = a i :=
      (F.parametrization_embedding i.val).injective (hez.trans (ha i).symm)
    have hak : a i ∈ ((F.domain i.val).chart k).map.source :=
      hs ▸ ((F.domain i.val).chart k).map.map_target hz
    have hza : ((F.domain i.val).chart k).map (a i) = z := by
      rw [← hs]; exact ((F.domain i.val).chart k).map.right_inv hz
    have hcomp := native_piece_tangent_ranges_eq E F i.val k (j i) (a i) hak (hj i) c
      (by rw [ha i]; exact hc)
    dsimp only [D]
    rw [hchoice i]
    simpa only [hza] using hcomp
  intro i k m l z w hz hw hzx hwx
  let i' : I := ⟨i,⟨_,hzx⟩⟩
  let m' : I := ⟨m,⟨_,hwx⟩⟩
  exact (hcompare i' k z hz hzx).trans ((hsame i' m').trans (hcompare m' l w hw hwx).symm)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
