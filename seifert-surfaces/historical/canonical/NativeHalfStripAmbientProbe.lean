import NativeHalfStripTopologyProbe
import CoreClockClosureProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

theorem native_halfstrip_source_in_chart
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    {q : SeamLocalTime → Euc 2} (H : NativeSeamHalfStrip E F i j q)
    (z : ℝ × ℝ) (hz : z ∈ nativeHalfStripDomain H.height) :
    nativeHalfStripSource E F i j H z ∈ F.parametrization i '' ((F.domain i).chart j).map.source :=
  ⟨_, ((F.domain i).chart j).map.map_target (H.maps_to_sector hz), rfl⟩

theorem native_halfstrip_other_piece_forces_zero_height
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i k : Fin F.pieceCount) (hik : i ≠ k) (j : Fin (F.domain i).count)
    {q : SeamLocalTime → Euc 2} (H : NativeSeamHalfStrip E F i j q)
    (z : ℝ × ℝ) (hz : z ∈ nativeHalfStripDomain H.height)
    (hk : nativeHalfStripSource E F i j H z ∈ range (F.parametrization k)) : z.2 = 0 := by
  have hzcut : nativeHalfStripSource E F i j H z ∈ F.seam.carrier ∪ S.boundary :=
    native_distinct_piece_intersection_subset_cut E F i k hik ⟨⟨_, rfl⟩, hk⟩
  by_contra hn
  have hpos : 0 < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm hn)
  exact native_piece_interior_avoids_cut E F i
    ⟨_, H.positive_piece_interior ⟨hz.1, hpos, hz.2.2⟩, rfl⟩ hzcut

/-- Full ambient neighbourhood geometry of the two actual native
halfstrips: exact chart cover, exact common edge and whole-piece incidence. -/
theorem native_halfstrips_actual_ambient_window
    (S : CompactOrientedSurface.{u}) (F : GeometricPiecewiseSurface S E.Carrier)
    (i k : Fin F.pieceCount) (hik : i ≠ k)
    (j : Fin (F.domain i).count) (l : Fin (F.domain k).count)
    (q r : SeamLocalTime → Euc 2)
    (H : NativeSeamHalfStrip E F i j q) (J : NativeSeamHalfStrip E F k l r)
    (hheight : H.height = J.height)
    (γ : ℝ → ThreeSphere) (hγ : IsEmbedding (fun t : SeamLocalTime => γ t))
    (hq : ∀ t, pieceSphereCoordinate E F i j (q t) = γ t)
    (hr : ∀ t, pieceSphereCoordinate E F k l (r t) = γ t) :
    ∃ N : Set ThreeSphere, IsOpen N ∧ γ 0 ∈ N ∧
      E.toSphere '' F.image ∩ N =
        ((E.toSphere ∘ F.map ∘ F.parametrization i) '' ((F.domain i).chart j).map.source ∪
         (E.toSphere ∘ F.map ∘ F.parametrization k) '' ((F.domain k).chart l).map.source) ∩ N ∧
      (((E.toSphere ∘ F.map ∘ F.parametrization i) '' ((F.domain i).chart j).map.source ∩
         (E.toSphere ∘ F.map ∘ F.parametrization k) '' ((F.domain k).chart l).map.source) ∩ N =
        (γ '' Ioo (-1 : ℝ) 1) ∩ N) ∧
      ∀ t : SeamLocalTime, ∀ a : Fin F.pieceCount,
        F.parametrization i (((F.domain i).chart j).map.symm (q t)) ∈
          range (F.parametrization a) ↔ a = i ∨ a = k := by
  let f := nativeHalfStripSource E F i j H
  let g := nativeHalfStripSource E F k l J
  let U := f '' nativeHalfStripDomain H.height ∪ g '' nativeHalfStripDomain J.height
  have hU : IsOpen U := native_halfstrips_actual_open_union E S F i k hik j l q r H J
    hheight _ hγ.injective hq hr
  let A := E.toSphere ∘ F.map
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hA : IsEmbedding A := hinc.isEmbedding.comp F.embedding
  let t0 : SeamLocalTime := ⟨0, neg_one_lt_zero, zero_lt_one⟩
  let x0 := f (0, 0)
  have hx0 : x0 ∈ U := Or.inl ⟨(0, 0), ⟨t0.property, le_rfl, H.height_pos⟩, rfl⟩
  have hAx0 : A x0 = γ 0 := by
    rw [show x0 = nativeHalfStripSource E F i j H (t0, 0) from rfl,
      native_halfstrip_source_boundary E F i j H t0]
    exact hq t0
  obtain ⟨N, hN, hxN, _, hpre, _⟩ := A3GraphLower.embedding_ambient_open_source_isolation
    A hA x0 U hU hx0 univ isOpen_univ (mem_univ _)
  have hcInc := native_two_piece_open_cover_excludes_others E F i k U hU
    (by
      rintro x (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr ⟨_, rfl⟩)
  have hcommon (t : SeamLocalTime) :
      F.parametrization i (((F.domain i).chart j).map.symm (q t)) =
        F.parametrization k (((F.domain k).chart l).map.symm (r t)) :=
    hA.injective ((hq t).trans (hr t).symm)
  have hqU (t : SeamLocalTime) : F.parametrization i (((F.domain i).chart j).map.symm (q t)) ∈ U := by
    apply Or.inl
    refine ⟨(t, 0), ⟨t.property, le_rfl, H.height_pos⟩, ?_⟩
    exact native_halfstrip_source_boundary E F i j H t
  refine ⟨N, hN, by rwa [hAx0] at hxN, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨⟨z, ⟨x, rfl⟩, rfl⟩, hyN⟩
      have hxU := hpre hyN
      refine ⟨?_, hyN⟩
      rcases hxU with ⟨z, hz, hzx⟩ | ⟨z, hz, hzx⟩
      · obtain ⟨p, hp, hpx⟩ := native_halfstrip_source_in_chart E F i j H z hz
        exact Or.inl ⟨p, hp, congrArg A (hpx.trans hzx)⟩
      · obtain ⟨p, hp, hpx⟩ := native_halfstrip_source_in_chart E F k l J z hz
        exact Or.inr ⟨p, hp, congrArg A (hpx.trans hzx)⟩
    · rintro ⟨(⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩), hyN⟩
      · exact ⟨⟨_, ⟨_, rfl⟩, rfl⟩, hyN⟩
      · exact ⟨⟨_, ⟨_, rfl⟩, rfl⟩, hyN⟩
  · ext y
    constructor
    · rintro ⟨⟨⟨p, hp, hpy⟩, ⟨w, hw, hwy⟩⟩, hyN⟩
      have he : F.parametrization i p = F.parametrization k w := hA.injective (hpy.trans hwy.symm)
      have hxU : F.parametrization i p ∈ U := hpre (by
        change A (F.parametrization i p) ∈ N
        rw [show A (F.parametrization i p) = y from hpy]
        exact hyN)
      refine ⟨?_, hyN⟩
      rcases hxU with ⟨z, hz, hzx⟩ | ⟨z, hz, hzx⟩
      · have hz0 := native_halfstrip_other_piece_forces_zero_height E F i k hik j H z hz
          ⟨w, he.symm.trans hzx.symm⟩
        have hzero : z = (z.1, 0) := Prod.ext rfl hz0
        refine ⟨z.1, hz.1, ?_⟩
        dsimp only [f] at hzx
        rw [hzero, native_halfstrip_source_boundary E F i j H ⟨z.1, hz.1⟩] at hzx
        exact (hq ⟨z.1, hz.1⟩).symm.trans (congrArg A hzx |>.trans hpy)
      · have hz0 := native_halfstrip_other_piece_forces_zero_height E F k i (Ne.symm hik) l J z hz
          ⟨p, hzx.symm⟩
        have hzero : z = (z.1, 0) := Prod.ext rfl hz0
        refine ⟨z.1, hz.1, ?_⟩
        dsimp only [g] at hzx
        rw [hzero, native_halfstrip_source_boundary E F k l J ⟨z.1, hz.1⟩] at hzx
        exact (hr ⟨z.1, hz.1⟩).symm.trans (congrArg A hzx |>.trans hpy)
    · rintro ⟨⟨t, ht, rfl⟩, hyN⟩
      have htH : (t, 0) ∈ nativeHalfStripDomain H.height := ⟨ht, le_rfl, H.height_pos⟩
      have htJ : (t, 0) ∈ nativeHalfStripDomain J.height := ⟨ht, le_rfl, J.height_pos⟩
      refine ⟨⟨?_, ?_⟩, hyN⟩
      · refine ⟨_, ?_, hq ⟨t, ht⟩⟩
        rw [H.exact_boundary_lift ⟨t, ht⟩]
        exact ((F.domain i).chart j).map.map_target (H.maps_to_sector htH)
      · refine ⟨_, ?_, hr ⟨t, ht⟩⟩
        rw [J.exact_boundary_lift ⟨t, ht⟩]
        exact ((F.domain k).chart l).map.map_target (J.maps_to_sector htJ)
  · intro t a
    constructor
    · exact hcInc _ (hqU t) a
    · rintro (rfl | rfl)
      · exact ⟨_, rfl⟩
      · exact ⟨_, (hcommon t).symm⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
