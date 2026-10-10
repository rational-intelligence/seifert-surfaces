import NativeHalfStripPackageProbe
import NativeIncidenceTwoUpperProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

def nativeHalfStripSource
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    {lift : SeamLocalTime → Euc 2} (H : NativeSeamHalfStrip E F i j lift) : ℝ × ℝ → S :=
  fun z => F.parametrization i (((F.domain i).chart j).map.symm
    (nativeHalfStripCoordinates H.origin H.tangent H.inward H.clock z))

theorem native_halfstrip_shorter_subset (h h' : ℝ) (hh : h ≤ h') :
    nativeHalfStripDomain h ⊆ nativeHalfStripDomain h' := by
  intro z hz
  exact ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 hh⟩

/-- A genuine native strip may be shortened in height, preserving every
approved field and its original boundary clock. -/
def nativeHalfStripShorten
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    {lift : SeamLocalTime → Euc 2} (H : NativeSeamHalfStrip E F i j lift)
    (h : ℝ) (hh : 0 < h) (hhH : h ≤ H.height) : NativeSeamHalfStrip E F i j lift := by
  have hsub := native_halfstrip_shorter_subset h H.height hhH
  refine {
    height := h
    height_pos := hh
    origin := H.origin
    tangent := H.tangent
    inward := H.inward
    tangent_unit := H.tangent_unit
    inward_unit := H.inward_unit
    frame_orthogonal := H.frame_orthogonal
    clock := H.clock
    clock_c1 := H.clock_c1
    clock_regular := H.clock_regular
    exact_boundary_lift := H.exact_boundary_lift
    planar_c1 := H.planar_c1.mono hsub
    planar_embedding := H.planar_embedding.comp (IsEmbedding.inclusion hsub)
    planar_rank := fun z hz => H.planar_rank z (hsub hz)
    maps_to_sector := H.maps_to_sector.mono_left hsub
    positive_sector_interior := ?_
    source_embedding := H.source_embedding.comp (IsEmbedding.inclusion hsub)
    positive_piece_interior := ?_
  }
  · exact H.positive_sector_interior.mono_left
      (fun z hz => ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 hhH⟩)
  · exact H.positive_piece_interior.mono_left
      (fun z hz => ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 hhH⟩)

theorem native_halfstrip_source_boundary
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    {lift : SeamLocalTime → Euc 2} (H : NativeSeamHalfStrip E F i j lift)
    (t : SeamLocalTime) :
    nativeHalfStripSource E F i j H (t, 0) =
      F.parametrization i (((F.domain i).chart j).map.symm (lift t)) := by
  unfold nativeHalfStripSource
  rw [← H.exact_boundary_lift]

/-- Distinct whole pieces and their exact common embedded seam clock prove
the cross-intersection condition required by the glued-strip theorem. -/
theorem native_halfstrips_cross_only_on_common_clock
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i k : Fin F.pieceCount) (hik : i ≠ k)
    (j : Fin (F.domain i).count) (l : Fin (F.domain k).count)
    (q r : SeamLocalTime → Euc 2)
    (H : NativeSeamHalfStrip E F i j q) (J : NativeSeamHalfStrip E F k l r)
    (γ : SeamLocalTime → ThreeSphere) (hγ : Function.Injective γ)
    (hq : ∀ t, pieceSphereCoordinate E F i j (q t) = γ t)
    (hr : ∀ t, pieceSphereCoordinate E F k l (r t) = γ t) :
    ∀ z ∈ nativeHalfStripDomain H.height, ∀ w ∈ nativeHalfStripDomain J.height,
      nativeHalfStripSource E F i j H z = nativeHalfStripSource E F k l J w →
        z.2 = 0 ∧ w.2 = 0 ∧ z.1 = w.1 := by
  intro z hz w hw he
  have hzcut : nativeHalfStripSource E F i j H z ∈ F.seam.carrier ∪ S.boundary :=
    native_distinct_piece_intersection_subset_cut E F i k hik
      ⟨⟨_, rfl⟩, ⟨_, he.symm⟩⟩
  have hz0 : z.2 = 0 := by
    by_contra hn
    have hpos : 0 < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm hn)
    exact native_piece_interior_avoids_cut E F i
      ⟨_, H.positive_piece_interior ⟨hz.1, hpos, hz.2.2⟩, rfl⟩ hzcut
  have hw0 : w.2 = 0 := by
    by_contra hn
    have hpos : 0 < w.2 := lt_of_le_of_ne hw.2.1 (Ne.symm hn)
    have hwcut : nativeHalfStripSource E F k l J w ∈ F.seam.carrier ∪ S.boundary := by
      rw [← he]
      exact hzcut
    exact native_piece_interior_avoids_cut E F k
      ⟨_, J.positive_piece_interior ⟨hw.1, hpos, hw.2.2⟩, rfl⟩ hwcut
  have hzeq : z = (z.1, 0) := Prod.ext rfl hz0
  have hweq : w = (w.1, 0) := Prod.ext rfl hw0
  rw [hzeq, hweq, native_halfstrip_source_boundary E F i j H ⟨z.1, hz.1⟩,
    native_halfstrip_source_boundary E F k l J ⟨w.1, hw.1⟩] at he
  have hγeq : γ ⟨z.1, hz.1⟩ = γ ⟨w.1, hw.1⟩ := by
    rw [← hq, ← hr]
    exact congrArg (E.toSphere ∘ F.map) he
  exact ⟨hz0, hw0, congrArg Subtype.val (hγ hγeq)⟩

/-- The two actual native halfstrips form an open source neighbourhood.
No incidence bound or collar premise is used. -/
theorem native_halfstrips_actual_open_union
    (S : CompactOrientedSurface.{u}) (F : GeometricPiecewiseSurface S E.Carrier)
    (i k : Fin F.pieceCount) (hik : i ≠ k)
    (j : Fin (F.domain i).count) (l : Fin (F.domain k).count)
    (q r : SeamLocalTime → Euc 2)
    (H : NativeSeamHalfStrip E F i j q) (J : NativeSeamHalfStrip E F k l r)
    (hheight : H.height = J.height)
    (γ : SeamLocalTime → ThreeSphere) (hγ : Function.Injective γ)
    (hq : ∀ t, pieceSphereCoordinate E F i j (q t) = γ t)
    (hr : ∀ t, pieceSphereCoordinate E F k l (r t) = γ t) :
    IsOpen (nativeHalfStripSource E F i j H '' nativeHalfStripDomain H.height ∪
      nativeHalfStripSource E F k l J '' nativeHalfStripDomain J.height) := by
  have hJ : ContinuousOn (nativeHalfStripSource E F k l J) (nativeHalfStripDomain H.height) := by
    rw [hheight]
    exact continuousOn_iff_continuous_domRestrict.mpr J.source_embedding.continuous
  have hJi : InjOn (nativeHalfStripSource E F k l J) (nativeHalfStripDomain H.height) := by
    rw [hheight]
    intro z hz w hw he
    exact congrArg Subtype.val (J.source_embedding.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) he)
  have hc := native_halfstrips_cross_only_on_common_clock E F i k hik j l q r H J γ hγ hq hr
  have hf : ContinuousOn (nativeHalfStripSource E F i j H) (nativeHalfStripDomain H.height) :=
    continuousOn_iff_continuous_domRestrict.mpr H.source_embedding.continuous
  have hfi : InjOn (nativeHalfStripSource E F i j H) (nativeHalfStripDomain H.height) := by
    intro z hz w hw he
    exact congrArg Subtype.val (H.source_embedding.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) he)
  have hfg : ∀ t ∈ Ioo (-1 : ℝ) 1,
      nativeHalfStripSource E F i j H (t, 0) = nativeHalfStripSource E F k l J (t, 0) := by
    intro t ht
    rw [native_halfstrip_source_boundary E F i j H ⟨t, ht⟩,
      native_halfstrip_source_boundary E F k l J ⟨t, ht⟩]
    apply F.embedding.injective
    apply Subtype.ext
    exact (hq ⟨t, ht⟩).trans (hr ⟨t, ht⟩).symm
  rw [← hheight]
  exact native_two_halfstrip_union_open S H.height H.height_pos _ _ hf hJ hfi hJi hfg
    (fun z hz w hw he => hc z hz w (hheight ▸ hw) he)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
