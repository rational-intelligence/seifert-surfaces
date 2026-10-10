import OriginalA25SourceDefinitionsV464
import AreaSectorInteriorSupport

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology MeasureTheory
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section

namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

theorem native_piece_interior_avoids_cut
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) :
    (F.parametrization i) '' (F.domain i).interior ⊆ (F.seam.carrier ∪ S.boundary)ᶜ := by
  obtain ⟨x, hx, heq⟩ := F.piece_interior_component i
  rw [heq]
  exact connectedComponentIn_subset _ _

theorem native_seam_incident_preimage_boundary
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (p : F.domain i)
    (hp : F.parametrization i p ∈ F.seam.carrier) : p ∈ (F.domain i).boundary := by
  by_contra h
  exact native_piece_interior_avoids_cut E F i ⟨p, h, rfl⟩ (Or.inl hp)



/-- Every native incident seam preimage is a boundary point of its actual
closed whole piece, hence a frontier point in any selected native chart. -/
theorem native_seam_chart_coordinate_boundary
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (p : F.domain i)
    (hp : F.parametrization i p ∈ F.seam.carrier)
    (hpc : p ∈ ((F.domain i).chart j).map.source) :
    ((F.domain i).chart j).map p ∈ ((F.domain i).chart j).map.target ∩
      frontier ((F.domain i).chart j).map.target := by
  let c := (F.domain i).chart j
  have hyt : c.map p ∈ c.map.target := c.map.map_source hpc
  have hyb : c.map p ∈ c.model.boundary := by
    rw [← (F.domain i).boundary_charts j]
    exact ⟨p, ⟨native_seam_incident_preimage_boundary E F i p hp, hpc⟩, rfl⟩
  refine ⟨hyt, ⟨subset_closure hyt, ?_⟩⟩
  rw [c.target_eq, AreaCertificates.sector_model_interior]
  exact fun h => h.2 hyb

/-- Compact native graph components isolate every nonvertex point of an
original arc from the source boundary and from every other seam component. -/
theorem native_arc_isolated_source_window
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin F.seam.arcCount) (s : Time)
    (hleft : 0 < (s : ℝ)) (hright : (s : ℝ) < 1) :
    ∃ U : Set S, IsOpen U ∧ F.seam.arc a s ∈ U ∧
      U ⊆ S.boundaryᶜ ∧ F.seam.carrier ∩ U = range (F.seam.arc a) ∩ U := by
  classical
  let A := ⋃ i : {i : Fin F.seam.arcCount // i ≠ a}, range (F.seam.arc i.val)
  let C := ⋃ i : Fin F.seam.circleCount, range (F.seam.circle i)
  have hA : IsClosed A :=
    (isCompact_iUnion (fun i : {i : Fin F.seam.arcCount // i ≠ a} =>
      isCompact_range (F.seam.arc i.val).continuous)).isClosed
  have hC : IsClosed C :=
    (isCompact_iUnion (fun i => isCompact_range (F.seam.circle i).continuous)).isClosed
  have hB : IsClosed S.boundary := ModelWithCorners.isClosed_boundary (I := 𝓡∂ 2) (n := ∞) (by simp)
  have hs0 : s ≠ 0 := by intro h; have := congrArg Subtype.val h; simpa using hleft.ne' this
  have hs1 : s ≠ 1 := by intro h; have := congrArg Subtype.val h; simpa using hright.ne this
  have hb : F.seam.arc a s ∉ S.boundary := by
    intro hb
    rcases F.seam.arc_boundary a hb with h | h
    · exact hs0 h
    · exact hs1 h
  have ha : F.seam.arc a s ∉ A := by
    intro h
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    have hh := F.seam.arc_intersections a i.val (Ne.symm i.property)
      ⟨⟨s, rfl⟩, hi⟩
    rcases hh.1 with h | h
    · exact hs0 ((F.seam.arc_embedding a).injective h)
    · exact hs1 ((F.seam.arc_embedding a).injective h)
  have hc : F.seam.arc a s ∉ C := by
    intro h
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    exact Set.disjoint_left.mp (F.seam.arc_circle_disjoint a i) ⟨s, rfl⟩ hi
  refine ⟨(S.boundary ∪ A ∪ C)ᶜ, ((hB.union hA).union hC).isOpen_compl,
    by simpa only [mem_compl_iff, mem_union] using not_or.mpr ⟨not_or.mpr ⟨hb, ha⟩, hc⟩,
    ?_, ?_⟩
  · intro x hx hxB
    exact hx (Or.inl (Or.inl hxB))
  · ext x
    constructor
    · rintro ⟨hx, hxU⟩
      refine ⟨?_, hxU⟩
      rcases hx with hx | hx
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        by_cases hia : i = a
        · simpa only [hia] using hi
        · exact (hxU (Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨i, hia⟩, hi⟩)))).elim
      · exact (hxU (Or.inr hx)).elim
    · rintro ⟨hx, hxU⟩
      exact ⟨Or.inl (mem_iUnion.mpr ⟨a, hx⟩), hxU⟩

/-- Circle components need no chosen global cut: their native compact
ranges isolate them from every other component and the source boundary. -/
theorem native_circle_isolated_source_window
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (a : Fin F.seam.circleCount) (s : Circle) :
    ∃ U : Set S, IsOpen U ∧ F.seam.circle a s ∈ U ∧
      U ⊆ S.boundaryᶜ ∧ F.seam.carrier ∩ U = range (F.seam.circle a) ∩ U := by
  classical
  let A := ⋃ i : Fin F.seam.arcCount, range (F.seam.arc i)
  let C := ⋃ i : {i : Fin F.seam.circleCount // i ≠ a}, range (F.seam.circle i.val)
  have hA : IsClosed A :=
    (isCompact_iUnion (fun i => isCompact_range (F.seam.arc i).continuous)).isClosed
  have hC : IsClosed C :=
    (isCompact_iUnion (fun i : {i : Fin F.seam.circleCount // i ≠ a} =>
      isCompact_range (F.seam.circle i.val).continuous)).isClosed
  have hB : IsClosed S.boundary := ModelWithCorners.isClosed_boundary (I := 𝓡∂ 2) (n := ∞) (by simp)
  have hb : F.seam.circle a s ∉ S.boundary :=
    fun hb => Set.disjoint_left.mp (F.seam.circle_off_boundary a) ⟨s, rfl⟩ hb
  have ha : F.seam.circle a s ∉ A := by
    intro h
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    exact Set.disjoint_left.mp (F.seam.arc_circle_disjoint i a) hi ⟨s, rfl⟩
  have hc : F.seam.circle a s ∉ C := by
    intro h
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    exact Set.disjoint_left.mp (F.seam.circle_intersections (Ne.symm i.property)) ⟨s, rfl⟩ hi
  refine ⟨(S.boundary ∪ A ∪ C)ᶜ, ((hB.union hA).union hC).isOpen_compl,
    by simpa only [mem_compl_iff, mem_union] using not_or.mpr ⟨not_or.mpr ⟨hb, ha⟩, hc⟩,
    ?_, ?_⟩
  · intro x hx hxB
    exact hx (Or.inl (Or.inl hxB))
  · ext x
    constructor
    · rintro ⟨hx, hxU⟩
      refine ⟨?_, hxU⟩
      rcases hx with hx | hx
      · exact (hxU (Or.inl (Or.inr hx))).elim
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        by_cases hia : i = a
        · simpa only [hia] using hi
        · exact (hxU (Or.inr (mem_iUnion.mpr ⟨⟨i, hia⟩, hi⟩))).elim
    · rintro ⟨hx, hxU⟩
      exact ⟨Or.inr (mem_iUnion.mpr ⟨a, hx⟩), hxU⟩



/-- Distinct native whole pieces can intersect only on the native cutting
set. This uses literal whole-piece boundaries and disjoint interiors. -/
theorem native_distinct_piece_intersection_subset_cut
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i j : Fin F.pieceCount) (hij : i ≠ j) :
    range (F.parametrization i) ∩ range (F.parametrization j) ⊆
      F.seam.carrier ∪ S.boundary := by
  rintro x ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
  by_cases hpb : p ∈ (F.domain i).boundary
  · exact F.piece_boundary i ⟨p, hpb, hp⟩
  by_cases hqb : q ∈ (F.domain j).boundary
  · exact F.piece_boundary j ⟨q, hqb, hq⟩
  exact (Set.disjoint_left.mp (F.pieces_distinct hij) ⟨p, hpb, hp⟩ ⟨q, hqb, hq⟩).elim

/-- The native cover supplies an actual incident whole piece at every point. -/
theorem native_piece_incidence_nonempty
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier) (x : S) :
    ∃ i : Fin F.pieceCount, x ∈ range (F.parametrization i) := by
  have hx : x ∈ ⋃ i, range (F.parametrization i) := by rw [F.covers]; trivial
  exact mem_iUnion.mp hx

/-- Compact native parameter embeddings allow any open parameter window to
be isolated by an open source neighbourhood, retaining the original clock. -/
theorem native_compact_parameter_window
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] [CompactSpace P] [T2Space X]
    (f : C(P, X)) (hf : IsEmbedding f) (p : P) (W : Set P) (hW : IsOpen W) (hp : p ∈ W) :
    ∃ U : Set X, IsOpen U ∧ f p ∈ U ∧ f ⁻¹' U ⊆ W := by
  let U := (f '' Wᶜ)ᶜ
  have hU : IsOpen U := (hW.isClosed_compl.isCompact.image f.continuous).isClosed.isOpen_compl
  refine ⟨U, hU, ?_, ?_⟩
  · rintro ⟨q, hq, hqp⟩
    exact hq (hf.injective hqp ▸ hp)
  · intro q hq
    by_contra hnot
    exact hq ⟨q, hnot, rfl⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
