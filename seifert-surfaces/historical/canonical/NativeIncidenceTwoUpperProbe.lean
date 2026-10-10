import IncidenceProbe
import HalfStripGlueProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- Every whole native piece incident to an open two-piece neighbourhood is
one of those two. The whole-piece closure axiom and actual disjoint interiors
exclude a third boundary-only incident piece. -/
theorem native_two_piece_open_cover_excludes_others
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i j : Fin F.pieceCount) (U : Set S) (hU : IsOpen U)
    (hcover : U ⊆ range (F.parametrization i) ∪ range (F.parametrization j)) :
    ∀ x ∈ U, ∀ k : Fin F.pieceCount,
      x ∈ range (F.parametrization k) → k = i ∨ k = j := by
  intro x hx k hk
  by_contra hnot
  have hki : k ≠ i := fun h => hnot (Or.inl h)
  have hkj : k ≠ j := fun h => hnot (Or.inr h)
  have hxcl : x ∈ closure ((F.parametrization k) '' (F.domain k).interior) := by
    rw [← F.piece_closure k]
    exact hk
  have hex : (U ∩ ((F.parametrization k) '' (F.domain k).interior)).Nonempty :=
    mem_closure_iff_nhds.mp hxcl U (hU.mem_nhds hx)
  obtain ⟨z, hzU, hzk⟩ := hex
  have hzcut : z ∉ F.seam.carrier ∪ S.boundary := native_piece_interior_avoids_cut E F k hzk
  have hzrange : z ∈ range (F.parametrization k) := image_subset_range _ _ hzk
  rcases hcover hzU with hzi | hzj
  · exact hzcut (native_distinct_piece_intersection_subset_cut E F k i hki ⟨hzrange, hzi⟩)
  · exact hzcut (native_distinct_piece_intersection_subset_cut E F k j hkj ⟨hzrange, hzj⟩)

/-- Once two actual native halfstrips are constructed, their open glued
neighbourhood proves the whole-piece incidence count there. -/
theorem native_halfstrips_exclude_third_incident_piece
    (S : CompactOrientedSurface.{u}) (F : GeometricPiecewiseSurface S E.Carrier)
    (i j : Fin F.pieceCount) (h : ℝ) (hh : 0 < h) (f g : ℝ × ℝ → S)
    (hf : ContinuousOn f (seamHalfstrip h)) (hg : ContinuousOn g (seamHalfstrip h))
    (hfi : InjOn f (seamHalfstrip h)) (hgi : InjOn g (seamHalfstrip h))
    (hfg : ∀ t ∈ Ioo (-1 : ℝ) 1, f (t, 0) = g (t, 0))
    (hcross : ∀ z ∈ seamHalfstrip h, ∀ w ∈ seamHalfstrip h,
      f z = g w → z.2 = 0 ∧ w.2 = 0 ∧ z.1 = w.1)
    (hfrange : MapsTo f (seamHalfstrip h) (range (F.parametrization i)))
    (hgrange : MapsTo g (seamHalfstrip h) (range (F.parametrization j))) :
    ∀ x ∈ f '' seamHalfstrip h ∪ g '' seamHalfstrip h,
      ∀ k : Fin F.pieceCount, x ∈ range (F.parametrization k) → k = i ∨ k = j := by
  apply native_two_piece_open_cover_excludes_others E F i j _
    (native_two_halfstrip_union_open S h hh f g hf hg hfi hgi hfg hcross)
  rintro x (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
  · exact Or.inl (hfrange hz)
  · exact Or.inr (hgrange hz)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
