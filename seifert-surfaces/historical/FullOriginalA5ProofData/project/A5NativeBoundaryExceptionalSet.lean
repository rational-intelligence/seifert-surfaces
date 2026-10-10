import A5NativeLongitudeBoundary
import A5NativeFiniteSeamConsumer

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- The only possible nonsmooth boundary points of a literal native image
are its finite arc endpoints. This uses the native image-chart field itself. -/
theorem native_boundary_image_charts_off_arc_endpoints
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {R : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface R E.Carrier)
    (x : R) (hx : x ∈ R.boundary)
    (hzero : ∀ a : Fin F.seam.arcCount, x ≠ F.seam.arc a 0)
    (hone : ∀ a : Fin F.seam.arcCount, x ≠ F.seam.arc a 1) :
    ∃ C : SmoothImageChart R F.map, x ∈ C.chart.source := by
  have hxs : x ∉ F.seam.carrier := by
    intro hs
    rcases hs with ha | hc
    · obtain ⟨a,s,he⟩ := mem_iUnion.mp ha
      have hb : F.seam.arc a s ∈ R.boundary := he ▸ hx
      obtain hs | hs := F.seam.arc_boundary a hb
      · exact hzero a (he.symm.trans (congrArg (F.seam.arc a) hs))
      · exact hone a (he.symm.trans (congrArg (F.seam.arc a) hs))
    · obtain ⟨a,s,he⟩ := mem_iUnion.mp hc
      exact Set.disjoint_left.mp (F.seam.circle_off_boundary a) ⟨s,he⟩ hx
  obtain ⟨C,hC,_⟩ := F.smooth_off_seam x hxs
  exact ⟨C,hC⟩

/-- All boundary regularity reduces to the finitely many actual native
arc endpoints on the boundary. No assumption concerns other boundary points. -/
theorem native_boundary_image_charts_of_arc_endpoints
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {R : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface R E.Carrier)
    (hzero : ∀ a : Fin F.seam.arcCount, F.seam.arc a 0 ∈ R.boundary →
      ∃ C : SmoothImageChart R F.map, F.seam.arc a 0 ∈ C.chart.source)
    (hone : ∀ a : Fin F.seam.arcCount, F.seam.arc a 1 ∈ R.boundary →
      ∃ C : SmoothImageChart R F.map, F.seam.arc a 1 ∈ C.chart.source) :
    ∀ x ∈ R.boundary, ∃ C : SmoothImageChart R F.map, x ∈ C.chart.source := by
  intro x hx
  by_cases hz : ∃ a : Fin F.seam.arcCount, x = F.seam.arc a 0
  · obtain ⟨a,rfl⟩ := hz; exact hzero a hx
  by_cases ho : ∃ a : Fin F.seam.arcCount, x = F.seam.arc a 1
  · obtain ⟨a,rfl⟩ := ho; exact hone a hx
  exact native_boundary_image_charts_off_arc_endpoints F x hx
    (fun a he => hz ⟨a,he⟩) (fun a he => ho ⟨a,he⟩)

/-- Each exceptional boundary endpoint can be isolated from all other
endpoints. Assuming ordinary arc/circle regularity, the entire punctured
native neighborhood already has actual smooth image charts. -/
theorem native_boundary_endpoint_punctured_image_cover
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {R : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface R E.Carrier)
    (x : R)
    (harc : ∀ (a : Fin F.seam.arcCount) (s : Time), 0 < s → s < 1 →
      ∃ C : SmoothImageChart R F.map, F.seam.arc a s ∈ C.chart.source)
    (hcircle : ∀ (a : Fin F.seam.circleCount) (s : Circle),
      ∃ C : SmoothImageChart R F.map, F.seam.circle a s ∈ C.chart.source) :
    ∃ U : Set R, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ≠ x → ∃ C : SmoothImageChart R F.map, y ∈ C.chart.source := by
  let A : Set R := range (fun a => F.seam.arc a 0) ∪ range (fun a => F.seam.arc a 1)
  have hA : A.Finite := (finite_range _).union (finite_range _)
  let U := (A \ {x})ᶜ
  have hU : IsOpen U := (hA.subset sdiff_subset).isClosed.isOpen_compl
  have hxU : x ∈ U := by simp [U]
  refine ⟨U,hU,hxU,?_⟩
  intro y hy hne
  have hyA : y ∉ A := fun hm => hy ⟨hm,hne⟩
  by_cases hs : y ∈ F.seam.carrier
  · rcases hs with ha | hc
    · obtain ⟨a,s,rfl⟩ := mem_iUnion.mp ha
      have hs0 : s ≠ 0 := by
        intro he; apply hyA; subst s; exact Or.inl (mem_range_self a)
      have hs1 : s ≠ 1 := by
        intro he; apply hyA; subst s; exact Or.inr (mem_range_self a)
      exact harc a s (lt_of_le_of_ne s.property.1 (Ne.symm hs0))
        (lt_of_le_of_ne s.property.2 hs1)
    · obtain ⟨a,s,rfl⟩ := mem_iUnion.mp hc
      exact hcircle a s
  · obtain ⟨C,hC,_⟩ := F.smooth_off_seam y hs
    exact ⟨C,hC⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
