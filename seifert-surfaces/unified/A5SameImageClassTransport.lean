import A5GlobalSourceConsumer

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- Relabelling the target by a same-image source homeomorphism preserves
the complete geometric source morphism. All rank and regularity fields are
transported as literal equalities of the original ambient maps. -/
def geometric_source_map_same_image_target
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    {S R Q : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (H : GeometricPiecewiseSurface Q M) (e : R ≃ₜ Q)
    (he : ∀ x, H.map (e x) = G.map x)
    (f : S → R) (D : GeometricSourceMap F G f) :
    GeometricSourceMap F H (e ∘ f) := by
  have hm (i : Fin D.count) : H.map ∘ (e ∘ f) ∘ D.parametrization i =
      G.map ∘ f ∘ D.parametrization i := by funext x; exact he _
  exact {
    count := D.count
    domain := D.domain
    parametrization := D.parametrization
    embedding := D.embedding
    covers := D.covers
    source_c1 := D.source_c1
    source_injective := D.source_injective
    source_smooth_interior := D.source_smooth_interior
    target_c1 := fun i => by rw [hm]; exact D.target_c1 i
    target_injective := fun i x => by rw [hm]; exact D.target_injective i x
    target_smooth_interior := fun i => by rw [hm]; exact D.target_smooth_interior i }

/-- Relabel the source with the same actual geometric image, keeping every
original compact corner domain and its original ambient regularity. -/
def geometric_source_map_same_image_source
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    {S R Q : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (H : GeometricPiecewiseSurface Q M) (e : S ≃ₜ Q)
    (he : ∀ x, H.map (e x) = F.map x)
    (f : S → R) (D : GeometricSourceMap F G f) :
    GeometricSourceMap H G (f ∘ e.symm) := by
  let p (i : Fin D.count) : C(D.domain i, Q) :=
    ⟨e ∘ D.parametrization i, e.continuous.comp (D.parametrization i).continuous⟩
  have hsource (i : Fin D.count) : H.map ∘ p i = F.map ∘ D.parametrization i := by
    funext x
    exact he _
  have htarget (i : Fin D.count) : G.map ∘ (f ∘ e.symm) ∘ p i =
      G.map ∘ f ∘ D.parametrization i := by
    funext x
    change G.map (f (e.symm (e (D.parametrization i x)))) = G.map (f (D.parametrization i x))
    rw [e.symm_apply_apply]
  refine {
    count := D.count
    domain := D.domain
    parametrization := p
    embedding := fun i => e.isEmbedding.comp (D.embedding i)
    covers := ?_
    source_c1 := fun i => by rw [hsource]; exact D.source_c1 i
    source_injective := fun i x => by rw [hsource]; exact D.source_injective i x
    source_smooth_interior := fun i => by rw [hsource]; exact D.source_smooth_interior i
    target_c1 := fun i => by rw [htarget]; exact D.target_c1 i
    target_injective := fun i x => by rw [htarget]; exact D.target_injective i x
    target_smooth_interior := fun i => by rw [htarget]; exact D.target_smooth_interior i }
  apply Set.eq_univ_of_forall
  intro x
  have hx : e.symm x ∈ ⋃ i, range (D.parametrization i) := by rw [D.covers]; trivial
  obtain ⟨i, y, hy⟩ := mem_iUnion.mp hx
  refine mem_iUnion.mpr ⟨i, y, ?_⟩
  change e (D.parametrization i y) = x
  rw [hy, e.apply_symm_apply]

/-- Exact same-image source relabelling preserves the original full
fixed-boundary competitor class, including its original anchored track. -/
theorem FixedBoundaryImageIsotopic.same_image_source
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {S R Q : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (G : GeometricPiecewiseSurface R E.Carrier)
    (H : GeometricPiecewiseSurface Q E.Carrier)
    (e : R ≃ₜ Q) (he : ∀ x, H.map (e x) = G.map x)
    (hboundary : e '' R.boundary = Q.boundary)
    (h : FixedBoundaryImageIsotopic E F G) : FixedBoundaryImageIsotopic E F H := by
  obtain ⟨d, stage, hc, ht, hzero, hone, hfixed⟩ := h
  let D : GeometricSourceHomeomorph F H := {
    homeomorph := d.homeomorph.trans e
    forward := geometric_source_map_same_image_target F G H e he d.homeomorph d.forward
    backward := geometric_source_map_same_image_source G F H e he d.homeomorph.symm d.backward
    boundary_image := by
      calc
        (e ∘ d.homeomorph) '' S.boundary = e '' (d.homeomorph '' S.boundary) := by
          ext z; constructor
          · rintro ⟨x, hx, rfl⟩
            exact ⟨d.homeomorph x, ⟨x, hx, rfl⟩, rfl⟩
          · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨x, hx, rfl⟩
        _ = e '' R.boundary := by rw [d.boundary_image]
        _ = Q.boundary := hboundary }
  refine ⟨D, stage, hc, ht, hzero, ?_, hfixed⟩
  rw [hone]
  apply ContinuousMap.ext
  intro x
  exact (he (d.homeomorph x)).symm

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
