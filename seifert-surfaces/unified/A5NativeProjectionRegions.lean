import A5NativePieceProjectionGraph

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- The actual whole-piece decomposition becomes a finite relatively
closed cover of the projection domain, with continuous exact graph section
and exact image equality. No projected-region cover is assumed. -/
theorem native_projection_whole_piece_regions
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (c : SmoothAmbientChart ThreeSphere) (P : Euc 3 →L[ℝ] Euc 2)
    (e : OpenPartialHomeomorph S (Euc 2))
    (he : ∀ x, e x = P (c.chart (E.toSphere (F.map x))))
    (hmaps : MapsTo (E.toSphere ∘ F.map) e.source c.chart.source) :
    let regions := fun i : Fin F.pieceCount => e.target ∩ e.symm ⁻¹' range (F.parametrization i)
    let f := c.chart ∘ E.toSphere ∘ F.map ∘ e.symm
    (⋃ i, regions i) = e.target ∧
    (∀ i, closure (regions i) ∩ e.target ⊆ regions i) ∧
    ContinuousOn f e.target ∧ (∀ y ∈ e.target, P (f y) = y) ∧
    f '' e.target = (c.chart ∘ E.toSphere ∘ F.map) '' e.source := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact hi.1
    · intro hy
      have hc : e.symm y ∈ ⋃ i, range (F.parametrization i) := by rw [F.covers]; trivial
      obtain ⟨i, hi⟩ := mem_iUnion.mp hc
      exact mem_iUnion.mpr ⟨i, hy, hi⟩
  · intro i y hy
    refine ⟨hy.2, ?_⟩
    let R := e.target ∩ e.symm ⁻¹' range (F.parametrization i)
    let _ : NeBot (𝓝[R] y) := mem_closure_iff_nhdsWithin_neBot.mp hy.1
    have hc : IsClosed (range (F.parametrization i)) :=
      (isCompact_range (F.parametrization i).continuous).isClosed
    apply hc.mem_of_tendsto (b := 𝓝[R] y)
      ((e.symm.continuousAt hy.2).mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin (s := R) (a := y)] with z hz
    exact hz.2
  · apply c.chart.continuousOn.comp
      ((continuous_subtype_val.comp F.map.continuous).comp_continuousOn e.symm.continuousOn)
    intro y hy
    exact hmaps (e.map_target hy)
  · intro y hy
    change P (c.chart (E.toSphere (F.map (e.symm y)))) = y
    rw [← he, e.right_inv hy]
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e.symm y, e.map_target hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e x, e.map_source hx, ?_⟩
      change c.chart (E.toSphere (F.map (e.symm (e x)))) = c.chart (E.toSphere (F.map x))
      rw [e.left_inv hx]

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
