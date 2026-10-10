import A5InteriorNativeImageChart

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v

/-- At an interior source point, an actual smooth image chart gives a
regular smooth parametrization on an open subset of the plane. -/
theorem native_image_chart_plane_parametrization
    {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    (S : CompactOrientedSurface.{u}) (f : S → M)
    (C : SmoothImageChart S f) (x : S) (hx : x ∈ C.chart.source)
    (hxboundary : x ∉ S.boundary) :
    ∃ e : OpenPartialHomeomorph S (Euc 2),
      x ∈ e.source ∧ e.source ⊆ C.chart.source ∧
      ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞ (f ∘ e.symm) e.target ∧
      ∀ y ∈ e.target, Function.Injective
        (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) (f ∘ e.symm) y) := by
  let c : OpenPartialHomeomorph S (EuclideanHalfSpace 2) := {
    toPartialHomeomorph := C.chart
    open_source := C.source_open
    open_target := C.target_open }
  let D := interiorHalfSpaceCoordinates (0 : Euc 2)
  let d := D.toOpenPartialHomeomorph
  let e := c.trans d
  have hxmodel : C.chart x ∉ (𝓡∂ 2).boundary (EuclideanHalfSpace 2) := by
    intro hb
    have hm : C.chart x ∈ C.chart '' (S.boundary ∩ C.chart.source) := by
      rw [C.boundary_image]
      exact ⟨hb, C.chart.map_source hx⟩
    obtain ⟨z, hz, he⟩ := hm
    exact hxboundary (C.chart.injOn hz.2 hx he ▸ hz.1)
  have hxd : c x ∈ d.source := by
    have hi := ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint (C.chart x)).mpr hxmodel
    change extChartAt (𝓡∂ 2) (C.chart x) (C.chart x) ∈ interior (range (𝓡∂ 2)) at hi
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at hi
    change 0 < ((𝓡∂ 2) (c x)) 0
    change 0 < ((𝓡∂ 2) (C.chart x)) 0
    simpa using hi
  have hD : d.MDifferentiable (𝓡∂ 2) 𝓘(ℝ, Euc 2) :=
    ⟨D.contMDiffOn.mdifferentiableOn (by simp), D.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hsm : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞ (f ∘ e.symm) e.target :=
    C.cInfinity.comp (D.symm.contMDiffOn.mono (fun y hy => hy.1)) (fun y hy => hy.2)
  refine ⟨e, ⟨hx, hxd⟩, fun y hy => hy.1, hsm, ?_⟩
  intro y hy
  have hd := hD.mdifferentiableAt_symm hy.1
  have hf := (C.cInfinity.contMDiffAt (C.target_open.mem_nhds hy.2)).mdifferentiableAt (by simp)
  have hr := C.differential_injective (d.symm y) hy.2
  rw [mfderivWithin_of_mem_nhds (C.target_open.mem_nhds hy.2)] at hr
  change Function.Injective (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) ((f ∘ C.chart.symm) ∘ d.symm) y)
  rw [mfderiv_comp y hf hd]
  exact hr.comp (hD.symm.mfderiv_injective hy.1)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
