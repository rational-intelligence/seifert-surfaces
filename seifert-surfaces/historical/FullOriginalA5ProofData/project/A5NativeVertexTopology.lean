import A5LocalContinuousProjection
import A5NativeProjectionAllCharts

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

theorem point_accumulates_in_plane_chart
    {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (Euc 2)) (x : X) (hx : x ∈ e.source) :
    x ∈ closure ({x}ᶜ : Set X) := by
  apply mem_closure_iff_nhds.mpr
  intro W hW
  have htx : e x ∈ e.target := e.map_source hx
  have hnear : e.target ∩ e.symm ⁻¹' W ∈ 𝓝 (e x) :=
    inter_mem (e.open_target.mem_nhds htx)
      ((e.symm.continuousAt htx).preimage_mem_nhds (by simpa only [e.left_inv hx] using hW))
  obtain ⟨z, hz, hzne⟩ := mem_closure_iff_nhds.mp
    (dense_compl_singleton (e x) (e x)) _ hnear
  refine ⟨e.symm z, hz.2, ?_⟩
  intro he
  apply hzne
  change z = e x
  rw [← e.right_inv hz.1, he]

theorem native_interior_point_accumulates
    (S : CompactOrientedSurface) (x : S) (hx : x ∈ (𝓡∂ 2).interior S) :
    x ∈ closure ({x}ᶜ : Set S) := by
  let c := extChartAt (𝓡∂ 2) x
  let e : OpenPartialHomeomorph S (Euc 2) := {
    toFun := c
    invFun := c.symm
    source := c.source ∩ c ⁻¹' interior c.target
    target := interior c.target
    map_source' := fun _ h => h.2
    map_target' := by
      intro y hy
      refine ⟨c.map_target (interior_subset hy), ?_⟩
      change c (c.symm y) ∈ interior c.target
      rw [c.right_inv (interior_subset hy)]
      exact hy
    left_inv' := fun _ h => c.left_inv h.1
    right_inv' := fun _ h => c.right_inv (interior_subset h)
    open_source := isOpen_extChartAt_preimage' x isOpen_interior
    open_target := isOpen_interior
    continuousOn_toFun := (continuousOn_extChartAt x).mono inter_subset_left
    continuousOn_invFun := (continuousOn_extChartAt_symm x).mono interior_subset }
  exact point_accumulates_in_plane_chart e x
    ⟨mem_extChartAt_source x, (ModelWithCorners.isInteriorPoint_iff).mp hx⟩

/-- The native interior topology supplies both the connected punctures and
accumulation needed to remove an isolated projection singularity. Continuity
is required only on the literal ambient-chart neighborhood. -/
theorem native_interior_projection_across_vertex
    (S : CompactOrientedSurface) (x : S) (hx : x ∈ (𝓡∂ 2).interior S)
    (f : S → Euc 2) (U : Set S) (hU : IsOpen U) (hxU : x ∈ U)
    (hf : ContinuousOn f U)
    (hzero : ∀ z ∈ U, f z = f x → z = x)
    (hlocal : IsLocalHomeomorphOn f (U \ {x}))
    (height : S → ℝ) (hheight : ContinuousOn height U)
    (hseparate : InjOn (fun z => (f z, height z)) U) :
    IsLocalHomeomorphOn f {x} :=
  locally_continuous_projection_across_point f x U hU hxU hf hzero hlocal
    (native_interior_point_accumulates S x hx)
    (native_interior_punctured_neighborhoods S x hx) height hheight hseparate

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
