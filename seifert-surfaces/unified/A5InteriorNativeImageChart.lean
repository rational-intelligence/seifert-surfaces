import A5InteriorHalfSpaceChart
import A5NativeAmbientLift

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v

/-- A smooth regular parametrization on an actual plane projection chart
constructs the literal native image chart. Source boundary labels and the
half-space model boundary are both preserved. -/
theorem native_interior_image_chart_of_plane_chart
    {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    (S : CompactOrientedSurface.{u}) (f : S → M)
    (e : OpenPartialHomeomorph S (Euc 2)) (x : S)
    (hx : x ∈ e.source) (hxboundary : x ∉ S.boundary)
    (hsmooth : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞ (f ∘ e.symm) e.target)
    (hrank : ∀ y ∈ e.target, Function.Injective
      (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) (f ∘ e.symm) e.target y)) :
    ∃ c : SmoothImageChart S f, x ∈ c.chart.source ∧ c.chart.source ⊆ e.source := by
  have hboundary : IsClosed S.boundary := (𝓡∂ 2).isClosed_boundary (n := ∞) (by simp)
  let er := e.restrOpen S.boundaryᶜ hboundary.isOpen_compl
  let D := interiorHalfSpaceCoordinates (e x)
  let d := D.toOpenPartialHomeomorph
  let c := er.trans d.symm
  have hxc : x ∈ c.source :=
    ⟨⟨hx, hxboundary⟩, interiorHalfSpaceCoordinates_mem_target (e x)⟩
  have htarget (y : EuclideanHalfSpace 2) (hy : y ∈ c.target) :
      y ∈ d.source ∧ d y ∈ er.target := hy
  have hD : d.MDifferentiable (𝓡∂ 2) 𝓘(ℝ, Euc 2) :=
    ⟨D.contMDiffOn.mdifferentiableOn (by simp),
      D.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hc : ContMDiffOn (𝓡∂ 2) (𝓡∂ 3) ∞ (f ∘ c.symm) c.target := by
    exact hsmooth.comp (D.contMDiffOn.mono (fun y hy => (htarget y hy).1))
      (fun y hy => (htarget y hy).2.1)
  refine ⟨{
    chart := c.toPartialHomeomorph
    source_open := c.open_source
    target_open := c.open_target
    cInfinity := hc
    differential_injective := ?_
    boundary_image := ?_ }, hxc, fun y hy => hy.1.1⟩
  · intro y hy
    change Function.Injective
      (mfderivWithin (𝓡∂ 2) (𝓡∂ 3) (f ∘ c.symm) c.target y)
    have hyd := (htarget y hy).1
    have hye : d y ∈ e.target := (htarget y hy).2.1
    have hf := (hsmooth.contMDiffAt (e.open_target.mem_nhds hye)).mdifferentiableAt (by simp)
    have hd := hD.mdifferentiableAt hyd
    have hi := hrank (d y) hye
    rw [mfderivWithin_eq_mfderiv (e.open_target.uniqueMDiffWithinAt hye) hf] at hi
    have hcy := (hc.contMDiffAt (c.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
    rw [mfderivWithin_eq_mfderiv
      (I := 𝓡∂ 2) (I' := 𝓡∂ 3) (c.open_target.uniqueMDiffWithinAt hy) hcy]
    change Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) ((f ∘ e.symm) ∘ d) y)
    rw [mfderiv_comp y hf hd]
    exact hi.comp (hD.mfderiv_injective hyd)
  · apply Set.ext
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact False.elim (hz.2.1.2 hz.1)
    · intro hy
      exact False.elim ((Set.disjoint_left.mp
        (interiorHalfSpaceCoordinates_source_avoids_boundary (e x)))
        (htarget y hy.2).1 hy.1)

/-- The coordinate graph theorem feeds the exact native image chart
directly, without assuming smoothness of the auxiliary source map. -/
theorem native_interior_image_chart_of_sphere_graph
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (e : OpenPartialHomeomorph S (Euc 2)) (x : S)
    (hx : x ∈ e.source) (hxboundary : x ∉ S.boundary)
    (c : SmoothAmbientChart ThreeSphere)
    (hchart : MapsTo (E.toSphere ∘ F.map ∘ e.symm) e.target c.chart.source)
    (hsmooth : ContDiffOn ℝ ∞ (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) e.target)
    (hrank : ∀ y ∈ e.target, Function.Injective
      (fderiv ℝ (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) y)) :
    ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source ∧ C.chart.source ⊆ e.source := by
  obtain ⟨hs, hr⟩ := native_exterior_smooth_rank_of_coordinate_graph E (F.map ∘ e.symm)
    e.target e.open_target (F.map.continuous.comp_continuousOn e.symm.continuousOn)
    c hchart hsmooth hrank
  exact native_interior_image_chart_of_plane_chart S F.map e x hx hxboundary hs hr

/-- The native projection identity itself supplies the immersion rank,
so smoothness of its inverse image parametrization is the only analytic
input to the interior image-chart construction. -/
theorem native_interior_image_chart_of_smooth_projection
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (e : OpenPartialHomeomorph S (Euc 2)) (x : S)
    (hx : x ∈ e.source) (hxboundary : x ∉ S.boundary)
    (c : SmoothAmbientChart ThreeSphere) (P : Euc 3 →L[ℝ] Euc 2)
    (he : ∀ z ∈ e.source, e z = P (c.chart (E.toSphere (F.map z))))
    (hchart : MapsTo (E.toSphere ∘ F.map ∘ e.symm) e.target c.chart.source)
    (hsmooth : ContDiffOn ℝ ∞ (c.chart ∘ E.toSphere ∘ F.map ∘ e.symm) e.target) :
    ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source ∧ C.chart.source ⊆ e.source := by
  apply native_interior_image_chart_of_sphere_graph E F e x hx hxboundary c hchart hsmooth
  intro y hy
  let g := c.chart ∘ E.toSphere ∘ F.map ∘ e.symm
  have hg : DifferentiableAt ℝ g y :=
    (hsmooth.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have heq : P ∘ g =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    change P (c.chart (E.toSphere (F.map (e.symm z)))) = z
    rw [← he _ (e.map_target hz), e.right_inv hz]
  have hd : P.comp (fderiv ℝ g y) = ContinuousLinearMap.id ℝ (Euc 2) := by
    rw [← (P.hasFDerivAt.comp y hg.hasFDerivAt).fderiv,
      heq.fderiv_eq, fderiv_id]
  have hi : Function.Injective (P.comp (fderiv ℝ g y)) := by
    rw [hd]
    exact Function.injective_id
  exact Function.Injective.of_comp hi

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
