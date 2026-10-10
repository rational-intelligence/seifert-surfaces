import Section5BoundaryCurveStraighteningV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter Manifold
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.Section5.BoundaryNormalFormV488
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations
universe u v
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (Euc 1) S]
  [IsManifold (𝓡 1) ∞ S]
  {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- The actual half-space chart assembly. The graph equality and the image
condition are used on an open source neighborhood of the same map. -/
theorem boundary_curve_immersion_of_straightening
    {f : S → M} (hf : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ f) (x : S)
    (g : Euc 1 → Euc 3)
    (hge : g =ᶠ[𝓝 (extChartAt (𝓡 1) x x)]
      ((extChartAt (𝓡∂ 3) (f x)) ∘ f ∘ (extChartAt (𝓡 1) x).symm))
    (β : OpenPartialHomeomorph (Euc 3) (Euc 3))
    (hβ : ContDiffOn ℝ ∞ β β.source) (hβi : ContDiffOn ℝ ∞ β.symm β.target)
    (himage : β.IsImage (range (𝓡∂ 3)) (range (𝓡∂ 3)))
    (hgraph : ∀ᶠ z : Euc 1 in 𝓝 (extChartAt (𝓡 1) x x),
      g z ∈ β.source ∧ β (g z) = standardBoundaryCurveEquiv (z,0)) :
    IsImmersionAtOfComplement (Euc 2) (𝓡 1) (𝓡∂ 3) ∞ f x := by
  let c := chartAt (Euc 1) x
  let d := chartAt (EuclideanHalfSpace 3) (f x)
  let e := extChartAt (𝓡 1) x
  let F := (extChartAt (𝓡∂ 3) (f x)) ∘ f
  let η := halfSpaceRestriction β himage
  let δ := d.trans η
  have heT : Tendsto e (𝓝 x) (𝓝 (e x)) :=
    (contMDiffAt_extChartAt (I := 𝓡 1) (n := ∞) (x := x)).continuousAt.tendsto
  have hmatch : ∀ᶠ y in 𝓝 x,
      y ∈ c.source ∧ f y ∈ d.source ∧
      F y ∈ β.source ∧ β (F y) = standardBoundaryCurveEquiv (e y,0) := by
    have hgr := (contMDiffAt_extChartAt (I := 𝓡 1) (n := ∞) (x := x)).continuousAt.tendsto.eventually hgraph
    have heq := heT.eventually hge
    have hdf : ∀ᶠ y in 𝓝 x, f y ∈ d.source :=
      hf.continuous.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds (mem_chart_source _ _))
    filter_upwards [c.open_source.mem_nhds (mem_chart_source _ _),hdf,hgr,heq] with y hy hdy hgy heqy
    have hey : y ∈ e.source := by simpa [e,c] using hy
    have hecy : e.symm (e y) = y := e.left_inv hey
    have hgyF : g (e y) = F y := by
      change g (e y) = (extChartAt (𝓡∂ 3) (f x)) (f (e.symm (e y))) at heqy
      rw [hecy] at heqy
      exact heqy
    exact ⟨hy,hdy,hgyF ▸ hgy.1,hgyF ▸ hgy.2⟩
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hmatch
  let α := c.restrOpen V hVo
  have hαs : α.source = c.source ∩ V := rfl
  have hα : α ∈ IsManifold.maximalAtlas (𝓡 1) ∞ S := by
    apply α.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_chart (I := 𝓡 1) (n := ∞) (x := x)).mono inter_subset_left
    · exact (contMDiffOn_chart_symm (I := 𝓡 1) (n := ∞) (x := x)).mono inter_subset_left
  have hδ : δ ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M := by
    apply δ.mem_maximalAtlas_of_contMDiffOn
    · exact (halfSpaceRestriction_smooth β himage hβ).comp
        ((contMDiffOn_chart (I := 𝓡∂ 3) (n := ∞) (x := f x)).mono inter_subset_left)
        (fun _ hy => hy.2)
    · exact (contMDiffOn_chart_symm (I := 𝓡∂ 3) (n := ∞) (x := f x)).comp
        ((halfSpaceRestriction_inverse_smooth β himage hβi).mono inter_subset_left)
        (fun _ hy => hy.2)
  have hmaps : α.source ⊆ f ⁻¹' δ.source := by
    intro y hy
    have hm := hV hy.2
    exact ⟨hm.2.1,hm.2.2.1⟩
  have hxα : x ∈ α.source := ⟨mem_chart_source _ _,hxV⟩
  refine IsImmersionAtOfComplement.mk_of_charts standardBoundaryCurveEquiv α δ hxα
    (hmaps hxα) hα hδ hmaps ?_
  intro z hz
  let y := (α.extend (𝓡 1)).symm z
  have hys' : y ∈ (α.extend (𝓡 1)).source := (α.extend (𝓡 1)).map_target hz
  have hys : y ∈ α.source := by simpa only [OpenPartialHomeomorph.extend_source] using hys'
  have hEy : e y = z := (α.extend (𝓡 1)).right_inv hz
  have hfy : f y ∈ δ.source := hmaps hys
  have hη : (𝓡∂ 3) (η (d (f y))) = β (F y) :=
    halfSpaceRestriction_coordinate β himage (d (f y)) hfy.2
  change (𝓡∂ 3) (η (d (f y))) = standardBoundaryCurveEquiv (z,0)
  rw [hη,(hV hys.2).2.2.2,hEy]

end SeifertSurfaces.OriginalEndpoints.Section5.BoundaryNormalFormV488
