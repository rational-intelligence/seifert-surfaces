import GeometricCategory
import A7HalfSpaceExtensionV464
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource

private theorem euclidean_halfspace_cancel
    (g : Euc 2 → Euc 3) (f : Euc 2 → Euc 2) (y : Euc 2)
    (U : Set (Euc 2)) (hU : IsOpen U) (hy : f y ∈ U)
    (hyr : y ∈ range (𝓡∂ 2)) (hfyr : f y ∈ range (𝓡∂ 2))
    (hg : ContDiffOn ℝ ∞ g (U ∩ range (𝓡∂ 2)))
    (hinj : Function.Injective (fderivWithin ℝ g (range (𝓡∂ 2)) (f y)))
    (hf : ContinuousWithinAt f (range (𝓡∂ 2)) y)
    (hfmap : ∀ᶠ z in 𝓝[range (𝓡∂ 2)] y, f z ∈ range (𝓡∂ 2))
    (hgf : ContDiffWithinAt ℝ ∞ (g ∘ f) (range (𝓡∂ 2)) y) :
    ContDiffWithinAt ℝ ∞ f (range (𝓡∂ 2)) y := by
  obtain ⟨G, hG, hGg⟩ :=
    SeifertSurfaces.OriginalEndpoints.A7Support.exists_contDiff_extension_halfspace_local hU hg hy
  have hud := (𝓡∂ 2).uniqueDiffOn (f y) hfyr
  have hgm : U ∩ range (𝓡∂ 2) ∈ 𝓝[range (𝓡∂ 2)] (f y) :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hy)) self_mem_nhdsWithin
  have hgd : DifferentiableWithinAt ℝ g (range (𝓡∂ 2)) (f y) :=
    (hg (f y) ⟨hy, hfyr⟩).mono_of_mem_nhdsWithin hgm |>.differentiableWithinAt (by simp)
  have hGeq : fderiv ℝ G (f y) = fderivWithin ℝ g (range (𝓡∂ 2)) (f y) := by
    rw [← fderivWithin_eq_fderiv hud (hG.differentiable (by simp) _)]
    exact hGg.fderivWithin_eq_of_mem hfyr
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (show Function.Injective (fderiv ℝ G (f y)) by rwa [hGeq])
  have hLD : HasFDerivAt (L ∘ G)
      (ContinuousLinearEquiv.refl ℝ (Euc 2) : Euc 2 →L[ℝ] Euc 2) (f y) := by
    have hd := L.hasFDerivAt.comp (f y) (hG.differentiable (by simp) _).hasFDerivAt
    have he : L.comp (fderiv ℝ G (f y)) =
        (ContinuousLinearEquiv.refl ℝ (Euc 2) : Euc 2 →L[ℝ] Euc 2) := by
      apply ContinuousLinearMap.ext
      intro z
      exact hL z
    simpa only [he] using hd
  have hLG : ContDiffAt ℝ ∞ (L ∘ G) (f y) :=
    L.contDiff.contDiffAt.comp (f y) hG.contDiffAt
  have hft : Tendsto f (𝓝[range (𝓡∂ 2)] y) (𝓝[range (𝓡∂ 2)] (f y)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hf, hfmap⟩
  have hGfgf : (G ∘ f) =ᶠ[𝓝[range (𝓡∂ 2)] y] (g ∘ f) := hGg.comp_tendsto hft
  have hLGf : ContDiffWithinAt ℝ ∞ (L ∘ G ∘ f) (range (𝓡∂ 2)) y :=
    L.contDiff.contDiffAt.comp_contDiffWithinAt y (hgf.congr_of_eventuallyEq_of_mem hGfgf hyr)
  have hinv := hLG.to_localInverse hLD (by simp)
  have hinvEq := (hLG.hasStrictFDerivAt' hLD (by simp)).eventually_left_inverse
  have heq : ((hLG.localInverse hLD (by simp)) ∘ (L ∘ G ∘ f)) =ᶠ[𝓝[range (𝓡∂ 2)] y] f := hf.eventually hinvEq
  exact (hinv.comp_contDiffWithinAt y hLGf).congr_of_eventuallyEq_of_mem heq.symm hyr

universe u v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

private theorem image_chart_coordinate_extension
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (c : SmoothImageChart S F.map) (x : EuclideanHalfSpace 2) (hx : x ∈ c.chart.target) :
    ∃ U : Set (Euc 2), IsOpen U ∧ (𝓡∂ 2) x ∈ U ∧
      ContDiffOn ℝ ∞
        (extChartAt (𝓡∂ 3) (F.map (c.chart.symm x)) ∘ F.map ∘ c.chart.symm ∘ (𝓡∂ 2).symm)
        (U ∩ range (𝓡∂ 2)) := by
  let g : EuclideanHalfSpace 2 → M := F.map ∘ c.chart.symm
  let d := extChartAt (𝓡∂ 3) (g x)
  let W := c.chart.target ∩ g ⁻¹' d.source
  have hW : IsOpen W := c.cInfinity.continuousOn.isOpen_inter_preimage
    c.target_open (isOpen_extChartAt_source _)
  have hxW : x ∈ W := ⟨hx, mem_extChartAt_source (g x)⟩
  let U := (𝓡∂ 2).symm ⁻¹' W
  have hUx : (𝓡∂ 2) x ∈ U := by simpa only [U, mem_preimage, ModelWithCorners.left_inv] using hxW
  refine ⟨U, hW.preimage (𝓡∂ 2).continuous_symm, hUx, ?_⟩
  have hs : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ, Euc 3) ∞ (d ∘ g) W :=
    (contMDiffOn_iff_target.mp c.cInfinity).2 (g x)
  exact (hs.comp ((𝓡∂ 2).contMDiffOn_symm.mono inter_subset_right)
    (fun z hz => hz.1)).contDiffOn

/-- Every image-chart change is genuinely smooth, including at the source boundary. -/
theorem native_image_chart_transition_smooth
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (c d : SmoothImageChart S F.map) :
    ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (d.chart ∘ c.chart.symm)
      (c.chart.target ∩ c.chart.symm ⁻¹' d.chart.source) := by
  intro x hx
  let g : EuclideanHalfSpace 2 → M := F.map ∘ d.chart.symm
  let f : EuclideanHalfSpace 2 → EuclideanHalfSpace 2 := d.chart ∘ c.chart.symm
  have hcx : ContinuousAt c.chart.symm x :=
    (c.chart.symm.continuousOn x hx.1).continuousAt (c.target_open.mem_nhds hx.1)
  have hdx : ContinuousAt d.chart (c.chart.symm x) :=
    (d.chart.continuousOn _ hx.2).continuousAt (d.source_open.mem_nhds hx.2)
  have hf : ContinuousAt f x := hdx.comp hcx
  have hfx : f x ∈ d.chart.target := d.chart.map_source hx.2
  have hg : ContMDiffAt (𝓡∂ 2) (𝓡∂ 3) ∞ g (f x) :=
    d.cInfinity.contMDiffAt (d.target_open.mem_nhds hfx)
  have hinj := d.differential_injective (f x) hfx
  rw [mfderivWithin_of_mem_nhds (d.target_open.mem_nhds hfx)] at hinj
  have hcomp : ContMDiffAt (𝓡∂ 2) (𝓡∂ 3) ∞ (g ∘ f) x := by
    have he : (g ∘ f) =ᶠ[𝓝 x] (F.map ∘ c.chart.symm) := by
      filter_upwards [hcx.eventually (d.source_open.mem_nhds hx.2)] with z hz
      change F.map (d.chart.symm (d.chart (c.chart.symm z))) = F.map (c.chart.symm z)
      rw [d.chart.left_inv hz]
    exact (c.cInfinity.contMDiffAt (c.target_open.mem_nhds hx.1)).congr_of_eventuallyEq he
  let gu : Euc 2 → Euc 3 := extChartAt (𝓡∂ 3) (g (f x)) ∘ g ∘ (𝓡∂ 2).symm
  let fu : Euc 2 → Euc 2 := (𝓡∂ 2) ∘ f ∘ (𝓡∂ 2).symm
  have hfux : fu ((𝓡∂ 2) x) = (𝓡∂ 2) (f x) := by simp only [fu, Function.comp_apply, ModelWithCorners.left_inv]
  obtain ⟨U,hU,hfxU,hgu⟩ := image_chart_coordinate_extension F d (f x) hfx
  have hgD := (hg.mdifferentiableAt (by simp)).hasMFDerivAt.2
  change HasFDerivWithinAt gu
    ((tangentSpaceCastModel (𝓡∂ 3) (g (f x))).toContinuousLinearMap.comp
      ((mfderiv (𝓡∂ 2) (𝓡∂ 3) g (f x)).comp
        (tangentSpaceCastModel (𝓡∂ 2) (f x)).symm.toContinuousLinearMap))
    (range (𝓡∂ 2)) ((𝓡∂ 2) (f x)) at hgD
  have hiu : Function.Injective (fderivWithin ℝ gu (range (𝓡∂ 2)) ((𝓡∂ 2) (f x))) := by
    rw [hgD.fderivWithin ((𝓡∂ 2).uniqueDiffOn _ (mem_range_self _))]
    exact (tangentSpaceCastModel (𝓡∂ 3) (g (f x))).injective.comp
      (hinj.comp (tangentSpaceCastModel (𝓡∂ 2) (f x)).symm.injective)
  have hfu : ContinuousAt fu ((𝓡∂ 2) x) := by
    apply (𝓡∂ 2).continuousAt.comp
    apply ContinuousAt.comp _ (𝓡∂ 2).continuousAt_symm
    simpa only [ModelWithCorners.left_inv] using hf
  have hgufu : ContDiffWithinAt ℝ ∞ (gu ∘ fu) (range (𝓡∂ 2)) ((𝓡∂ 2) x) := by
    have h := (contMDiffAt_iff.mp hcomp).2
    simpa only [gu,fu,Function.comp_def,ModelWithCorners.left_inv, extChartAt_coe_symm, chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, extChartAt_self_apply, id_eq] using h
  have hfuSm : ContDiffWithinAt ℝ ∞ fu (range (𝓡∂ 2)) ((𝓡∂ 2) x) := by
    apply euclidean_halfspace_cancel gu fu ((𝓡∂ 2) x) U hU
    · simpa only [hfux] using hfxU
    · exact mem_range_self _
    · rw [hfux]; exact mem_range_self _
    · exact hgu
    · rwa [hfux]
    · exact hfu.continuousWithinAt
    · exact Filter.Eventually.of_forall (fun z => mem_range_self _)
    · exact hgufu
  exact (contMDiffAt_iff.mpr ⟨hf,hfuSm⟩).contMDiffWithinAt

#print axioms native_image_chart_transition_smooth
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
