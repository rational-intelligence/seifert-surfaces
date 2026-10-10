import A5NativeCenteredBoundaryHalfdisc
import A5BoundaryChartComposition
import A5BoundaryClockNeighborhood

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
universe u

/-- The actual native longitude clock and the centered C1 image chart
have the exact mutual image identities needed for differentiation and
straightening. Only continuity of the native source coordinates is used. -/
theorem native_centered_boundary_clock_compatibility
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (C : BoundaryC1ImageChart S E.Carrier F.map)
    (x : S) (hx : x ∈ C.chart.source) (hxb : x ∈ S.boundary)
    (c : SmoothAmbientChart ThreeSphere)
    (d : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2))
    (hds : d.source = univ) (hdt : d.target = univ)
    (hda : d (C.chart x) = 0) (hdia : d.symm 0 = C.chart x)
    (hdf : ∀ z, (𝓡∂ 2) (d z) = (𝓡∂ 2) z - (𝓡∂ 2) (C.chart x))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hmap : ∀ z ∈ closedHalfDisc ρ, d.symm ((𝓡∂ 2).symm z) ∈ C.chart.target)
    (b : ℝ → S) (hb0 : b 0 = x) (hbc : ContinuousAt b 0)
    (hbb : ∀ t, b t ∈ S.boundary)
    (hbi : IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => b t))
    (U : Set S) (hU : IsOpen U) (hxU : x ∈ U)
    (hcover : range (fun t : Ioo (-1 : ℝ) 1 => b t) = U ∩ S.boundary) :
    let f := c.chart ∘ E.toSphere ∘ F.map ∘ C.chart.symm ∘ d.symm ∘ (𝓡∂ 2).symm
    let q := (𝓡∂ 2) ∘ d ∘ C.chart ∘ b
    q 0 = 0 ∧ ContinuousAt q 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ closedHalfDisc ρ) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), q t 0 = 0) ∧
      (f ∘ q =ᶠ[𝓝 0] c.chart ∘ E.toSphere ∘ F.map ∘ b) ∧
      (∀ J ∈ 𝓝 (0 : ℝ), ∀ᶠ z in 𝓝[closedHalfDisc ρ] (0 : E2),
        z 0 = 0 → ∃ t ∈ J, f z = c.chart (E.toSphere (F.map (b t)))) := by
  dsimp only
  let f := c.chart ∘ E.toSphere ∘ F.map ∘ C.chart.symm ∘ d.symm ∘ (𝓡∂ 2).symm
  let q := (𝓡∂ 2) ∘ d ∘ C.chart ∘ b
  have hCb : ((𝓡∂ 2) (C.chart x)) 0 = 0 := by
    apply (model_halfspace_boundary_iff _).mp
    have hh : C.chart x ∈ C.chart '' (S.boundary ∩ C.chart.source) := ⟨x,⟨hxb,hx⟩,rfl⟩
    rw [C.boundary_image] at hh
    exact hh.1
  have hdc : Continuous d := continuousOn_univ.mp (hds ▸ d.continuousOn)
  have hdic : Continuous d.symm := continuousOn_univ.mp (hdt ▸ d.continuousOn_symm)
  have hqc : ContinuousAt q 0 := (𝓡∂ 2).continuous.continuousAt.comp
    (hdc.continuousAt.comp ((C.chart.continuousOn.continuousAt
      (C.source_open.mem_nhds (hb0.symm ▸ hx))).comp hbc))
  have hq0 : q 0 = 0 := by dsimp [q]; rw [hb0,hda]; rfl
  have hbC : ∀ᶠ t in 𝓝 (0 : ℝ), b t ∈ C.chart.source :=
    hbc.preimage_mem_nhds (hb0.symm ▸ C.source_open.mem_nhds hx)
  have hqmap : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ closedHalfDisc ρ := by
    have hh := hqc.preimage_mem_nhds (hq0.symm ▸ Metric.ball_mem_nhds (0 : E2) hρ)
    filter_upwards [hh] with t ht
    have ht' : q t ∈ Metric.ball 0 ρ := by simpa only [hq0,mem_preimage] using ht
    exact ⟨Metric.ball_subset_closedBall ht',(d (C.chart (b t))).property⟩
  have hqflat : ∀ᶠ t in 𝓝 (0 : ℝ), q t 0 = 0 := by
    filter_upwards [hbC] with t ht
    have hh : C.chart (b t) ∈ C.chart '' (S.boundary ∩ C.chart.source) :=
      ⟨b t,⟨hbb t,ht⟩,rfl⟩
    rw [C.boundary_image] at hh
    have ht0 := (model_halfspace_boundary_iff _).mp hh.1
    change ((𝓡∂ 2) (d (C.chart (b t)))) 0 = 0
    rw [hdf]
    simp only [PiLp.sub_apply,ht0,hCb,sub_self]
  have hfeq : f ∘ q =ᶠ[𝓝 0] c.chart ∘ E.toSphere ∘ F.map ∘ b := by
    filter_upwards [hbC] with t ht
    dsimp [f,q]
    have hmodel : (𝓡∂ 2).symm ((𝓡∂ 2) (d (C.chart (b t)))) =
        d (C.chart (b t)) := (𝓡∂ 2).left_inv _
    simp only [modelWithCornersEuclideanHalfSpace_apply] at hmodel
    rw [hmodel,d.left_inv (hds.symm ▸ mem_univ _),C.chart.left_inv ht]
  refine ⟨(by simpa [q] using hq0),(by simpa [q] using hqc),
    (by simpa [q] using hqmap),(by simpa [q] using hqflat),
    (by simpa [f,q] using hfeq),?_⟩
  let s := C.chart.symm ∘ d.symm ∘ (𝓡∂ 2).symm
  have hs0 : s 0 = x := by
    dsimp [s]
    rw [show (𝓡∂ 2).symm (0 : E2) = 0 from
      (𝓡∂ 2).left_inv (0 : EuclideanHalfSpace 2),hdia,C.chart.left_inv hx]
  have hinner : ContinuousWithinAt (d.symm ∘ (𝓡∂ 2).symm)
      (closedHalfDisc ρ) 0 :=
    hdic.continuousAt.comp_continuousWithinAt
      ((𝓡∂ 2).continuous_symm.continuousWithinAt)
  have hinner' : ContinuousWithinAt (C.chart.symm ∘ d.symm ∘ (𝓡∂ 2).symm)
      (closedHalfDisc ρ) 0 := by
    have hh : ContinuousAt C.chart.symm ((d.symm ∘ (𝓡∂ 2).symm) 0) :=
      C.chart.symm.continuousOn.continuousAt
      (C.target_open.mem_nhds (show d.symm ((𝓡∂ 2).symm (0 : E2)) ∈ C.chart.target by
        simpa only [show (𝓡∂ 2).symm (0 : E2) = 0 from (𝓡∂ 2).left_inv (0 : EuclideanHalfSpace 2),hdia]
          using C.chart.map_source hx))
    exact hh.comp_continuousWithinAt hinner
  have hsc : ContinuousWithinAt s (closedHalfDisc ρ) 0 := by
    simpa [s,Function.comp_def] using hinner'
  have hsB (z : E2) (hz : z ∈ closedHalfDisc ρ) (hz0 : z 0 = 0) : s z ∈ S.boundary := by
    have hzI : (𝓡∂ 2) ((𝓡∂ 2).symm z) = z :=
      (𝓡∂ 2).right_inv (by rw [range_modelWithCornersEuclideanHalfSpace]; exact hz.2)
    have hh := congrArg (fun v : E2 => v 0) (hdf (d.symm ((𝓡∂ 2).symm z)))
    rw [d.right_inv (hdt.symm ▸ mem_univ _),hzI] at hh
    simp only [PiLp.sub_apply,hCb,sub_zero,hz0] at hh
    have hzb : d.symm ((𝓡∂ 2).symm z) ∈
        C.chart '' (S.boundary ∩ C.chart.source) := by
      rw [C.boundary_image]
      exact ⟨(model_halfspace_boundary_iff _).mpr hh.symm,hmap z hz⟩
    obtain ⟨y,⟨hyB,hyC⟩,hy⟩ := hzb
    change C.chart.symm (d.symm ((𝓡∂ 2).symm z)) ∈ S.boundary
    rw [← hy,C.chart.left_inv hyC]
    exact hyB
  have hsmall := boundary_clock_coverage_under_continuous_lift S.boundary b hbi U hU
    (hb0.symm ▸ hxU) hcover (closedHalfDisc ρ) 0 s hsc (hs0.trans hb0.symm)
    {z : E2 | z 0 = 0} (fun z hz hz0 => hsB z hz hz0)
  intro J hJ
  filter_upwards [hsmall J hJ] with z hz
  intro hz0
  obtain ⟨t,ht,he⟩ := hz hz0
  exact ⟨t,ht,congrArg (c.chart ∘ E.toSphere ∘ F.map) he⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
