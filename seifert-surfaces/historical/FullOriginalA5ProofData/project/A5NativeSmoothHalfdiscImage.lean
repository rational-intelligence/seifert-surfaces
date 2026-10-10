import A5NativeHalfspaceImageChart
import A5NativeHalfspaceMetricGraph

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
universe u

/-- A regularized metric graph on an actual closed half-disc supplies a
literal boundary image chart of the original surface map. The projection
identity proves the immersion rank, including on the flat boundary. -/
theorem native_boundary_image_chart_of_smooth_metric_halfdisc
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (e : OpenPartialHomeomorph S (EuclideanHalfSpace 2)) (x : S)
    (hx : x ∈ e.source) (hcenter : (𝓡∂ 2) (e x) = 0)
    (hb : e '' (S.boundary ∩ e.source) =
      ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ e.target)
    (h : AmbientMetric ThreeSphere) (G : NativeMetricGraph h)
    (P : E3 →L[ℝ] E2)
    (hPo : P G.origin = 0) (hPp : ∀ v, P (G.plane v) = v)
    (hPn : P G.normal = 0)
    (r : ℝ) (hr : 0 < r)
    (hsmooth : ContDiffOn ℝ ∞ G.height (closedHalfDisc r))
    (hchart : MapsTo (E.toSphere ∘ F.map ∘ e.symm) e.target G.coordinates.chart.source)
    (hgraph : ∀ y ∈ e.target, ‖(𝓡∂ 2) y‖ < r →
      graphMap G.origin G.plane G.normal G.height ((𝓡∂ 2) y) =
        G.coordinates.chart (E.toSphere (F.map (e.symm y)))) :
    ∃ C : SmoothImageChart S F.map,
      x ∈ C.chart.source ∧ C.chart.source ⊆ e.source := by
  let V : Set (EuclideanHalfSpace 2) := (𝓡∂ 2) ⁻¹' Metric.ball 0 r
  have hV : IsOpen V := Metric.isOpen_ball.preimage (𝓡∂ 2).continuous
  let er := (e.symm.restrOpen V hV).symm
  have hxr : x ∈ er.source := by
    refine ⟨hx,?_⟩
    change (𝓡∂ 2) (e x) ∈ Metric.ball 0 r
    rw [hcenter]
    exact Metric.mem_ball_self hr
  have htarget (y : EuclideanHalfSpace 2) (hy : y ∈ er.target) :
      y ∈ e.target ∧ ‖(𝓡∂ 2) y‖ < r := by
    exact ⟨hy.1,by simpa only [V,mem_preimage,Metric.mem_ball,dist_zero_right] using hy.2⟩
  have hm (y : EuclideanHalfSpace 2) (hy : y ∈ er.target) :
      (𝓡∂ 2) y ∈ closedHalfDisc r :=
    ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using (htarget y hy).2.le,
      y.property⟩
  have hg : ContDiffOn ℝ ∞ (graphMap G.origin G.plane G.normal G.height)
      (closedHalfDisc r) :=
    (contDiffOn_const.add G.plane.contDiff.contDiffOn).add
      (hsmooth.smul contDiffOn_const)
  let f := G.coordinates.chart ∘ E.toSphere ∘ F.map ∘ er.symm
  have hf : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,E3) ∞ f er.target := by
    have hh := hg.contMDiffOn.comp (𝓡∂ 2).contMDiff.contMDiffOn (fun y hy => hm y hy)
    apply hh.congr
    intro y hy
    exact (hgraph y (htarget y hy).1 (htarget y hy).2).symm
  have hrank (y : EuclideanHalfSpace 2) (hy : y ∈ er.target) :
      Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) f y) := by
    have heq : P ∘ f =ᶠ[𝓝 y] (𝓡∂ 2) := by
      filter_upwards [er.open_target.mem_nhds hy] with z hz
      change P (G.coordinates.chart (E.toSphere (F.map (e.symm z)))) = _
      rw [← hgraph z (htarget z hz).1 (htarget z hz).2]
      simp only [graphMap,map_add,map_smul,hPo,hPp,hPn,smul_zero,zero_add,add_zero]
    have hi : Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,E2) (P ∘ f) y) := by
      rw [heq.mfderiv_eq]
      exact ((𝓡∂ 2).isImmersion (n := 1)).mfderiv_injective (by decide) y
    rw [mfderiv_comp y P.mdifferentiableAt
      ((hf.contMDiffAt (er.open_target.mem_nhds hy)).mdifferentiableAt (by simp))] at hi
    exact Function.Injective.of_comp hi
  have hbr : er '' (S.boundary ∩ er.source) =
      ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ er.target := by
    ext y
    constructor
    · rintro ⟨z,⟨hzB,hz⟩,rfl⟩
      have hzb : e z ∈ ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ e.target := by
        rw [← hb]
        exact ⟨z,⟨hzB,hz.1⟩,rfl⟩
      exact ⟨hzb.1,er.map_source hz⟩
    · intro hy
      have heB : y ∈ e '' (S.boundary ∩ e.source) := hb.symm ▸ ⟨hy.1,hy.2.1⟩
      obtain ⟨z,⟨hzB,hze⟩,hzy⟩ := heB
      refine ⟨z,⟨hzB,⟨hze,?_⟩⟩,hzy⟩
      change e z ∈ V
      rw [hzy]
      exact hy.2.2
  obtain ⟨C,hC⟩ := native_halfspace_image_chart_of_coordinate_parametrization E F
    er.toPartialHomeomorph er.open_source er.open_target hbr G.coordinates
    (fun y hy => hchart hy.1) hf hrank
  refine ⟨C,?_,?_⟩
  · rw [hC]
    exact hxr
  · rw [hC]
    exact fun y hy => hy.1

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
