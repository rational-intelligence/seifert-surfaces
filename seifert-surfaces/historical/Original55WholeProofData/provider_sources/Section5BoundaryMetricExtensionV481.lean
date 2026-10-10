import Section5BoundaryCoordinateExtensionV481
import Section5StrictBoundaryTransportV481

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

private theorem tangent_map_cast (f : ThreeSphere → E3) (x z : ThreeSphere)
    (hx : x = z) (v : TangentSpace 𝓘(ℝ, E3) z) :
    (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) f x) (hx.symm ▸ v) =
      (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) f z) v := by
  subst z
  rfl

private theorem inner_cast (g : AmbientMetric ThreeSphere) (x z : ThreeSphere)
    (hx : x = z) (u v : TangentSpace 𝓘(ℝ, E3) z) :
    g.inner x (hx.symm ▸ u) (hx.symm ▸ v) = g.inner z u v := by
  subst z
  rfl

/-- Native halfspace coefficients agree with the actual ambient metric in any
ambient chart extending those same native coordinates on a neighborhood. -/
theorem native_metric_eq_ambient_chart
    (H : Section4.SourceGeometry E) (p : E.Carrier)
    (c : SmoothAmbientChart ThreeSphere) (V : Set E.Carrier) (hV : IsOpen V)
    (hagree : ∀ q ∈ V, E.toSphere q ∈ c.chart.source ∧
      c.chart (E.toSphere q) = extChartAt (𝓡∂ 3) p q)
    (y : E3) (hy : y ∈ (extChartAt (𝓡∂ 3) p).target)
    (hyV : (extChartAt (𝓡∂ 3) p).symm y ∈ V) :
    actualChartTensor H.ambient.extension c y = MetricInChart (𝓡∂ 3) H.metric p y := by
  let q := (extChartAt (𝓡∂ 3) p).symm y
  have hq := hagree q hyV
  have hcoord : c.chart (E.toSphere q) = y := hq.2.trans ((extChartAt (𝓡∂ 3) p).right_inv hy)
  have hpoint : c.chart.symm y = E.toSphere q := by
    rw [← hcoord]
    exact c.chart.left_inv hq.1
  have hev : (c.chart ∘ E.toSphere) =ᶠ[𝓝 q] (extChartAt (𝓡∂ 3) p) := by
    filter_upwards [hV.mem_nhds hyV] with z hz
    exact (hagree z hz).2
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) 𝓘(ℝ, E3) ∞ E.toSphere := E.inclusion
  have hcMD : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
    ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
  have hdc : (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (E.toSphere q)).comp
      (mfderiv (𝓡∂ 3) 𝓘(ℝ, E3) E.toSphere q) =
      mfderiv (𝓡∂ 3) 𝓘(ℝ, E3) (extChartAt (𝓡∂ 3) p) q := by
    rw [← mfderiv_comp q (hcMD.mdifferentiableAt hq.1)
      (hinc.isImmersion.contMDiff.mdifferentiableAt (by simp))]
    exact hev.mfderiv_eq
  have hdx := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy
  have hcomp : (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (E.toSphere q)).comp
      ((mfderiv (𝓡∂ 3) 𝓘(ℝ, E3) E.toSphere q).comp
        (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (extChartAt (𝓡∂ 3) p).symm
          (range (𝓡∂ 3)) y)) = ContinuousLinearMap.id ℝ E3 := by
    rw [← ContinuousLinearMap.comp_assoc, hdc]
    exact hdx
  have hcy : y ∈ c.chart.target := hcoord ▸ c.chart.map_source hq.1
  have hinv : (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (c.chart.symm y)).comp
      (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y) = ContinuousLinearMap.id ℝ E3 := by
    rw [← mfderiv_comp y (hcMD.mdifferentiableAt (c.chart.map_target hcy))
      (hcMD.symm.mdifferentiableAt hcy)]
    have hi : c.chart ∘ c.chart.symm =ᶠ[𝓝 y] id := by
      filter_upwards [c.chart.open_target.mem_nhds hcy] with z hz
      exact c.chart.right_inv hz
    rw [hi.mfderiv_eq]
    exact mfderiv_id
  have heqD : ∀ v : E3,
      inverseChartDifferential c y v =
        (hpoint.symm ▸ mfderiv (𝓡∂ 3) 𝓘(ℝ, E3) E.toSphere q
          (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (extChartAt (𝓡∂ 3) p).symm
            (range (𝓡∂ 3)) y v)) := by
    intro v
    apply (hcMD.mfderiv_bijective (c.chart.map_target hcy)).1
    have hh := congrArg (fun L : E3 →L[ℝ] E3 => L v) hcomp
    have hi := congrArg (fun L : E3 →L[ℝ] E3 =>
      L ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)) hinv
    change (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (c.chart.symm y))
      ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y)
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)) = _
    change (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (c.chart.symm y))
      ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y)
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)) = v at hi
    change (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (E.toSphere q))
      ((mfderiv (𝓡∂ 3) 𝓘(ℝ, E3) E.toSphere q)
        ((mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (extChartAt (𝓡∂ 3) p).symm
          (range (𝓡∂ 3)) y) v)) = v at hh
    exact hi.trans ((tangent_map_cast c.chart _ _ hpoint _).trans hh).symm
  ext i j
  unfold actualChartTensor MetricInChart
  rw [heqD, heqD]
  erw [inner_cast H.ambient.extension _ _ hpoint]
  exact (H.ambient.metric_restriction q
    (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (extChartAt (𝓡∂ 3) p).symm
      (range (𝓡∂ 3)) y (EuclideanSpace.single i 1))
    (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (extChartAt (𝓡∂ 3) p).symm
      (range (𝓡∂ 3)) y (EuclideanSpace.single j 1))).symm

/-- The actual metric in a native boundary chart has a smooth positive-definite
extension obtained from the very same sphere metric and exterior inclusion. -/
theorem source_boundary_metric_extension
    (H : Section4.SourceGeometry E) (p : E.Carrier)
    (C : WarpedBoundaryCollar H.ambient.extension (range E.toSphere))
    (hp : E.toSphere p ∈ C.coordinates.chart.source) :
    ∃ c : SmoothAmbientChart ThreeSphere,
      E.toSphere p ∈ c.chart.source ∧
      c.chart (E.toSphere p) = extChartAt (𝓡∂ 3) p p ∧
      (∀ᶠ q in 𝓝 p, E.toSphere q ∈ c.chart.source ∧
        c.chart (E.toSphere q) = extChartAt (𝓡∂ 3) p q) ∧
      ∃ V : Set E3, IsOpen V ∧ extChartAt (𝓡∂ 3) p p ∈ V ∧
        V ⊆ c.chart.target ∧
        (∀ y ∈ V ∩ (extChartAt (𝓡∂ 3) p).target,
          actualChartTensor H.ambient.extension c y =
            MetricInChart (𝓡∂ 3) H.metric p y) ∧
        Nonempty (CoordinateMetric V) := by
  obtain ⟨c, hpc, hcp, hev⟩ := source_boundary_ambient_chart H p C hp
  refine ⟨c, hpc, hcp, hev, ?_⟩
  obtain ⟨W, hWsub, hWo, hpW⟩ := mem_nhds_iff.mp hev
  have hty : extChartAt (𝓡∂ 3) p p ∈ c.chart.target := hcp ▸ c.chart.map_source hpc
  have hsym : (extChartAt (𝓡∂ 3) p).symm (extChartAt (𝓡∂ 3) p p) = p :=
    (extChartAt (𝓡∂ 3) p).left_inv (mem_extChartAt_source p)
  have hn : c.chart.target ∩ (extChartAt (𝓡∂ 3) p).symm ⁻¹' W ∈
      𝓝 (extChartAt (𝓡∂ 3) p p) := by
    apply inter_mem (c.chart.open_target.mem_nhds hty)
    apply (continuousAt_extChartAt_symm p).preimage_mem_nhds
    rw [hsym]
    exact hWo.mem_nhds hpW
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp hn
  refine ⟨V, hVo, hxV, fun y hy => (hVsub hy).1, ?_, ?_⟩
  · intro y hy
    exact native_metric_eq_ambient_chart H p c W hWo
      (fun q hq => hWsub hq) y hy.2 (hVsub hy.1).2
  · obtain ⟨hs, hsymm, hpos⟩ :=
      A4GeometryBridges.actual_chart_tensor_metric_properties H.ambient.extension c
    exact ⟨{ tensor := actualChartTensor H.ambient.extension c
             smooth := fun i j => (hs i j).mono (fun y hy => (hVsub hy).1)
             symmetric := fun y hy => hsymm y (hVsub hy).1
             positive := fun y hy => hpos y (hVsub hy).1 }⟩

#print axioms native_metric_eq_ambient_chart
#print axioms source_boundary_metric_extension
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
