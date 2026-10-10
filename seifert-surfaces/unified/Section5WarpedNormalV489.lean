import Section5ActualAmbientFlowV488
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
noncomputable section
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ,E3) ∞ N]

theorem ambient_chart_differential_inverse (c : SmoothAmbientChart N) (p : N)
    (hp : p ∈ c.chart.source) (v : E3) :
    chartDifferential c p (inverseChartDifferential c (c.chart p) v) = v := by
  have hc : c.chart.MDifferentiable 𝓘(ℝ,E3) 𝓘(ℝ,E3) :=
    ⟨c.smooth.mdifferentiableOn (by simp),c.inverse_smooth.mdifferentiableOn (by simp)⟩
  have h := hc.comp_symm_deriv (c.chart.map_source hp)
  rw [c.chart.left_inv hp] at h
  exact congrArg (fun f => f v) h

theorem ambient_chart_inverse_differential (c : SmoothAmbientChart N) (p : N)
    (hp : p ∈ c.chart.source) (v : TangentSpace 𝓘(ℝ,E3) p) :
    inverseChartDifferential c (c.chart p) (chartDifferential c p v) = v := by
  have hc : c.chart.MDifferentiable 𝓘(ℝ,E3) 𝓘(ℝ,E3) :=
    ⟨c.smooth.mdifferentiableOn (by simp),c.inverse_smooth.mdifferentiableOn (by simp)⟩
  exact congrArg (fun f => f v) (hc.symm_comp_deriv hp)

theorem ambient_chart_inner (h : AmbientMetric N) (c : SmoothAmbientChart N) (y v w : E3) :
    coordinateInner (actualChartTensor h c) y v w =
      h.inner (c.chart.symm y) (inverseChartDifferential c y v) (inverseChartDifferential c y w) := by
  have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
    ext j
    simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
  have hdiff (v : E3) : inverseChartDifferential c y v =
      ∑ i : Fin 3, v i • inverseChartDifferential c y (coordinateVector 3 i) := by
    simpa only [map_sum,map_smul] using congrArg (inverseChartDifferential c y) (hsum v).symm
  unfold coordinateInner actualChartTensor
  rw [hdiff v,hdiff w,map_sum]
  simp only [map_smul,sum_apply,smul_apply,map_sum,smul_eq_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem warped_radial_differential {h : AmbientMetric N} {M : Set N}
    (C : WarpedBoundaryCollar h M) (p : N) (hp : p ∈ C.coordinates.chart.source) :
    mfderiv 𝓘(ℝ,E3) 𝓘(ℝ) C.radial p =
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)).comp (chartDifferential C.coordinates p) := by
  let P : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
  have he : C.radial =ᶠ[𝓝 p] P ∘ C.coordinates.chart := by
    filter_upwards [C.coordinates.chart.open_source.mem_nhds hp] with q hq
    exact C.radial_coordinate q hq
  rw [he.mfderiv_eq]
  have hc : C.coordinates.chart.MDifferentiable 𝓘(ℝ,E3) 𝓘(ℝ,E3) :=
    ⟨C.coordinates.smooth.mdifferentiableOn (by simp),
      C.coordinates.inverse_smooth.mdifferentiableOn (by simp)⟩
  rw [mfderiv_comp p P.differentiableAt.mdifferentiableAt (hc.mdifferentiableAt hp)]
  rw [mfderiv_eq_fderiv,P.fderiv]
  rfl

def warpedMetricNormal {h : AmbientMetric N} {M : Set N}
    (C : WarpedBoundaryCollar h M) (p : N) : TangentSpace 𝓘(ℝ,E3) p :=
  inverseChartDifferential C.coordinates (C.coordinates.chart p) (coordinateVector 3 0)

theorem warped_metric_normal_pairing {h : AmbientMetric N} {M : Set N}
    (C : WarpedBoundaryCollar h M) (p : N) (hp : p ∈ C.coordinates.chart.source)
    (w : TangentSpace 𝓘(ℝ,E3) p) :
    h.inner p (warpedMetricNormal C p) w = mfderiv 𝓘(ℝ,E3) 𝓘(ℝ) C.radial p w := by
  have hinner := ambient_chart_inner h C.coordinates (C.coordinates.chart p)
    (coordinateVector 3 0) (chartDifferential C.coordinates p w)
  rw [ambient_chart_inverse_differential C.coordinates p hp w,C.coordinates.chart.left_inv hp] at hinner
  apply hinner.symm.trans
  rw [C.warped_metric _ (C.coordinates.chart.map_source hp),warped_radial_differential C p hp]
  change (coordinateVector 3 0) 0 * (chartDifferential C.coordinates p w) 0 + _ = _
  simp only [levelVector,levelCoordinates,coordinateVector,EuclideanSpace.single,PiLp.single_apply]
  simp
  rfl

theorem warped_metric_normal_unit {h : AmbientMetric N} {M : Set N}
    (C : WarpedBoundaryCollar h M) (p : N) (hp : p ∈ C.coordinates.chart.source) :
    h.inner p (warpedMetricNormal C p) (warpedMetricNormal C p) = 1 := by
  rw [warped_metric_normal_pairing C p hp,warped_radial_differential C p hp]
  change (chartDifferential C.coordinates p
    (inverseChartDifferential C.coordinates (C.coordinates.chart p) (coordinateVector 3 0))) 0 = 1
  rw [ambient_chart_differential_inverse C.coordinates p hp]
  simp [coordinateVector,EuclideanSpace.single]

#print axioms warped_metric_normal_unit
#print axioms warped_metric_normal_pairing
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
