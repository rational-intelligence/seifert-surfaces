import B1ActualChartVectorField_v475

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
open DifferentialGeometry.Analysis.ODE
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem native_actual_chart_inverse_comp_v475 (c : SmoothAmbientChart ThreeSphere)
    (p : ThreeSphere) (hp : p ∈ c.chart.source) (v : TangentSpace (𝓡 3) p) :
    inverseChartDifferential c (c.chart p) (chartDifferential c p v) = v := by
  have hmd : c.chart.MDifferentiable (𝓡 3) 𝓘(ℝ,E3) :=
    ⟨c.smooth.mdifferentiableOn (by simp),c.inverse_smooth.mdifferentiableOn (by simp)⟩
  exact congrArg (fun L => L v) (hmd.symm_comp_deriv hp)

/-- A Euclidean solution of the actual chart velocity lifts to the actual
ambient integral curve. -/
theorem native_actual_chart_lift_curve_v475
    (X : NativeInteriorSmoothVectorField_v475 E) (c : SmoothAmbientChart ThreeSphere)
    (ψ : ℝ → E3) (a b : ℝ)
    (hψ : ∀ t ∈ Ioo a b, ψ t ∈ c.chart.target)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt ψ
      (chartDifferential c (c.chart.symm (ψ t)) (X.field (c.chart.symm (ψ t)))) t) :
    IsMIntegralCurveOn (c.chart.symm ∘ ψ) X.field (Ioo a b) := by
  intro t ht
  have hcinv : MDifferentiableAt 𝓘(ℝ,E3) (𝓡 3) c.chart.symm (ψ t) :=
    (c.inverse_smooth.contMDiffAt (c.chart.open_target.mem_nhds (hψ t ht))).mdifferentiableAt (by simp)
  have hd := hcinv.hasMFDerivAt.comp t (hderiv t ht).hasFDerivAt.hasMFDerivAt
  apply HasMFDerivAt.hasMFDerivWithinAt
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change mfderiv 𝓘(ℝ,E3) (𝓡 3) c.chart.symm (ψ t)
      ((NormedSpace.fromTangentSpace (ψ t)).symm
        (r • chartDifferential c (c.chart.symm (ψ t)) (X.field (c.chart.symm (ψ t))))) =
    r • X.field (c.chart.symm (ψ t))
  rw [map_smul,map_smul]
  congr 1
  have hinv := native_actual_chart_inverse_comp_v475 c (c.chart.symm (ψ t))
    (c.chart.map_target (hψ t ht)) (X.field (c.chart.symm (ψ t)))
  rw [c.chart.right_inv (hψ t ht)] at hinv
  exact hinv

/-- Uniqueness connects the lifted coordinate solution to the same native
admissible ambient flow, including negative times. -/
theorem native_actual_chart_flow_of_curve_v475
    (X : NativeInteriorSmoothVectorField_v475 E) (c : SmoothAmbientChart ThreeSphere)
    (ψ : ℝ → E3) (a b : ℝ) (h0 : (0 : ℝ) ∈ Ioo a b)
    (hψ : ∀ t ∈ Ioo a b, ψ t ∈ c.chart.target)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt ψ
      (chartDifferential c (c.chart.symm (ψ t)) (X.field (c.chart.symm (ψ t)))) t) :
    ∀ t ∈ Ioo a b,
      curveAt X.field (native_actual_field_complete_v475 X) (c.chart.symm (ψ 0)) t =
        c.chart.symm (ψ t) := by
  have hcurve := native_actual_chart_lift_curve_v475 X c ψ a b hψ hderiv
  have hactual := curveAt_integralCurve X.field (native_actual_field_complete_v475 X)
    (c.chart.symm (ψ 0))
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless h0
    (X.smooth.of_le (by simp)) (hactual.isMIntegralCurveOn _) hcurve
    (by exact curveAt_zero _ _ _)

#print axioms native_actual_chart_inverse_comp_v475
#print axioms native_actual_chart_lift_curve_v475
#print axioms native_actual_chart_flow_of_curve_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
