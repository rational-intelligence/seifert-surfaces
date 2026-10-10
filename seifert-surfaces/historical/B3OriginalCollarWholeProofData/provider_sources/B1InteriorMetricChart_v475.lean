import B1InteriorDensityTransport_v475
import B1InteriorIsothermalAlgebra_v475
import B1BoundaryMetricProvider_v466
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The existing closed-domain metric parametrization restricts to an actual
open C1 isothermal interior chart, with ordinary derivatives. -/
theorem native_metric_parametrization_interior_chart_v475
    {R : ℝ} {A : E2 → Mat2} (G : InverseMetricData R A)
    (Ω : SmoothFlatJordanDomain R) (P : MetricDiscParametrization G Ω)
    (hdet : ∀ x ∈ closure Ω.domain, Matrix.det (A x) = 1) :
    ∃ F : NativeInteriorChart_v475,
      F.chart.source = Ω.domain ∧ F.chart.target = disc 1 ∧
      (∀ x, F.chart x = P.tau.symm x) ∧
      (∀ z, F.chart.symm z = P.tau z) ∧
      (∀ z ∈ F.chart.target, densityLeading A F.chart (F.chart.symm z) = 1) := by
  classical
  have hclosed : disc (1:ℝ) ⊆ closedDisc 1 := Metric.ball_subset_closedBall
  have hPsource (z : E2) (hz : z ∈ disc 1) : z ∈ P.tau.source :=
    P.source_eq.symm ▸ hclosed hz
  have hPtarget (x : E2) (hx : x ∈ Ω.domain) : x ∈ P.tau.target :=
    P.target_eq.symm ▸ subset_closure hx
  have himg (z : E2) (hz : z ∈ disc 1) : P.tau z ∈ Ω.domain := by
    rw [← P.interior_image]
    exact mem_image_of_mem P.tau hz
  have hinv (x : E2) (hx : x ∈ Ω.domain) : P.tau.symm x ∈ disc 1 := by
    rw [← P.inverse_interior_image]
    exact mem_image_of_mem P.tau.symm hx
  let χ : PartialHomeomorph E2 E2 :=
    { toFun := P.tau.symm
      invFun := P.tau
      source := Ω.domain
      target := disc 1
      map_source' := hinv
      map_target' := himg
      left_inv' := fun x hx => P.tau.right_inv (hPtarget x hx)
      right_inv' := fun z hz => P.tau.left_inv (hPsource z hz)
      continuousOn_toFun := P.inverse_C1.continuousOn.mono subset_closure
      continuousOn_invFun := P.forward_C1.continuousOn.mono hclosed }
  have hforward : ContDiffOn ℝ 1 χ χ.source := P.inverse_C1.mono subset_closure
  have hinverse : ContDiffOn ℝ 1 χ.symm χ.target := P.forward_C1.mono hclosed
  have hsrc : χ.source = Ω.domain := rfl
  have htgt : χ.target = disc 1 := rfl
  have hfj (x : E2) (hx : x ∈ Ω.domain) :
      jacobian χ x = jacobianWithin P.tau.symm (closure Ω.domain) x := by
    unfold jacobian jacobianWithin
    change (fun i j => (fderiv ℝ P.tau.symm x (coordinateVector 2 j)) i) = _
    rw [fderivWithin_of_mem_nhds (Filter.mem_of_superset (Ω.open_domain.mem_nhds hx) subset_closure)]
  have hij (z : E2) (hz : z ∈ disc 1) :
      jacobian χ.symm z = jacobianWithin P.tau (closedDisc 1) z := by
    unfold jacobian jacobianWithin
    change (fun i j => (fderiv ℝ P.tau z (coordinateVector 2 j)) i) = _
    rw [fderivWithin_of_mem_nhds (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) hclosed)]
  have hfd (x : E2) (hx : x ∈ χ.source) : DifferentiableAt ℝ χ x :=
    ((hforward x hx).contDiffAt (Ω.open_domain.mem_nhds hx)).differentiableAt (by simp)
  have hid (z : E2) (hz : z ∈ χ.target) : DifferentiableAt ℝ χ.symm z :=
    ((hinverse z hz).contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  have hχdet (x : E2) (hx : x ∈ χ.source) : Matrix.det (jacobian χ x) ≠ 0 := by
    rw [hfj x hx]
    exact P.inverse_det x (subset_closure hx)
  let F : NativeInteriorChart_v475 :=
    { chart := χ
      source_open := Ω.open_domain
      target_open := Metric.isOpen_ball
      forward_C1 := hforward
      inverse_C1 := hinverse
      forward_det := hχdet }
  refine ⟨F,rfl,rfl,fun x => rfl,fun z => rfl,?_⟩
  intro z hz
  let x := χ.symm z
  let M := jacobian χ x
  let D := jacobian χ.symm z
  have hx : x ∈ χ.source := χ.map_target hz
  have hjac (f : E2 → E2) (y : E2) :
      LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (fderiv ℝ f y).toLinearMap = jacobian f y := by
    ext i j
    simp [LinearMap.toMatrix_apply,jacobian,coordinateVector,EuclideanSpace.basisFun_apply]
  have hMD : M*D = 1 := by
    have hcomp := (hfd x hx).hasFDerivAt.comp z (hid z hz).hasFDerivAt
    have hev : (fun y : E2 => y) =ᶠ[𝓝 z] χ ∘ χ.symm := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      exact (χ.right_inv hy).symm
    have hd := (hcomp.congr_of_eventuallyEq hev).unique (hasFDerivAt_id z)
    have hm := congrArg (fun L : E2 →L[ℝ] E2 =>
      LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis L.toLinearMap) hd
    change LinearMap.toMatrix _ _ ((fderiv ℝ χ x).toLinearMap.comp
      (fderiv ℝ χ.symm z).toLinearMap) = LinearMap.toMatrix _ _ LinearMap.id at hm
    rw [LinearMap.toMatrix_comp _ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis _,hjac,hjac,
      LinearMap.toMatrix_id] at hm
    exact hm
  have hmu : IsUnit (Matrix.det M) := isUnit_iff_ne_zero.mpr (hχdet x hx)
  have hD : D = M⁻¹ := by
    have hh := congrArg (fun B : Mat2 => M⁻¹*B) hMD
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul M hmu,
      Matrix.one_mul, Matrix.mul_one] using hh
  have hDM : D*M = 1 := by rw [hD, Matrix.nonsing_inv_mul M hmu]
  have hconf : D.transpose*(A x)⁻¹*D = P.lambda z • (1:Mat2) := by
    change (jacobian χ.symm z).transpose*(A (P.tau z))⁻¹*jacobian χ.symm z = _
    rw [hij z hz]
    exact P.conformal z (hclosed hz)
  have hi : (A x)⁻¹ = P.lambda z • (M.transpose*M) := by
    calc
      (A x)⁻¹ = (M.transpose*D.transpose)*(A x)⁻¹*(D*M) := by
        rw [← Matrix.transpose_mul,hDM,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one]
      _ = M.transpose*(D.transpose*(A x)⁻¹*D)*M := by simp only [Matrix.mul_assoc]
      _ = P.lambda z • (M.transpose*M) := by
        rw [hconf]
        simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]
  change densityLeading A χ x = 1
  exact native_interior_isothermal_density_algebra_v475 (A x) M
    (hdet x (subset_closure hx)) (hχdet x hx) (P.lambda z) (P.lambda_pos z (hclosed hz)) hi

#print axioms native_metric_parametrization_interior_chart_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
