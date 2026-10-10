import B1L1DirectWeakLower
import DifferentialGeometry.External.DeGiorgi.StampacchiaTruncation

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem native_weak_gradient_on_equal_set
    (u v : E2 → ℝ) (hu : Measurable u) (hv : Measurable v)
    (U : Set E2) (hU : IsOpen U)
    (wu : DeGiorgi.MemW1pWitness 2 u U)
    (wv : DeGiorgi.MemW1pWitness 2 v U) (j : Fin 2) :
    ∀ᵐ x ∂volume.restrict U, u x = v x → wu.weakGrad x j = wv.weakGrad x j := by
  let w := wu.add (wv.smul (-1))
  have hm : Measurable (fun x => u x + -1 * v x) := hu.add (hv.const_mul (-1))
  have hz := DeGiorgi.weakGrad_ae_eq_zero_on_zeroSet hU w.memW1p w.isWeakGrad j
    (w.weakGrad_component_memLp j) hm
  filter_upwards [hz] with x hx he
  have hzero : u x + -1 * v x = 0 := by rw [he]; ring
  have hgrad := hx hzero
  change (wu.weakGrad x + -1 • wv.weakGrad x) j = 0 at hgrad
  simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, neg_one_mul,
    ← sub_eq_add_neg, sub_eq_zero] using hgrad

private def native_W12_of_H1 (U : Set E2) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du) : DeGiorgi.MemW1pWitness 2 u U where
  memLp := hu.2.1
  weakGrad := du
  weakGrad_component_memLp := fun j => hu.2.2.eval_piLp j
  isWeakGrad := by
    intro j phi hp hc hs
    have hbasis : EuclideanSpace.single j 1 = coordinateVector 2 j := by
      ext k
      simp [coordinateVector, EuclideanSpace.single]
    rw [hbasis]
    exact hu.1.2.2 phi hp hc hs j

private def native_W12_congr (u v : E2 → ℝ) (U : Set E2)
    (wu : DeGiorgi.MemW1pWitness 2 u U)
    (he : u =ᵐ[volume.restrict U] v) : DeGiorgi.MemW1pWitness 2 v U where
  memLp := wu.memLp.ae_eq he
  weakGrad := wu.weakGrad
  weakGrad_component_memLp := wu.weakGrad_component_memLp
  isWeakGrad := by
    intro j phi hp hc hs
    have hi := wu.isWeakGrad j phi hp hc hs
    have hleft : (∫ x in U, v x * fderiv ℝ phi x (EuclideanSpace.single j 1)) =
        ∫ x in U, u x * fderiv ℝ phi x (EuclideanSpace.single j 1) :=
      integral_congr_ae (he.symm.mul EventuallyEq.rfl)
    exact hleft.trans hi

private theorem native_weak_gradient_locality
    (u v : E2 → ℝ) (U : Set E2) (hU : IsOpen U)
    (wu : DeGiorgi.MemW1pWitness 2 u U)
    (wv : DeGiorgi.MemW1pWitness 2 v U) (j : Fin 2) :
    ∀ᵐ x ∂volume.restrict U, u x = v x → wu.weakGrad x j = wv.weakGrad x j := by
  have hu := wu.memLp.aestronglyMeasurable.aemeasurable
  have hv := wv.memLp.aestronglyMeasurable.aemeasurable
  let u0 := hu.mk u
  let v0 := hv.mk v
  let wu0 := native_W12_congr u u0 U wu hu.ae_eq_mk
  let wv0 := native_W12_congr v v0 U wv hv.ae_eq_mk
  have hg := native_weak_gradient_on_equal_set u0 v0 hu.measurable_mk hv.measurable_mk
    U hU wu0 wv0 j
  filter_upwards [hu.ae_eq_mk, hv.ae_eq_mk, hg] with x hux hvx hx heq
  apply hx
  change AEMeasurable.mk u hu x = AEMeasurable.mk v hv x
  rw [← hux, ← hvx]
  exact heq

private theorem continuous_memLp_on_disc (v : E2 → ℝ) (hv : Continuous v) :
    MemLp v 2 (volume.restrict (disc 1)) := by
  letI : IsFiniteMeasure (volume.restrict (disc 1)) := isFiniteMeasure_restrict.mpr
    (measure_ball_lt_top (μ := volume) (x := (0 : E2)) (r := 1)).ne
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E2) 1).exists_bound_of_continuousOn
    hv.continuousOn
  apply MemLp.of_bound hv.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  exact hC x (Metric.ball_subset_closedBall hx)

private def native_W12_of_C1 (v : E2 → ℝ) (hv : ContDiff ℝ 1 v) :
    DeGiorgi.MemW1pWitness 2 v (disc 1) where
  memLp := continuous_memLp_on_disc v hv.continuous
  weakGrad := fun x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun j => fderiv ℝ v x (coordinateVector 2 j))
  weakGrad_component_memLp := by
    intro j
    exact continuous_memLp_on_disc _
      ((hv.continuous_fderiv (by simp)).clm_apply continuous_const)
  isWeakGrad := by
    intro j
    have hbasis : EuclideanSpace.single j 1 = coordinateVector 2 j := by
      ext k
      simp [coordinateVector, EuclideanSpace.single]
    have hraw := DeGiorgi.HasWeakPartialDeriv.of_contDiff (Ω := disc 1) (i := j)
      Metric.isOpen_ball (hv.of_le (by simp))
    have he : (fun x => ((EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun k => fderiv ℝ v x (coordinateVector 2 k))) j) =
        (fun x => fderiv ℝ v x (coordinateVector 2 j)) := by
      funext x
      rfl
    rw [he]
    simpa only [hbasis] using hraw

private theorem original_weak_jets_on_C1_equal_set
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (v : E2 → E2) (hv : ContDiff ℝ 1 v) :
    ∀ᵐ x ∂volume.restrict (disc 1), u x = v x →
      ∀ i j, d i x j = (fderiv ℝ v x (coordinateVector 2 j)) i := by
  have hvc (i : Fin 2) : ContDiff ℝ 1 (fun x => v x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hv
  have he (i j : Fin 2) : ∀ᵐ x ∂volume.restrict (disc 1),
      u x i = v x i → d i x j = fderiv ℝ (fun x => v x i) x (coordinateVector 2 j) :=
    native_weak_gradient_locality _ _ _ Metric.isOpen_ball
      (native_W12_of_H1 _ _ _ (hH1 i))
      (native_W12_of_C1 _ (hvc i)) j
  have hae : ∀ᵐ x ∂volume.restrict (disc 1), ∀ i j, u x i = v x i →
      d i x j = fderiv ℝ (fun x => v x i) x (coordinateVector 2 j) := by
    exact ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => he i j))
  filter_upwards [hae] with x hx hsame i j
  have hdx := (hv.differentiable (by simp) x).hasFDerivAt
  have hc := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hdx).fderiv
  have hcoord : u x i = v x i := congrArg (fun z : E2 => z i) hsame
  rw [hx i j hcoord]
  change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i) ∘ v) x
      (coordinateVector 2 j) = _
  rw [hc]
  rfl

#print axioms native_weak_gradient_on_equal_set
#print axioms native_W12_of_H1
#print axioms native_weak_gradient_locality
#print axioms native_W12_of_C1
#print axioms original_weak_jets_on_C1_equal_set

private theorem native_linear_det_eq_coordinate_det (L : E2 →L[ℝ] E2) :
    L.det = Matrix.det (fun i j : Fin 2 => (L (coordinateVector 2 j)) i) := by
  change LinearMap.det L.toLinearMap = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  congr 1

private theorem original_weak_det_on_C1_equal_set
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (v : E2 → E2) (hv : ContDiff ℝ 1 v) :
    ∀ᵐ x ∂volume.restrict (disc 1), u x = v x →
      (fderiv ℝ v x).det = Matrix.det (weakJacobian d x) := by
  filter_upwards [original_weak_jets_on_C1_equal_set u d hH1 v hv]
    with x hx he
  rw [native_linear_det_eq_coordinate_det]
  congr 1
  ext i j
  exact (hx he i j).symm

#print axioms native_linear_det_eq_coordinate_det
#print axioms original_weak_det_on_C1_equal_set
