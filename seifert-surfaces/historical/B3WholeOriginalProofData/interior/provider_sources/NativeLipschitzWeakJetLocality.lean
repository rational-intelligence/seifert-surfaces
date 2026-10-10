import NativeWeakJetLocality
import Mathlib.Analysis.Calculus.Rademacher

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

private theorem lipschitz_memLp_on_disc
    (v : E2 → ℝ) (C : ℝ≥0) (hv : LipschitzWith C v) :
    MemLp v 2 (volume.restrict (disc 1)) := by
  let : IsFiniteMeasure (volume.restrict (disc 1)) := isFiniteMeasure_restrict.mpr
    (measure_ball_lt_top (μ := volume) (x := (0 : E2)) (r := 1)).ne
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E2) 1).exists_bound_of_continuousOn
    hv.continuous.continuousOn
  apply MemLp.of_bound hv.continuous.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  exact hB x (Metric.ball_subset_closedBall hx)

private def native_W12_of_lipschitz
    (v : E2 → ℝ) (C : ℝ≥0) (hv : LipschitzWith C v) :
    DeGiorgi.MemW1pWitness 2 v (disc 1) where
  memLp := lipschitz_memLp_on_disc v C hv
  weakGrad := fun x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun j => lineDeriv ℝ v x (coordinateVector 2 j))
  weakGrad_component_memLp := by
    intro j
    let : IsFiniteMeasure (volume.restrict (disc 1)) := isFiniteMeasure_restrict.mpr
      (measure_ball_lt_top (μ := volume) (x := (0 : E2)) (r := 1)).ne
    apply MemLp.of_bound (aestronglyMeasurable_lineDeriv hv.continuous _) (C * ‖coordinateVector 2 j‖)
    filter_upwards with x
    exact norm_lineDeriv_le_of_lipschitz ℝ hv
  isWeakGrad := by
    intro j phi hp hc hs
    let ei : E2 := EuclideanSpace.single j 1
    have hbasis : ei = coordinateVector 2 j := by
      ext k
      simp [ei, coordinateVector, EuclideanSpace.single]
    obtain ⟨B, hpLip⟩ := hp.lipschitzWith_of_hasCompactSupport hc (by simp)
    have hraw := hv.integral_lineDeriv_mul_eq (μ := volume) hpLip hc ei
    have he : (fun x => lineDeriv ℝ phi x (-ei) * v x) =
        (fun x => -(v x * fderiv ℝ phi x ei)) := by
      funext x
      rw [(hp.differentiable (by simp) x).lineDeriv_eq_fderiv]
      simp only [map_neg, neg_mul]
      ring
    rw [he, integral_neg] at hraw
    have hleft : (∫ x in disc 1, lineDeriv ℝ v x ei * phi x) =
        ∫ x, lineDeriv ℝ v x ei * phi x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : phi x = 0 := by
        by_contra hn
        exact hx (hs (subset_tsupport phi hn))
      rw [hz, mul_zero]
    have hright : (∫ x in disc 1, v x * fderiv ℝ phi x ei) =
        ∫ x, v x * fderiv ℝ phi x ei := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : fderiv ℝ phi x ei = 0 := by
        by_contra hn
        exact hx (((tsupport_fderiv_apply_subset ℝ ei).trans hs)
          (subset_tsupport _ hn))
      rw [hz, mul_zero]
    change (∫ x in disc 1, v x * fderiv ℝ phi x ei) =
      -(∫ x in disc 1,
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun k => lineDeriv ℝ v x (coordinateVector 2 k))) j * phi x)
    have hcoord : (fun x =>
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun k => lineDeriv ℝ v x (coordinateVector 2 k))) j * phi x) =
        (fun x => lineDeriv ℝ v x ei * phi x) := by
      funext x
      rw [hbasis]
      rfl
    rw [hcoord, hleft, hright]
    linarith [hraw]

private theorem native_lipschitz_weak_gradient_locality
    (u v : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (disc 1) u du) (C : ℝ≥0) (hv : LipschitzWith C v) (j : Fin 2) :
    ∀ᵐ x ∂volume.restrict (disc 1), u x = v x →
      du x j = lineDeriv ℝ v x (coordinateVector 2 j) := by
  run_tac do
    let wn := (Lean.Name.num `_private.NativeWeakJetLocality 0).str "native_W12_of_H1"
    let ln := (Lean.Name.num `_private.NativeWeakJetLocality 0).str "native_weak_gradient_locality"
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact $(Lean.mkIdent ln) $(Lean.mkIdent `u) $(Lean.mkIdent `v)
        (disc 1) Metric.isOpen_ball
        ($(Lean.mkIdent wn) (disc 1) $(Lean.mkIdent `u) $(Lean.mkIdent `du) $(Lean.mkIdent `hu))
        ($(Lean.mkIdent `native_W12_of_lipschitz) $(Lean.mkIdent `v)
          $(Lean.mkIdent `C) $(Lean.mkIdent `hv)) $(Lean.mkIdent `j)))

private theorem original_weak_jets_on_lipschitz_equal_set
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (v : E2 → E2) (C : ℝ≥0) (hv : LipschitzWith C v) :
    ∀ᵐ x ∂volume.restrict (disc 1), u x = v x →
      ∀ i j, d i x j = (fderiv ℝ v x (coordinateVector 2 j)) i := by
  let Ci (i : Fin 2) : ℝ≥0 := ‖EuclideanSpace.proj (𝕜 := ℝ) i‖₊ * C
  have hvc (i : Fin 2) : LipschitzWith (Ci i) (fun x => v x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp hv
  have he (i j : Fin 2) : ∀ᵐ x ∂volume.restrict (disc 1),
      u x i = v x i → d i x j = lineDeriv ℝ (fun x => v x i) x (coordinateVector 2 j) :=
    native_lipschitz_weak_gradient_locality _ _ _ (hH1 i) (Ci i) (hvc i) j
  have hae : ∀ᵐ x ∂volume.restrict (disc 1), ∀ i j, u x i = v x i →
      d i x j = lineDeriv ℝ (fun x => v x i) x (coordinateVector 2 j) :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => he i j))
  have hd : ∀ᵐ x ∂volume.restrict (disc 1), DifferentiableAt ℝ v x :=
    ae_restrict_of_ae (hv.ae_differentiableAt (μ := volume))
  filter_upwards [hae, hd] with x hx hdx hsame i j
  have hcoord : u x i = v x i := congrArg (fun z : E2 => z i) hsame
  rw [hx i j hcoord]
  have hdi := (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x hdx
  change lineDeriv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i) ∘ v) x
    (coordinateVector 2 j) = _
  rw [hdi.lineDeriv_eq_fderiv]
  have hc := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hdx.hasFDerivAt).fderiv
  change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i) ∘ v) x
    (coordinateVector 2 j) = _
  rw [hc]
  rfl

private theorem original_weak_det_on_lipschitz_equal_set
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (v : E2 → E2) (C : ℝ≥0) (hv : LipschitzWith C v) :
    ∀ᵐ x ∂volume.restrict (disc 1), u x = v x →
      (fderiv ℝ v x).det = Matrix.det (weakJacobian d x) := by
  have hlinear (L : E2 →L[ℝ] E2) : L.det =
      Matrix.det (fun i j : Fin 2 => (L (coordinateVector 2 j)) i) := by
    run_tac do
      let n := (Lean.Name.num `_private.NativeWeakJetLocality 0).str
        "native_linear_det_eq_coordinate_det"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) $(Lean.mkIdent `L)))
  filter_upwards [original_weak_jets_on_lipschitz_equal_set u d hH1 v C hv]
    with x hx he
  rw [hlinear]
  congr 1
  ext i j
  exact (hx he i j).symm

#print axioms native_W12_of_lipschitz
#print axioms original_weak_jets_on_lipschitz_equal_set
#print axioms original_weak_det_on_lipschitz_equal_set
