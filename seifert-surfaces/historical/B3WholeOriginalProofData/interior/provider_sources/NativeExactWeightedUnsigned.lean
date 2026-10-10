import NativeSobolevUnsignedFormula

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

private theorem native_H1_exact_original_weighted_formula
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (huc : ContinuousOn u (closedDisc 1)) (hL : LusinOnDisc u)
    (M : E2 → Mat2) (hM : Continuous M) :
    ∀ S : Set E2, MeasurableSet S → S ⊆ disc 1 →
      AEMeasurable (multiplicity u S) volume ∧
      (∫⁻ x in S, ENNReal.ofReal (metricWeight M (u x) * |Matrix.det (weakJacobian d x)|)) =
        ∫⁻ y, ENNReal.ofReal (metricWeight M y) * multiplicity u S y := by
  have hweight : Measurable (fun y => ENNReal.ofReal (metricWeight M y)) :=
    hM.matrix_det.sqrt.measurable.ennreal_ofReal
  have hall : LusinOnDisc u ∧
      ∀ (w : E2 → ℝ≥0∞), Measurable w →
        ∀ S : Set E2, MeasurableSet S → S ⊆ disc 1 →
          AEMeasurable (multiplicity u S) volume ∧
          (∫⁻ x in S, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
            ∫⁻ y, w y * multiplicity u S y := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeSobolevUnsignedFormula 0).str
        "native_H1_unsigned_formula_from_actual_lusin"
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact $(Lean.mkIdent pn) $(Lean.mkIdent `u) $(Lean.mkIdent `d)
          $(Lean.mkIdent `hH1) $(Lean.mkIdent `huc) $(Lean.mkIdent `hL)))
  intro S hS hSU
  obtain ⟨hmeas, heq⟩ := hall.2 (fun y => ENNReal.ofReal (metricWeight M y)) hweight S hS hSU
  refine ⟨hmeas, ?_⟩
  calc
    _ = ∫⁻ x in S, ENNReal.ofReal (metricWeight M (u x)) *
        ENNReal.ofReal |Matrix.det (weakJacobian d x)| := by
      apply lintegral_congr
      intro x
      exact ENNReal.ofReal_mul (Real.sqrt_nonneg _)
    _ = _ := heq

#print axioms native_H1_exact_original_weighted_formula
