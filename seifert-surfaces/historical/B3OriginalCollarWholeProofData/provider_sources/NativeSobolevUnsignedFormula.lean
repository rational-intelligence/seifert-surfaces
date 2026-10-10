import NativeSobolevLipschitzPieces

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

private theorem native_H1_unsigned_formula_from_actual_lusin
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (huc : ContinuousOn u (closedDisc 1)) (hL : LusinOnDisc u) :
    LusinOnDisc u ∧
    ∀ (w : E2 → ℝ≥0∞), Measurable w →
      ∀ S : Set E2, MeasurableSet S → S ⊆ disc 1 →
        AEMeasurable (multiplicity u S) volume ∧
        (∫⁻ x in S, w (u x) * ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
          ∫⁻ y, w y * multiplicity u S y := by
  have hpieces : ∃ (v : ℕ → E2 → E2) (C : ℕ → ℝ≥0),
      (∀ n, LipschitzWith (C n) (v n)) ∧
      volume (disc 1 \ ⋃ n, {x | u x = v n x}) = 0 := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeSobolevLipschitzPieces 0).str
        "native_H1_countable_lipschitz_coincidences"
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact $(Lean.mkIdent pn) $(Lean.mkIdent `u) $(Lean.mkIdent `d)
          $(Lean.mkIdent `hH1) $(Lean.mkIdent `huc)))
  obtain ⟨v, C, hv, hcover⟩ := hpieces
  have himage : volume (u '' (disc 1 \ ⋃ n, {x | u x = v n x})) = 0 :=
    hL _ sdiff_subset hcover
  run_tac do
    let pn := (Lean.Name.num `_private.NativeLipschitzAreaReduction 0).str
      "area_and_lusin_of_countable_lipschitz_coincidences"
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact $(Lean.mkIdent pn) $(Lean.mkIdent `u) $(Lean.mkIdent `d)
        $(Lean.mkIdent `hH1) $(Lean.mkIdent `huc)
        $(Lean.mkIdent `v) $(Lean.mkIdent `C) $(Lean.mkIdent `hv)
        $(Lean.mkIdent `hcover) $(Lean.mkIdent `himage)))

private theorem native_H1_original_unweighted_from_actual_lusin
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (huc : ContinuousOn u (closedDisc 1)) (hL : LusinOnDisc u) :
    ∀ S : Set E2, MeasurableSet S → S ⊆ disc 1 →
      AEMeasurable (multiplicity u S) volume ∧
      (∫⁻ x in S, ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
        ∫⁻ y, multiplicity u S y := by
  intro S hS hSU
  simpa only [one_mul] using
    (native_H1_unsigned_formula_from_actual_lusin u d hH1 huc hL).2
      (fun _ => 1) measurable_const S hS hSU

#print axioms native_H1_unsigned_formula_from_actual_lusin
#print axioms native_H1_original_unweighted_from_actual_lusin
