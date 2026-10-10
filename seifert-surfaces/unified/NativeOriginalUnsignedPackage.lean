import NativeHigherIntegrability
import NativeActualUnsignedAssembly

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

private theorem native_original_unsigned_package
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ) (beta : ℝ≥0)
    (beta_positive : 0 < beta) (beta_le_one : beta ≤ 1)
    (P : SameHolderRepresentative Ω f d theta sigma beta) :
    LusinOnDisc P.u ∧
    (∀ S : Set E2, MeasurableSet S → S ⊆ disc 1 →
      AEMeasurable (multiplicity P.u S) volume ∧
      (∫⁻ x in S, ENNReal.ofReal |Matrix.det (weakJacobian d x)|) =
        ∫⁻ y, multiplicity P.u S y) ∧
    (∀ S : Set E2, MeasurableSet S → S ⊆ disc 1 →
      AEMeasurable (multiplicity P.u S) volume ∧
      (∫⁻ x in S, ENNReal.ofReal (metricWeight M (P.u x) *
        |Matrix.det (weakJacobian d x)|)) =
        ∫⁻ y, ENNReal.ofReal (metricWeight M y) * multiplicity P.u S y) := by
  have hderived : ∃ p : ℝ, 2 < p ∧ ∀ t : ℝ, 0 < t → t < 1 → ∀ i,
      MemLp (d i) (ENNReal.ofReal p) (volume.restrict (disc t)) := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeHigherIntegrability 0).str
        "native_original_higher_integrability"
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact $(Lean.mkIdent pn) $(Lean.mkIdent `R) $(Lean.mkIdent `A)
          $(Lean.mkIdent `G) $(Lean.mkIdent `Ω) $(Lean.mkIdent `M)
          $(Lean.mkIdent `agreement) $(Lean.mkIdent `symmetric) $(Lean.mkIdent `elliptic)
          $(Lean.mkIdent `holder) $(Lean.mkIdent `identity_at_infinity)
          $(Lean.mkIdent `f) $(Lean.mkIdent `d) $(Lean.mkIdent `minimum)
          $(Lean.mkIdent `theta) $(Lean.mkIdent `sigma) $(Lean.mkIdent `beta)
          $(Lean.mkIdent `P)))
  run_tac do
    let pn := (Lean.Name.num `_private.NativeActualUnsignedAssembly 0).str
      "same_holder_unsigned_after_derived_full"
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact $(Lean.mkIdent pn) $(Lean.mkIdent `R) $(Lean.mkIdent `A)
        $(Lean.mkIdent `G) $(Lean.mkIdent `Ω) $(Lean.mkIdent `M)
        $(Lean.mkIdent `agreement) $(Lean.mkIdent `symmetric) $(Lean.mkIdent `elliptic)
        $(Lean.mkIdent `holder) $(Lean.mkIdent `identity_at_infinity)
        $(Lean.mkIdent `f) $(Lean.mkIdent `d) $(Lean.mkIdent `minimum)
        $(Lean.mkIdent `theta) $(Lean.mkIdent `sigma) $(Lean.mkIdent `beta)
        $(Lean.mkIdent `P) $(Lean.mkIdent `hderived)))

#print axioms native_original_unsigned_package
