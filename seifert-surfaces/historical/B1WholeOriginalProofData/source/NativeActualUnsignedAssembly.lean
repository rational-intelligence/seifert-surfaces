import NativeSupercriticalLusin
import NativeExactWeightedUnsigned

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

private theorem same_holder_unsigned_after_derived_local_p
    {R : ℝ} {Ω : SmoothFlatJordanDomain R}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    {theta : ℝ → ℝ} {sigma : ℝ} {beta : ℝ≥0}
    (P : SameHolderRepresentative Ω f d theta sigma beta)
    (hderived : ∃ p : ℝ, 2 < p ∧ ∀ t : ℝ, 0 < t → t < 1 → ∀ i,
      MemLp (d i) (ENNReal.ofReal p) (volume.restrict (disc t)))
    (M : E2 → Mat2) (hM : Continuous M) :
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
  have hL : LusinOnDisc P.u := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeSupercriticalLusin 0).str
        "same_holder_supercritical_lusin"
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact $(Lean.mkIdent pn) $(Lean.mkIdent `P) $(Lean.mkIdent `hderived)))
  refine ⟨hL, ?_, ?_⟩
  · run_tac do
      let pn := (Lean.Name.num `_private.NativeSobolevUnsignedFormula 0).str
        "native_H1_original_unweighted_from_actual_lusin"
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact $(Lean.mkIdent pn) $(Lean.mkIdent `P).u $(Lean.mkIdent `d)
          $(Lean.mkIdent `P).same_H1 $(Lean.mkIdent `P).continuous $(Lean.mkIdent `hL)))
  · run_tac do
      let pn := (Lean.Name.num `_private.NativeExactWeightedUnsigned 0).str
        "native_H1_exact_original_weighted_formula"
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact $(Lean.mkIdent pn) $(Lean.mkIdent `P).u $(Lean.mkIdent `d)
          $(Lean.mkIdent `P).same_H1 $(Lean.mkIdent `P).continuous $(Lean.mkIdent `hL)
          $(Lean.mkIdent `M) $(Lean.mkIdent `hM)))

#print axioms same_holder_unsigned_after_derived_local_p

private theorem same_holder_unsigned_after_derived_full
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ) (beta : ℝ≥0)
    (P : SameHolderRepresentative Ω f d theta sigma beta)
    (hderived : ∃ p : ℝ, 2 < p ∧ ∀ t : ℝ, 0 < t → t < 1 → ∀ i,
      MemLp (d i) (ENNReal.ofReal p) (volume.restrict (disc t))) :
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
  have hM : Continuous M := continuous_pi_iff.mpr fun i =>
    continuous_pi_iff.mpr fun j => by
      obtain ⟨C, hC⟩ := holder i j
      exact hC.continuous G.alpha_pos
  exact same_holder_unsigned_after_derived_local_p P hderived M hM

#print axioms same_holder_unsigned_after_derived_full
