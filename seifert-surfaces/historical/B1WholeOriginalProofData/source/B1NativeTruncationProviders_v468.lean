import B1HalfDiscBarrierWeak_v468
import NativeH10SupportedBridge
import DifferentialGeometry.External.DeGiorgi.PositivePart
import Lean
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Exact reuse of the existing native compactly supported H1-to-H10 bridge. -/
theorem native_supported_h10_provider_v468
    (U K : Set E2) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H1On U u du)
    (hsu : tsupport u ⊆ K) (hsdu : ∀ i, tsupport (fun x => du x i) ⊆ K) :
    H10On U u du := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let env := (← Lean.getEnv).setExporting false
    let some ci := env.constants.toList.find? (fun (n,_) => n.toString == "_private.NativeH10SupportedBridge.0.native_H1_supported_is_H10") |
      throwError "exact supported H10 provider absent"
    let some raw := ci.2.value? (allowOpaque := true) | throwError "exact supported provider body absent"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let args := ctx.foldl (init := #[]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push (Lean.mkFVar decl.fvarId)
    let value := raw.beta args
    Lean.Meta.checkWithKernel value
    goal.assign value
    Lean.Elab.Tactic.replaceMainGoal []

/-- Exact reuse of the paid smooth positive-part weak derivative. -/
theorem smooth_positivepart_partial_provider_v468
    (U : Set E2) (i : Fin 2) (f : E2 → ℝ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => if 0 < f x then fderiv ℝ f x (EuclideanSpace.single i 1) else 0)
      (fun x => max (f x) 0) U := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let env := (← Lean.getEnv).setExporting false
    let some ci := env.constants.toList.find? (fun (n,_) => n.toString ==
      "_private.DifferentialGeometry.External.DeGiorgi.PositivePart.0.DeGiorgi.weakPartialDeriv_positivePart_of_contDiff") |
      throwError "exact smooth positive-part provider absent"
    let some raw := ci.2.value? (allowOpaque := true) | throwError "exact positive-part body absent"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let args := ctx.foldl (init := #[Lean.mkNatLit 2]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push (Lean.mkFVar decl.fvarId)
    let value := raw.beta args
    Lean.Meta.checkWithKernel value
    goal.assign value
    Lean.Elab.Tactic.replaceMainGoal []

/-- Exact reuse of L2 convergence under the positive-part map. -/
theorem native_positivepart_convergence_provider_v468
    (u : E2 → ℝ) (ψ : ℕ → E2 → ℝ) (μ : Measure E2)
    (hu : AEStronglyMeasurable u μ) (hψ : ∀ n, AEStronglyMeasurable (ψ n) μ)
    (hconv : Tendsto (fun n => eLpNorm (fun x => ψ n x - u x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => max (ψ n x) 0 - max (u x) 0) 2 μ) atTop (𝓝 0) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let env := (← Lean.getEnv).setExporting false
    let some ci := env.constants.toList.find? (fun (n,_) => n.toString ==
      "_private.DifferentialGeometry.External.DeGiorgi.PositivePart.0.DeGiorgi.tendsto_eLpNorm_positivePart_sub") |
      throwError "exact positive-part convergence provider absent"
    let some raw := ci.2.value? (allowOpaque := true) | throwError "exact convergence body absent"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let args := ctx.foldl (init := #[Lean.mkNatLit 2]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push (Lean.mkFVar decl.fvarId)
    let value := raw.beta args
    Lean.Meta.checkWithKernel value
    goal.assign value
    Lean.Elab.Tactic.replaceMainGoal []

/-- Exact reuse of the paid compact smooth cutoff. -/
theorem native_compact_cutoff_provider_v468
    (K U : Set E2) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E2 → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      Set.range χ ⊆ Set.Icc 0 1 ∧ (∀ x ∈ K, χ x = 1) ∧ tsupport χ ⊆ U := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let env := (← Lean.getEnv).setExporting false
    let some ci := env.constants.toList.find? (fun (n,_) => n.toString ==
      "_private.DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation.0.DeGiorgi.exists_smooth_cutoff") |
      throwError "exact compact cutoff provider absent"
    let some raw := ci.2.value? (allowOpaque := true) | throwError "exact cutoff body absent"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.getLCtx
    let args := ctx.foldl (init := #[Lean.mkNatLit 2]) fun acc decl =>
      if decl.isImplementationDetail then acc else acc.push (Lean.mkFVar decl.fvarId)
    let value := raw.beta args
    Lean.Meta.checkWithKernel value
    goal.assign value
    Lean.Elab.Tactic.replaceMainGoal []

end SeifertSurfaces.OriginalEndpoints.B1Tangency
