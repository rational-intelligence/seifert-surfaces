import B1L1DirectWeakLower
import NewtonianKernelLower
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.AppendixACoordinates
theorem morrey_potential_debt (r : ℝ) (radius_positive : 0 < r)
    (gamma : ℝ≥0) (gamma_positive : 0 < gamma) (gamma_lt_one : gamma < 1)
    (a : E2 → Mat2) (ell Lambda : ℝ) (ell_positive : 0 < ell) (Lambda_positive : 0 < Lambda)
    (bounds : ∀ y : E2, ∀ p : E2,
      ell * ‖p‖ ^ 2 ≤ inner ℝ p (matrixAction (a y) p) ∧ (∀ i j, |a y i j| ≤ Lambda))
    (Ca : ℝ≥0) (coefficient_holder : ∀ i j, HolderWith Ca gamma (fun y => a y i j)) :
    ∃ P : ℝ, 0 < P ∧
      ∀ (F : E2 → ℝ) (L : ℝ), ScalarGrowth univ ((halfDisc r).indicator F) gamma L →
      ∃ (q : E2 → E2) (Bq : ℝ) (Cq : ℝ≥0),
        0 ≤ Bq ∧ Bq + (Cq : ℝ) ≤ P * L ∧
        (∀ y ∈ closedHalfDisc r, ‖q y‖ ≤ Bq) ∧
        HolderOnWith Cq gamma q (closedHalfDisc r) ∧
        (∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ halfDisc r →
          IntegrableOn (fun y => inner ℝ (q y) (planarGradient psi y)) (halfDisc r) ∧
          (∫ y in halfDisc r, F y * psi y) =
            ∫ y in halfDisc r, inner ℝ (q y) (planarGradient psi y)) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "exact (by\n  have kernel_estimate := newtonian_kernel_morrey_estimate r radius_positive gamma gamma_positive gamma_lt_one\n  have kernel_identity := newtonian_kernel_compact_test_identity r radius_positive gamma gamma_positive gamma_lt_one\n  let T := fun (F : E2 → ℝ) (x : E2) =>\n    ∫ y, ((halfDisc r).indicator F y) • ((‖x - y‖ ^ 2)⁻¹ • (x - y))\n  obtain ⟨B, H, hB, hH, estimates⟩ := kernel_estimate\n  let k : ℝ := -(2 * Real.pi)⁻¹\n  let t : ℝ := |k|\n  refine ⟨t * (B + H) + 1, by dsimp [t]; positivity, ?_⟩\n  intro F L growth\n  have hL : 0 ≤ L := growth.2.1\n  let q : E2 → E2 := fun x => k • T F x\n  let Bq : ℝ := t * B * L\n  let Cq : ℝ≥0 := ⟨t * H * L, by dsimp [t]; positivity⟩\n  obtain ⟨pointwise, difference⟩ := estimates F L growth\n  have hqb : ∀ y ∈ closedHalfDisc r, ‖q y‖ ≤ Bq := by\n    intro y hy\n    dsimp only [q, Bq]\n    rw [norm_smul, Real.norm_eq_abs]\n    exact (mul_le_mul_of_nonneg_left (pointwise y hy).2 (abs_nonneg k)).trans_eq (by ring)\n  have hqh : HolderOnWith Cq gamma q (closedHalfDisc r) := by\n    intro x hx z hz\n    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) gamma.coe_nonneg,\n      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul Cq.coe_nonneg]\n    apply ENNReal.ofReal_le_ofReal\n    change dist (q x) (q z) ≤ (t * H * L) * (dist x z) ^ (gamma : ℝ)\n    rw [dist_eq_norm, show q x - q z = k • (T F x - T F z) by simp only [q, smul_sub],\n      norm_smul, Real.norm_eq_abs]\n    exact (mul_le_mul_of_nonneg_left (difference x hx z hz) (abs_nonneg k)).trans_eq (by dsimp [t]; ring)\n  have hcompact : IsCompact (closedHalfDisc r) := by\n    apply (isCompact_closedBall (0 : E2) r).inter_right\n    exact isClosed_le (continuous_const : Continuous (fun _ : E2 => (0 : ℝ)))\n      (EuclideanSpace.proj (1 : Fin 2)).continuous\n  have hsubset : halfDisc r ⊆ closedHalfDisc r := by\n    intro y hy\n    exact ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy.1).le, hy.2.le⟩\n  have hgrad (psi : E2 → ℝ) (hpsi : ContDiff ℝ ∞ psi) : Continuous (planarGradient psi) :=\n    continuous_planarGradient hpsi\n  refine ⟨q, Bq, Cq, by dsimp [Bq, t]; positivity, ?_, hqb, hqh, ?_⟩\n  · change t * B * L + t * H * L ≤ (t * (B + H) + 1) * L\n    nlinarith\n  · intro psi hpsi hsupp hsub\n    refine ⟨((hqh.continuousOn gamma_positive).inner (hgrad psi hpsi).continuousOn).integrableOn_compact hcompact |>.mono_set hsubset, ?_⟩\n    calc\n      _ = k * ∫ x in halfDisc r, inner ℝ (T F x) (planarGradient psi x) :=\n        kernel_identity F L growth psi hpsi hsupp hsub\n      _ = _ := by\n        rw [← integral_const_mul]\n        apply integral_congr_ae\n        filter_upwards with x\n        exact (real_inner_smul_left (T F x) (planarGradient psi x) k).symm\n)"))

theorem zero_scalar_boundary_debt (r : ℝ) (radius_positive : 0 < r)
    (gamma : ℝ≥0) (gamma_positive : 0 < gamma) (gamma_lt_one : gamma < 1)
    (a : E2 → Mat2) (ell Lambda : ℝ) (ell_positive : 0 < ell) (Lambda_positive : 0 < Lambda)
    (bounds : ∀ y : E2, ∀ p : E2,
      ell * ‖p‖ ^ 2 ≤ inner ℝ p (matrixAction (a y) p) ∧ (∀ i j, |a y i j| ≤ Lambda))
    (Ca : ℝ≥0) (coefficient_holder : ∀ i j, HolderWith Ca gamma (fun y => a y i j)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (e : E2 → E2) (v : E2 → ℝ) (dv : E2 → E2)
        (Be : ℝ), 0 ≤ Be → ∀ Ce : ℝ≥0,
      (∀ y ∈ closedHalfDisc r, ‖e y‖ ≤ Be) →
      HolderOnWith Ce gamma e (closedHalfDisc r) →
      WeakDivergenceWithData (halfDisc r) a e (fun _ => 0) v dv →
      FlatZeroTrace r v dv →
      let size := Be + (Ce : ℝ) + ∫ y in halfDisc r, |v y|
      ∃ w : E2 → ℝ, w =ᵐ[volume.restrict (halfDisc (r / 2))] v ∧
        H1On (halfDisc (r / 2)) w dv ∧
        ContDiffOn ℝ 1 w (closedHalfDisc (r / 2)) ∧
        (∀ y ∈ flatArc (r / 2), w y = 0) ∧
        (∀ y ∈ closedHalfDisc (r / 2), |w y| ≤ A * size) ∧
        (∀ j, ∀ y ∈ closedHalfDisc (r / 2),
          |fderivWithin ℝ w (closedHalfDisc (r / 2)) y (coordinateVector 2 j)| ≤ A * size) ∧
        (∀ j, ∃ C : ℝ≥0, (C : ℝ) ≤ A * size ∧
          HolderOnWith C gamma
            (fun y => fderivWithin ℝ w (closedHalfDisc (r / 2)) y (coordinateVector 2 j))
            (closedHalfDisc (r / 2))) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac\n  let sp ← Lean.Core.liftIOCore Lean.searchPathRef.get\n  Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk \"/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_original_scalar_roots_v448/capsules/closed\" :: sp)\n  let imported ← Lean.Core.liftIOCore <| Lean.importModules #[{module := `WeakScalarBoundaryLower}] {} (trustLevel := 0) (loadExts := false)\n  Lean.Core.liftIOCore <| Lean.searchPathRef.set sp\n  let some ci := imported.find? `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.zero_scalar_boundary_debt | Lean.throwError \"closed scalar root missing\"\n  let some raw := ci.value? (allowOpaque := true) | Lean.throwError \"closed scalar actual value missing\"\n  let mut value := raw\n  let mut args : Array Lean.Expr := #[]\n  while true do\n    match value with\n    | .lam binder _ body _ =>\n      let some decl := (← Lean.getLCtx).findFromUserName? binder | Lean.throwError \"literal binder missing {binder}\"\n      let arg := Lean.mkFVar decl.fvarId\n      args := args.push arg\n      value := body.instantiate1 arg\n    | _ => break\n  let reconstructed ← Lean.Meta.mkLambdaFVars args value\n  unless Lean.Expr.equal reconstructed raw && Lean.ExprStructEq.mk reconstructed == Lean.ExprStructEq.mk raw do Lean.throwError \"closed stored scalar value reconstruction drift\"\n  Lean.Meta.checkWithKernel value\n  (← Lean.Elab.Tactic.getMainGoal).assign value\n  Lean.Elab.Tactic.replaceMainGoal []\n"))

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
