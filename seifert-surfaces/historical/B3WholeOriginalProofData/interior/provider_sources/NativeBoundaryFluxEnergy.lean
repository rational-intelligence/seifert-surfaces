import NativeBoundaryFluxDerivatives

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

theorem C1QuasilinearDirichletSolution.native_flux_gradient_bound
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x : E2) (hx : x ∈ openHalfDisc ρ) (i : Fin 2)
    (M : ℝ) (hM : 0 ≤ M)
    (hDx : ‖fluxDx Q (firstJetWithin ρ u x)‖ ≤ M)
    (hDz : ‖fluxDz Q (firstJetWithin ρ u x)‖ ≤ M)
    (ha : ∀ k j, |rawPrincipalMatrix Q u x k j| ≤ M)
    (hg : ‖planarGradientWithin u (closedHalfDisc ρ) x‖ ≤ M) :
    ‖planarGradient (fun y => Q.flux (firstJetWithin ρ u y) i) x‖ ≤
      2 * (M + M ^ 2) + 2 * M *
        (‖planarGradient (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 0)) x‖ +
         ‖planarGradient (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1)) x‖) := by
  let G (j : Fin 2) := planarGradient (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 j)) x
  rw [firstJetWithin_eq_firstJet u hx] at hDx hDz
  rw [planarGradientWithin_closedHalfDisc_eq u hx] at hg
  have hH (k j : Fin 2) : |planarHessian u x k j| ≤ ‖G j‖ := by
    rw [← hsolution.native_partial_gradient_hessian x hx k j]
    exact PiLp.norm_apply_le (G j) k (p := 2)
  have hb (k : Fin 2) :
      |fluxDx Q (firstJet u x) (coordinateVector 2 k) i +
        fluxDz Q (firstJet u x) i * planarGradient u x k| ≤ M + M ^ 2 := by
    apply (abs_add_le _ _).trans
    have hxD : |fluxDx Q (firstJet u x) (coordinateVector 2 k) i| ≤ M := by
      calc
        _ ≤ ‖fluxDx Q (firstJet u x) (coordinateVector 2 k)‖ :=
          PiLp.norm_apply_le _ i (p := 2)
        _ ≤ ‖fluxDx Q (firstJet u x)‖ * ‖coordinateVector 2 k‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M := by simpa [coordinateVector, PiLp.norm_single] using hDx
    have hzD : |fluxDz Q (firstJet u x) i| ≤ M :=
      (PiLp.norm_apply_le _ i (p := 2)).trans hDz
    have hgD : |planarGradient u x k| ≤ M := (PiLp.norm_apply_le _ k (p := 2)).trans hg
    rw [abs_mul, pow_two]
    exact add_le_add hxD (mul_le_mul hzD hgD (abs_nonneg _) hM)
  have hcomponent (k : Fin 2) :
      |planarGradient (fun y => Q.flux (firstJetWithin ρ u y) i) x k| ≤
        M + M ^ 2 + M * (‖G 0‖ + ‖G 1‖) := by
    rw [hsolution.native_flux_partial_derivative x hx i k]
    simp only [Fin.sum_univ_two]
    calc
      _ ≤ |fluxDx Q (firstJet u x) (coordinateVector 2 k) i +
          fluxDz Q (firstJet u x) i * planarGradient u x k| +
          |rawPrincipalMatrix Q u x i 0 * planarHessian u x k 0 +
           rawPrincipalMatrix Q u x i 1 * planarHessian u x k 1| := abs_add_le _ _
      _ ≤ (M + M ^ 2) +
          (|rawPrincipalMatrix Q u x i 0 * planarHessian u x k 0| +
           |rawPrincipalMatrix Q u x i 1 * planarHessian u x k 1|) :=
        add_le_add (hb k) (abs_add_le _ _)
      _ ≤ (M + M ^ 2) + (M * ‖G 0‖ + M * ‖G 1‖) := by
        simp only [abs_mul]
        exact add_le_add le_rfl (add_le_add
          (mul_le_mul (ha i 0) (hH k 0) (abs_nonneg _) hM)
          (mul_le_mul (ha i 1) (hH k 1) (abs_nonneg _) hM))
      _ = _ := by ring
  calc
    _ ≤ |planarGradient (fun y => Q.flux (firstJetWithin ρ u y) i) x 0| +
        |planarGradient (fun y => Q.flux (firstJetWithin ρ u y) i) x 1| := native_planar_norm_le_coordinate_sum _
    _ ≤ (M + M ^ 2 + M * (‖G 0‖ + ‖G 1‖)) +
        (M + M ^ 2 + M * (‖G 0‖ + ‖G 1‖)) := add_le_add (hcomponent 0) (hcomponent 1)
    _ = _ := by dsimp [G]; ring

theorem C1QuasilinearDirichletSolution.smooth_flux_component_on_openHalfDisc
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => Q.flux (firstJetWithin ρ u x) i) (openHalfDisc ρ) := by
  have hj : ContDiffOn ℝ ∞ (firstJet u) (openHalfDisc ρ) :=
    contDiffOn_id.prodMk (hsolution.smooth_on_openHalfDisc.prodMk
      (native_smooth_gradient_on_open _ (openHalfDisc_isOpen ρ) u hsolution.smooth_on_openHalfDisc))
  have hflux := Q.flux_smooth.comp hj (fun x hx => by
    simpa only [← firstJetWithin_eq_firstJet u hx] using
      hsolution.attained_jets x (openHalfDisc_subset_closedHalfDisc ρ hx))
  have hi := (EuclideanSpace.proj i).contDiff.contDiffOn.comp hflux (mapsTo_univ _ _)
  apply hi.congr
  intro x hx
  simp only [Function.comp_def, PiLp.proj_apply, ← firstJetWithin_eq_firstJet u hx]

theorem C1QuasilinearDirichletSolution.local_native_flux_memW1p
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      ∀ i : Fin 2,
        MemLp (planarGradient (fun x => Q.flux (firstJetWithin ρ u x) i)) 2
          (volume.restrict (Metric.ball c r ∩ {x : E2 | 0 < x 0})) ∧
        DeGiorgi.MemW1p 2 (fun x => Q.flux (firstJetWithin ρ u x) i)
          (Metric.ball c r ∩ {x : E2 | 0 < x 0}) := by
  obtain ⟨s, hs, hball, hG⟩ := hsolution.local_full_second_gradient_memLp hρ c hc
  have hcf : c 0 = 0 := hc.2
  obtain ⟨t, κ, M, T, ht, hTop, hconv, hcompact, hTJ, hjets, hκ, hM, hvalues,
    hbounds, hiterated, hcoercive⟩ :=
      hsolution.local_boundary_jet_tube hρ c ⟨Metric.ball_subset_closedBall hc.1, by change 0 ≤ c 0; simp [hcf]⟩
  let r := min s t
  have hr : 0 < r := lt_min hs ht
  let U := Metric.ball c r ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hsmall : U ⊆ Metric.ball c s ∩ {x : E2 | 0 < x 0} :=
    fun x hx => ⟨Metric.ball_subset_ball (min_le_left _ _) hx.1, hx.2⟩
  have hsub : U ⊆ openHalfDisc ρ := fun x hx =>
    ⟨hball (Metric.ball_subset_closedBall (hsmall hx).1), hx.2⟩
  have hclosed : Metric.closedBall c r ⊆ Metric.ball (0 : E2) ρ :=
    (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hball
  let G (i : Fin 2) := planarGradient (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 i))
  have hGLp (i : Fin 2) : MemLp (G i) 2 (volume.restrict U) :=
    (hG i).mono_measure (Measure.restrict_mono_set _ hsmall)
  haveI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr
      (lt_of_le_of_lt (measure_mono (show U ⊆ Metric.ball c r from fun x hx => hx.1))
        Metric.isBounded_ball.measure_lt_top).ne
  have hmajor : MemLp (fun x => 2 * (M + M ^ 2) + 2 * M * (‖G 0 x‖ + ‖G 1 x‖)) 2
      (volume.restrict U) := by
    have hconstant : MemLp (fun _ : E2 => 2 * (M + M ^ 2)) 2 (volume.restrict U) := memLp_const _
    have hsum : MemLp (fun x => ‖G 0 x‖ + ‖G 1 x‖) 2 (volume.restrict U) :=
      (hGLp 0).norm.add (hGLp 1).norm
    exact hconstant.add (hsum.const_mul (2 * M))
  refine ⟨r, hr, hclosed, ?_⟩
  intro i
  let f : E2 → ℝ := fun x => Q.flux (firstJetWithin ρ u x) i
  have hfc : ContDiffOn ℝ 1 f U :=
    (hsolution.smooth_flux_component_on_openHalfDisc i).mono hsub |>.of_le (by simp)
  have hfm : AEStronglyMeasurable (planarGradient f) (volume.restrict U) :=
    (QuasilinearLocalization.Helpers.gradient_continuousOn U hU f hfc).aestronglyMeasurable hU.measurableSet
  have hgrad : MemLp (planarGradient f) 2 (volume.restrict U) := by
    apply hmajor.mono' hfm
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    have hxΩ := hsub hx
    have hxclosed := openHalfDisc_subset_closedHalfDisc ρ hxΩ
    have hxT : firstJetWithin ρ u x ∈ closure T := by
      apply subset_closure
      apply hjets x
      refine ⟨Metric.mem_closedBall.mpr ?_, hxclosed⟩
      have hd := Metric.mem_ball.mp hx.1
      have hrt : r ≤ t := min_le_right _ _
      linarith
    have hb := hbounds _ hxT
    have hB := native_classical_coefficient_bounds hxΩ κ M (by linarith)
      (hvalues x hxclosed).2 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1
      (hcoercive _ hxT)
    exact hsolution.native_flux_gradient_bound x hxΩ i M (by linarith) hb.2.2.1 hb.2.2.2.1
      hB.2.1 (hvalues x hxclosed).2
  obtain ⟨L, hL⟩ := (closedHalfDisc_isCompact ρ).exists_bound_of_continuousOn
    ((EuclideanSpace.proj i).continuous.continuousOn.comp
      (hsolution.continuous_boundary_coefficients hρ).1 (mapsTo_univ _ _))
  have hf : MemLp f 2 (volume.restrict U) := by
    apply MemLp.of_bound (hfc.continuousOn.aestronglyMeasurable hU.measurableSet) L
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hL x (openHalfDisc_subset_closedHalfDisc ρ (hsub hx))
  exact ⟨hgrad, native_memW1p_of_C1_and_actual_gradient_memLp U hU f hfc hf hgrad⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
