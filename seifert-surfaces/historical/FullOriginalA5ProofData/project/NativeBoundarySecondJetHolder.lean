import NativeBoundaryHolderProduct

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem C1QuasilinearDirichletSolution.local_C1_holder_firstJetWithin
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, ∃ α : ℝ≥0, 0 < r ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      ContDiffOn ℝ 2 u (nativeClosedBoundaryCap c r) ∧
      ContDiffOn ℝ 1 (firstJetWithin ρ u) (nativeClosedBoundaryCap c r) ∧
      ∃ C : ℝ≥0, HolderOnWith C α
        (fderivWithin ℝ (firstJetWithin ρ u) (nativeClosedBoundaryCap c r))
        (nativeClosedBoundaryCap c r) := by
  obtain ⟨r, α, hr, hα, hα1, hball, hu, hH⟩ :=
    hsolution.local_C2_holder_closed_boundary_cap hρ c hc
  let K := nativeClosedBoundaryCap c r
  let D (i : Fin 2) := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 i)
  let G := planarGradientWithin u (closedHalfDisc ρ)
  have hKρ : K ⊆ closedHalfDisc ρ := fun x hx =>
    ⟨Metric.ball_subset_closedBall (hball hx.1), hx.2⟩
  have hKD : UniqueDiffOn ℝ K := nativeClosedBoundaryCap_uniqueDiffOn c r hr hc.2
  have hDu : EqOn (fderivWithin ℝ u K) (fderivWithin ℝ u (closedHalfDisc ρ)) K :=
    fun x hx => fderivWithin_subset hKρ (hKD x hx)
      (hsolution.c1.differentiableOn (by norm_num) x (hKρ hx))
  have hDi : ∀ i, ContDiffOn ℝ 1 (D i) K := by
    intro i
    have hd := (hu.fderivWithin (m := 1) hKD (by norm_num)).clm_apply
      (contDiffOn_const (c := coordinateVector 2 i))
    exact hd.congr (fun x hx => congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) (hDu hx).symm)
  have hG : ContDiffOn ℝ 1 G K :=
    ContDiffOn.sum (fun i _ => (hDi i).smul contDiffOn_const)
  have hJet := hsolution.firstJetWithin_contDiffOn_cap c hc.2 r hr hball 1 hu
  refine ⟨r, α, hr, hα, hα1, hball, hu, hJet, ?_⟩
  apply native_clm_holder_of_coordinate_evaluations
  intro i
  obtain ⟨A, hA⟩ := native_contDiffOn_cap_holder c r hr (D i) α hα1.le (hDi i)
  obtain ⟨B0, hB0⟩ := hH i 0
  obtain ⟨B1, hB1⟩ := hH i 1
  let H (j : Fin 2) := fun x => fderivWithin ℝ (D j) K x (coordinateVector 2 i)
  obtain ⟨C0, hC0⟩ := native_holder_smul_const K (H 0) B0 α hB0 (coordinateVector 2 0)
  obtain ⟨C1, hC1⟩ := native_holder_smul_const K (H 1) B1 α hB1 (coordinateVector 2 1)
  have hGH := native_holder_add K _ _ C0 C1 α hC0 hC1
  have hpH := native_holder_prodMk K (D i)
    (fun x => H 0 x • coordinateVector 2 0 + H 1 x • coordinateVector 2 1)
    A (C0 + C1) α hA hGH
  have hfullH := native_holder_prodMk K (fun _ => coordinateVector 2 i)
    (fun x => (D i x, H 0 x • coordinateVector 2 0 + H 1 x • coordinateVector 2 1))
    0 (A + (C0 + C1)) α (native_holder_const K _ α) hpH
  have hformula (x : E2) (hx : x ∈ K) :
      fderivWithin ℝ (firstJetWithin ρ u) K x (coordinateVector 2 i) =
        (coordinateVector 2 i, D i x, H 0 x • coordinateVector 2 0 + H 1 x • coordinateVector 2 1) := by
    have hGder : fderivWithin ℝ G K x = ∑ j : Fin 2, (fderivWithin ℝ (D j) K x).smulRight (coordinateVector 2 j) := by
      change fderivWithin ℝ (fun y => ∑ j : Fin 2, D j y • coordinateVector 2 j) K x = _
      rw [fderivWithin_fun_sum (hKD x hx) (fun j _ =>
        ((hDi j).differentiableOn (by norm_num) x hx).smul_const _)]
      apply Finset.sum_congr rfl
      intro j _
      exact fderivWithin_smul_const (hKD x hx) ((hDi j).differentiableOn (by norm_num) x hx) _
    have hud : DifferentiableWithinAt ℝ u K x := hu.differentiableOn (by norm_num) x hx
    have hgd : DifferentiableWithinAt ℝ G K x := hG.differentiableOn (by norm_num) x hx
    change fderivWithin ℝ (fun y => (y, u y, G y)) K x _ = _
    have hp0 := (differentiableWithinAt_id.fderivWithin_prodMk (hud.prodMk hgd) (hKD x hx))
    have hp1 := hud.fderivWithin_prodMk hgd (hKD x hx)
    simp only [id_eq] at hp0
    rw [hp0, hp1, fderivWithin_id (hKD x hx), hDu hx, hGder]
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, Fin.sum_univ_two,
      add_apply, ContinuousLinearMap.smulRight_apply, D, H]
  refine ⟨0 + (A + (C0 + C1)), ?_⟩
  intro x hx y hy
  change edist ((fderivWithin ℝ (firstJetWithin ρ u) K x) (coordinateVector 2 i))
      ((fderivWithin ℝ (firstJetWithin ρ u) K y) (coordinateVector 2 i)) ≤ _
  rw [hformula x hx, hformula y hy]
  exact hfullH x hx y hy

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
