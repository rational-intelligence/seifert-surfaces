import NativeBoundaryNormalHessianReconstruction

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_fderivWithin_eq_innerSL_planarGradientWithin
    (v : E2 → ℝ) (K : Set E2) (x : E2) :
    fderivWithin ℝ v K x = innerSL ℝ (planarGradientWithin v K x) := by
  ext q
  have hq : q = q 0 • coordinateVector 2 0 + q 1 • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  conv_lhs => rw [hq]
  simp only [map_add, map_smul, innerSL_apply_apply, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, conj_trivial]
  simp [planarGradientWithin, coordinateVector, Fin.sum_univ_two]

/-- The same original function is C2 up to its actual flat boundary. -/
theorem C1QuasilinearDirichletSolution.local_C2_closed_boundary_cap
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      ContDiffOn ℝ 2 u (nativeClosedBoundaryCap c δ) := by
  obtain ⟨s, hs, hsball, hN⟩ := hsolution.local_C1_normal_derivative hρ c hc
  obtain ⟨t, ht, htball, hT⟩ := hsolution.local_C1_tangential_derivative hρ c hc
  let δ := min s t
  have hδ : 0 < δ := lt_min hs ht
  let K := nativeClosedBoundaryCap c δ
  have hKs : K ⊆ nativeClosedBoundaryCap c s := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (min_le_left _ _) hx.1, hx.2⟩
  have hKt : K ⊆ nativeClosedBoundaryCap c t := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (min_le_right _ _) hx.1, hx.2⟩
  have hball : Metric.closedBall c δ ⊆ Metric.ball 0 ρ :=
    (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hsball
  have hKρ : K ⊆ closedHalfDisc ρ := fun x hx =>
    ⟨Metric.ball_subset_closedBall (hball hx.1), hx.2⟩
  have hpartials : ∀ i : Fin 2, ContDiffOn ℝ 1
      (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 i)) K := by
    intro i
    fin_cases i
    · exact hN.mono hKs
    · exact hT.mono hKt
  have hG : ContDiffOn ℝ 1 (planarGradientWithin u (closedHalfDisc ρ)) K :=
    ContDiffOn.sum (fun i _ => (hpartials i).smul contDiffOn_const)
  have hD : ContDiffOn ℝ 1 (fderivWithin ℝ u K) K := by
    have hInner : ContDiffOn ℝ 1 (fun x => innerSL ℝ (planarGradientWithin u (closedHalfDisc ρ) x)) K :=
      (innerSL ℝ).contDiff.comp_contDiffOn hG
    apply hInner.congr
    intro x hx
    rw [fderivWithin_subset hKρ (nativeClosedBoundaryCap_uniqueDiffOn c δ hδ hc.2 x hx)
      (hsolution.c1.differentiableOn (by norm_num) x (hKρ hx))]
    exact native_fderivWithin_eq_innerSL_planarGradientWithin u (closedHalfDisc ρ) x
  refine ⟨δ, hδ, hball, ?_⟩
  rw [show (2 : ℕ∞ω) = 1 + 1 by rfl,
    contDiffOn_succ_iff_fderivWithin (nativeClosedBoundaryCap_uniqueDiffOn c δ hδ hc.2)]
  exact ⟨(hsolution.c1.differentiableOn (by norm_num)).mono hKρ, by simp, hD⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
