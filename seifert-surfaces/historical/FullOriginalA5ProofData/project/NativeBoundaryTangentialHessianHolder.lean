import NativeBoundaryHigherJetComposition

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem C1QuasilinearDirichletSolution.local_C1_holder_tangential_derivative
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, ∃ α : ℝ≥0, 0 < r ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      ContDiffOn ℝ 1 (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1))
        (nativeClosedBoundaryCap c r) ∧
      ∀ i, ∃ C : ℝ≥0, HolderOnWith C α
        (fun x => fderivWithin ℝ
          (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1))
          (nativeClosedBoundaryCap c r) x (coordinateVector 2 i))
        (nativeClosedBoundaryCap c r) := by
  obtain ⟨r, α, hr, hα, hα1, hball, hv, hH⟩ :=
    hsolution.local_C1_holder_zero_trace_tangential_derivative hρ c hc
  let K := nativeClosedBoundaryCap c r
  let t := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1)
  let G := fun x : E2 => deriv g.value (x 1)
  let v := fun x => t x - G x
  have hG2 : ContDiffOn ℝ 2 G K :=
    (g.smooth_deriv_extension_on_ball.mono (fun x hx => hball hx.1)).of_le (by simp)
  have hG1 : ContDiffOn ℝ 1 G K := hG2.of_le (by norm_num)
  have ht : ContDiffOn ℝ 1 t K := by
    simpa only [v, t, G, sub_add_cancel] using hv.add hG1
  refine ⟨r, α, hr, hα, hα1, hball, ht, ?_⟩
  intro i
  obtain ⟨C, hC⟩ := hH i
  have hGi : ContDiffOn ℝ 1
      (fun x => fderivWithin ℝ G K x (coordinateVector 2 i)) K :=
    (hG2.fderivWithin (nativeClosedBoundaryCap_uniqueDiffOn c r hr hc.2) (by norm_num)).clm_apply
      contDiffOn_const
  obtain ⟨D, hD⟩ := native_contDiffOn_cap_holder c r hr _ α hα1.le hGi
  have hSum := native_holder_add K
    (fun x => fderivWithin ℝ v K x (coordinateVector 2 i))
    (fun x => fderivWithin ℝ G K x (coordinateVector 2 i)) C D α hC hD
  refine ⟨C + D, ?_⟩
  have hformula (x : E2) (hx : x ∈ K) :
      fderivWithin ℝ t K x (coordinateVector 2 i) =
      fderivWithin ℝ v K x (coordinateVector 2 i) +
      fderivWithin ℝ G K x (coordinateVector 2 i) := by
    have hs := fderivWithin_fun_sub (nativeClosedBoundaryCap_uniqueDiffOn c r hr hc.2 x hx)
      (ht.differentiableOn (by norm_num) x hx) (hG1.differentiableOn (by norm_num) x hx)
    change fderivWithin ℝ v K x = _ at hs
    rw [hs, ContinuousLinearMap.sub_apply]
    ring
  intro x hx y hy
  change edist ((fderivWithin ℝ t K x) (coordinateVector 2 i))
      ((fderivWithin ℝ t K y) (coordinateVector 2 i)) ≤ _
  rw [hformula x hx, hformula y hy]
  exact hSum x hx y hy

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
