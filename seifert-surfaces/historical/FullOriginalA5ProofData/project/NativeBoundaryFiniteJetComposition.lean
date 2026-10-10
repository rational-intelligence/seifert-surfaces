import NativeBoundaryFiniteHolderAssembly
import NativeBoundaryFiniteHolderTranslation
import NativeBoundarySecondOrderHolderGain

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem C1QuasilinearDirichletSolution.firstJetWithin_capHolder
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall c r ⊆ Metric.ball 0 ρ)
    (α : ℝ≥0) (hα1 : α ≤ 1) (n : ℕ)
    (hu : NativeCapHolder (nativeClosedBoundaryCap c r) α (n + 1) u) :
    NativeCapHolder (nativeClosedBoundaryCap c r) α n (firstJetWithin ρ u) := by
  let K := nativeClosedBoundaryCap c r
  have hKD := nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf
  have hKρ : K ⊆ closedHalfDisc ρ := fun x hx =>
    ⟨Metric.ball_subset_closedBall (hball hx.1), hx.2⟩
  have hG : NativeCapHolder K α n (planarGradientWithin u (closedHalfDisc ρ)) := by
    apply (hu.gradient_field hKD).congr
    intro x hx
    unfold planarGradientWithin
    rw [fderivWithin_subset hKρ (hKD x hx)
      (hsolution.c1.differentiableOn (by norm_num) x (hKρ hx))]
  have hx : NativeCapHolder K α n (fun x : E2 => x) :=
    NativeCapHolder.of_contDiffOn_succ c r hr hcf hα1
      ((contDiff_id.contDiffOn : ContDiffOn ℝ ∞ (fun x : E2 => x) K).of_le (by simp))
  exact hx.prodMk hKD ((hu.lower c r hr hα1).prodMk hKD hG)

theorem C1QuasilinearDirichletSolution.jet_composition_capHolder
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall c r ⊆ Metric.ball 0 ρ)
    (α : ℝ≥0) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ)
    (hu : NativeCapHolder (nativeClosedBoundaryCap c r) α (n + 1) u)
    (T : Set Jet) (hT : IsCompact T) (hTc : Convex ℝ T) (hTJ : T ⊆ J)
    (hmap : MapsTo (firstJetWithin ρ u) (nativeClosedBoundaryCap c r) T)
    (f : Jet → F) (hf : ContDiffOn ℝ ∞ f J) :
    NativeCapHolder (nativeClosedBoundaryCap c r) α n (fun x => f (firstJetWithin ρ u x)) :=
  (hsolution.firstJetWithin_capHolder c hcf r hr hball α hα1 n hu).comp_smooth
    c r hr hcf hα hα1 J T hsolution.jet_domain_open hT hTc hTJ f hf _ hmap

theorem C1QuasilinearDirichletSolution.local_capHolder_two
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, ∃ α : ℝ≥0, 0 < r ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      NativeCapHolder (nativeClosedBoundaryCap c r) α 2 u := by
  obtain ⟨r, α, hr, hα, hα1, hball, hu, hH⟩ :=
    hsolution.local_C2_holder_closed_boundary_cap hρ c hc
  let K := nativeClosedBoundaryCap c r
  have hKD := nativeClosedBoundaryCap_uniqueDiffOn c r hr hc.2
  have hKρ : K ⊆ closedHalfDisc ρ := fun x hx =>
    ⟨Metric.ball_subset_closedBall (hball hx.1), hx.2⟩
  refine ⟨r, α, hr, hα, hα1, hball, hu, ?_⟩
  intro j
  have hpartials : ContDiffOn ℝ 1
      (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 j)) K := by
    apply ((hu.fderivWithin hKD (m := 1) (by norm_num)).clm_apply contDiffOn_const).congr
    intro x hx
    rw [fderivWithin_subset hKρ (hKD x hx)
      (hsolution.c1.differentiableOn (by norm_num) x (hKρ hx))]
  apply (show NativeCapHolder K α 1
      (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 j)) from
      ⟨hpartials, fun i => hH i j⟩).congr
  intro x hx
  dsimp only
  rw [fderivWithin_subset hKρ (hKD x hx)
    (hsolution.c1.differentiableOn (by norm_num) x (hKρ hx))]

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
