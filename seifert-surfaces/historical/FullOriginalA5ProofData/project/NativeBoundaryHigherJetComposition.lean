import NativeBoundarySchauderFirstHolderGain
import NativeBoundaryHolderScalarOperations

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_contDiffOn_cap_holder
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E2) (r : ℝ) (hr : 0 < r) (f : E2 → F) (α : ℝ≥0) (hα1 : α ≤ 1)
    (hf : ContDiffOn ℝ 1 f (nativeClosedBoundaryCap c r)) :
    ∃ C : ℝ≥0, HolderOnWith C α f (nativeClosedBoundaryCap c r) := by
  let K := nativeClosedBoundaryCap c r
  have hK : IsCompact K := (isCompact_closedBall c r).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  obtain ⟨L, hL⟩ := hf.exists_lipschitzOnWith (by norm_num)
    (nativeClosedBoundaryCap_convex c r) hK
  let D : ℝ≥0 := ⟨2 * r, by positivity⟩
  have hdiam : ∀ x ∈ K, ∀ y ∈ K, edist x y ≤ D := by
    intro x hx y hy
    rw [edist_dist, ENNReal.ofReal_le_coe]
    change dist x y ≤ 2 * r
    have hh := dist_triangle_right x y c
    have hx' : dist x c ≤ r := hx.1
    have hy' : dist y c ≤ r := hy.1
    linarith
  exact ⟨L * D ^ (1 - (α : ℝ)), by
    simpa only [NNReal.coe_one] using HolderOnWith.of_le hdiam hL.holderOnWith hα1⟩

theorem C1QuasilinearDirichletSolution.firstJetWithin_contDiffOn_cap
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall c r ⊆ Metric.ball 0 ρ) (n : ℕ)
    (hu : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) u (nativeClosedBoundaryCap c r)) :
    ContDiffOn ℝ n (firstJetWithin ρ u) (nativeClosedBoundaryCap c r) := by
  let K := nativeClosedBoundaryCap c r
  have hKρ : K ⊆ closedHalfDisc ρ := fun x hx =>
    ⟨Metric.ball_subset_closedBall (hball hx.1), hx.2⟩
  have hD : ContDiffOn ℝ n (fderivWithin ℝ u K) K :=
    hu.fderivWithin (nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf) (by simp)
  have hDρ : ContDiffOn ℝ n (fderivWithin ℝ u (closedHalfDisc ρ)) K := by
    apply hD.congr
    intro x hx
    exact (fderivWithin_subset hKρ (nativeClosedBoundaryCap_uniqueDiffOn c r hr hcf x hx)
      (hsolution.c1.differentiableOn (by norm_num) x (hKρ hx))).symm
  have hG : ContDiffOn ℝ n (planarGradientWithin u (closedHalfDisc ρ)) K :=
    ContDiffOn.sum (fun i _ => (hDρ.clm_apply contDiffOn_const).smul contDiffOn_const)
  exact contDiffOn_id.prodMk ((hu.of_le (by exact_mod_cast Nat.le_succ n)).prodMk hG)

theorem C1QuasilinearDirichletSolution.jet_composition_contDiffOn_cap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hcf : c 0 = 0) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall c r ⊆ Metric.ball 0 ρ) (n : ℕ)
    (hu : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) u (nativeClosedBoundaryCap c r))
    (f : Jet → F) (hf : ContDiffOn ℝ ∞ f J) :
    ContDiffOn ℝ n (fun x => f (firstJetWithin ρ u x)) (nativeClosedBoundaryCap c r) := by
  have hmap : MapsTo (firstJetWithin ρ u) (nativeClosedBoundaryCap c r) J :=
    fun x hx => hsolution.attained_jets x ⟨Metric.ball_subset_closedBall (hball hx.1), hx.2⟩
  exact (hf.of_le (by simp)).comp
    (hsolution.firstJetWithin_contDiffOn_cap c hcf r hr hball n hu) hmap

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
