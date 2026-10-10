import NativeBoundaryTangentialSchauderWeak
import NativeBoundaryHolderOperations

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- Holder control of the actual principal operator and forcing in the
zero-source tangential derivative equation, with no estimate premises. -/
theorem C1QuasilinearDirichletSolution.local_holder_tangential_schauder_coefficients
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, ∃ K α : ℝ≥0, 0 < δ ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      HolderOnWith K α (nativeTangentialSchauderCoefficients ρ Q g u).a
        (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) ∧
      HolderOnWith K α (nativeTangentialSchauderCoefficients ρ Q g u).d
        (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) := by
  obtain ⟨δ, H, α, hδ, hα, hα1, hball, hH⟩ := hsolution.local_holder_jet_composition hρ c hc
    (fun j : Jet => (fluxDp Q j, nativeTangentialForcingJet Q j))
    ((native_tangential_principal_forcing_jet_smooth J hsolution.jet_domain_open Q).of_le (by simp))
  let V := Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}
  let a := (nativeTangentialSchauderCoefficients ρ Q g u).a
  let F := fun x => nativeTangentialForcingJet Q (firstJetWithin ρ u x)
  let v := fun x : E2 => deriv (deriv g.value) (x 1) • coordinateVector 2 1
  have hVH : V ⊆ closedHalfDisc ρ := fun x hx => ⟨Metric.ball_subset_closedBall (hball hx.1), hx.2⟩
  have haH : HolderOnWith H α a V := by
    apply native_holder_of_norm_distance_bound
    intro x hx y hy
    have hh := hH.dist_le hx hy
    simp only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub] at hh
    simpa only [a, nativeTangentialSchauderCoefficients, dist_eq_norm] using (le_max_left _ _).trans hh
  have hFH : HolderOnWith H α F V := by
    apply native_holder_of_norm_distance_bound
    intro x hx y hy
    have hh := hH.dist_le hx hy
    simp only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub] at hh
    simpa only [F, dist_eq_norm] using (le_max_right _ _).trans hh
  have hvSmooth : ContDiffOn ℝ 1 v (Metric.ball 0 ρ) :=
    (g.smooth_second_deriv_extension_on_ball.of_le (by simp)).smul_const _
  have hvLocal : LocallyLipschitzOn (Metric.ball 0 ρ) v := by
    intro x hx
    obtain ⟨L, U, hU, hL⟩ := (hvSmooth.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).exists_lipschitzOnWith
    exact ⟨L, U, mem_nhdsWithin_of_mem_nhds hU, hL⟩
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall c δ) (hvLocal.mono hball)
  let D : ℝ≥0 := ⟨2 * δ, by positivity⟩
  have hdiam : ∀ x ∈ V, ∀ y ∈ V, edist x y ≤ D := by
    intro x hx y hy
    rw [edist_dist, ENNReal.ofReal_le_coe]
    change dist x y ≤ 2 * δ
    have hd := dist_triangle_right x y c
    have hx' : dist x c ≤ δ := hx.1
    have hy' : dist y c ≤ δ := hy.1
    linarith
  have hvH : HolderOnWith (L * D ^ (1 - (α : ℝ))) α v V := by
    simpa only [NNReal.coe_one] using HolderOnWith.of_le hdiam
      ((hL.mono (fun x hx => hx.1)).holderOnWith) hα1.le
  obtain ⟨A, hA⟩ := (closedHalfDisc_isCompact ρ).exists_bound_of_continuousOn
    (hsolution.continuous_native_flux_slices hρ).2.2
  obtain ⟨B, hB⟩ := (isCompact_closedBall c δ).exists_bound_of_continuousOn
    (hvSmooth.continuousOn.mono hball)
  let Ma := Real.toNNReal A
  let Mv := Real.toNNReal B
  have haB : ∀ x ∈ V, ‖a x‖ ≤ (Ma : ℝ) := fun x hx =>
    (hA x (hVH hx)).trans (Real.le_coe_toNNReal A)
  have hvB : ∀ x ∈ V, ‖v x‖ ≤ (Mv : ℝ) := fun x hx =>
    (hB x hx.1).trans (Real.le_coe_toNNReal B)
  have hprod := native_holder_clm_apply V a v H (L * D ^ (1 - (α : ℝ))) Ma Mv α haH hvH haB hvB
  have hdH : HolderOnWith (H + (H * Mv + Ma * (L * D ^ (1 - (α : ℝ))))) α
      (nativeTangentialSchauderCoefficients ρ Q g u).d V :=
    native_holder_add V F (fun x => a x (v x)) _ _ α hFH hprod
  let K := H + (H * Mv + Ma * (L * D ^ (1 - (α : ℝ))))
  refine ⟨δ, K, α, hδ, hα, hα1, hball, haH.mono_const (le_add_right le_rfl), hdH⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
