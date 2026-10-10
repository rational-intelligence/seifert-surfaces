import NativeBoundaryTangentialHolder

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_tangential_quotient_limit
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x : E2) (hx : x ∈ Metric.ball 0 ρ) (hn : 0 ≤ x 0) :
    Tendsto (fun h => differenceQuotient (fun y => u y - g.value (y 1)) 1 h x) (𝓝[>] 0)
      (𝓝 (fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) - deriv g.value (x 1))) := by
  have hud := (hsolution.c1.differentiableOn (by norm_num) x
    ⟨Metric.ball_subset_closedBall hx, hn⟩).hasFDerivWithinAt
  have hpath : HasDerivAt (fun t : ℝ => x + t • coordinateVector 2 1)
      (coordinateVector 2 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector 2 1)).const_add x
  have hmaps : ∀ᶠ t : ℝ in 𝓝 0, x + t • coordinateVector 2 1 ∈ closedHalfDisc ρ := by
    have hc : Continuous (fun t : ℝ => x + t • coordinateVector 2 1) := by fun_prop
    have hb := hc.continuousAt.eventually_mem (show Metric.ball 0 ρ ∈ 𝓝 (x + (0 : ℝ) • coordinateVector 2 1) by
      simpa only [zero_smul, add_zero] using Metric.isOpen_ball.mem_nhds hx)
    filter_upwards [hb] with t ht
    exact ⟨Metric.ball_subset_closedBall ht, by
      change 0 ≤ shift 1 t x 0
      rwa [tangent_shift_normal]⟩
  have hu : HasDerivAt (fun t : ℝ => u (x + t • coordinateVector 2 1))
      (fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1)) 0 :=
    hud.comp_hasDerivAt_of_eq 0 hpath hmaps (by simp)
  have hnorm : ‖x‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hcoord : |x 1| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (1 : Fin 2) (p := 2)
  have hg := (g.smooth.contDiffAt (isOpen_Ioo.mem_nhds (abs_lt.mp (hcoord.trans_lt hnorm)))).differentiableAt (by simp)
  have hgpath : HasDerivAt (fun t : ℝ => g.value (x 1 + t)) (deriv g.value (x 1)) 0 := by
    have hgat : HasDerivAt g.value (deriv g.value (x 1)) (x 1 + 0) := by
      simpa only [add_zero] using hg.hasDerivAt
    convert hgat.comp 0 ((hasDerivAt_const (0 : ℝ) (x 1)).add (hasDerivAt_id (0 : ℝ))) using 1 <;>
      simp only [Function.comp_def, Pi.add_apply, id_eq, zero_add, mul_one]
  simpa [differenceQuotient, shift, coordinateVector, PiLp.add_apply, PiLp.smul_apply,
    EuclideanSpace.single, div_eq_mul_inv, smul_eq_mul, mul_comm] using
    (hu.sub hgpath).tendsto_slope_zero_right

/-- The actual tangential within derivative of the original C1 solution has
a positive Hölder exponent at every flat boundary point. -/
theorem C1QuasilinearDirichletSolution.local_holder_tangential_derivative
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, ∃ K α : ℝ≥0, 0 < δ ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      HolderOnWith K α (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1))
        (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) := by
  obtain ⟨r, δ, K, α, hr, hδ, hδr, hα, hα1, houter, hquot⟩ :=
    hsolution.uniform_zero_trace_tangential_holder hρ c hc
  let B := Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}
  have hball : Metric.closedBall c δ ⊆ Metric.ball (0 : E2) ρ :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans houter
  let D : E2 → ℝ := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1)
  let G : E2 → ℝ := fun x => deriv g.value (x 1)
  have hholderD : HolderOnWith K α (D - G) B := by
    intro x hx y hy
    have hlx := native_tangential_quotient_limit hsolution x (hball hx.1) hx.2
    have hly := native_tangential_quotient_limit hsolution y (hball hy.1) hy.2
    apply le_of_tendsto (continuous_edist.tendsto (D x - G x, D y - G y) |>.comp
      (hlx.prodMk_nhds hly))
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds] with h hh hhr
    have hhpos : 0 < h := hh
    exact hquot h (ne_of_gt hhpos) (by simpa only [abs_of_pos hhpos] using hhr) x hx y hy
  have hgsmooth : ContDiffOn ℝ ∞ G (Metric.ball (0 : E2) ρ) := by
    apply (g.smooth.deriv_of_isOpen isOpen_Ioo (by simp)).comp
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.contDiffOn
    intro x hx
    have hn : ‖x‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    have hh : |x 1| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (1 : Fin 2) (p := 2)
    exact abs_lt.mp (hh.trans_lt hn)
  obtain ⟨L, hL⟩ := (hgsmooth.mono hball).exists_lipschitzOnWith (by simp)
    (convex_closedBall _ _) (isCompact_closedBall _ _)
  let diameter : ℝ≥0 := ⟨2 * δ, by positivity⟩
  have hdiam : ∀ x ∈ B, ∀ y ∈ B, edist x y ≤ diameter := by
    intro x hx y hy
    rw [edist_dist, ENNReal.ofReal_le_coe]
    change dist x y ≤ 2 * δ
    have hh := dist_triangle_right x y c
    have hx' : dist x c ≤ δ := hx.1
    have hy' : dist y c ≤ δ := hy.1
    linarith
  have hholderG := HolderOnWith.of_le hdiam
    (hL.holderOnWith.mono (show B ⊆ Metric.closedBall c δ from fun x hx => hx.1)) hα1.le
  refine ⟨δ, K + L * diameter ^ (1 - (α : ℝ)), α, hδ, hα, hα1, hball, ?_⟩
  intro x hx y hy
  calc
    edist (D x) (D y) = edist ((D x - G x) + G x) ((D y - G y) + G y) := by simp
    _ ≤ edist (D x - G x) (D y - G y) + edist (G x) (G y) := edist_add_add_le _ _ _ _
    _ ≤ (K : ℝ≥0∞) * edist x y ^ (α : ℝ) +
      (L * diameter ^ (1 - (α : ℝ)) : ℝ≥0) * edist x y ^ (α : ℝ) :=
      add_le_add (hholderD x hx y hy) (hholderG x hx y hy)
    _ = _ := by rw [ENNReal.coe_add, add_mul]

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
