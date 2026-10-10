import B1NativeLoadedComparison_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem planarGradient_two_sub_v468 (v : E2 → ℝ) (hv : ContDiff ℝ ∞ v) :
    planarGradient (fun x => 2-v x) = fun x => -planarGradient v x := by
  funext x
  unfold planarGradient
  rw [fderiv_fun_sub (differentiableAt_const _) (hv.differentiable (by simp) x)]
  simp [Finset.sum_neg_distrib]

theorem classicalL_two_sub_v468
    (O : Set E2) (hO : IsOpen O) (a : E2 → Mat2) (b : E2 → E2) (c v : E2 → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hv : ContDiff ℝ ∞ v) (x : E2) (hx : x ∈ O) :
    classicalL a b c (fun y => 2-v y) x = 2*c x-classicalL a b c v x := by
  rw [classicalL,planarGradient_two_sub_v468 v hv,classicalL]
  have hm (y : E2) : matrixAction (a y) (-planarGradient v y) =
      -matrixAction (a y) (planarGradient v y) := by
    ext i
    simp [matrixAction,Finset.sum_neg_distrib]
  simp_rw [hm]
  simp only [PiLp.neg_apply]
  simp_rw [fderiv_fun_neg]
  simp [inner_neg_right,Fin.sum_univ_two]
  ring

/-- The same coercive native solution lies below any smooth supersolution
with boundary majorant 1. No sign condition on c is used. -/
theorem halfdisc_native_upper_comparison_v468
    (R δ : ℝ) (hδ : 0 < δ) (O : Set E2) (hO : IsOpen O) (hUO : halfDisc R ⊆ O)
    (a : E2 → Mat2) (b : E2 → E2) (c v : E2 → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hb : ContDiffOn ℝ ∞ b O) (hc : ContDiffOn ℝ ∞ c O)
    (hv : ContDiff ℝ ∞ v)
    (hvlp : MemLp v 2 (volume.restrict (halfDisc R)))
    (hdvlp : MemLp (planarGradient v) 2 (volume.restrict (halfDisc R)))
    (hclp : MemLp c 2 (volume.restrict (halfDisc R)))
    (hLlp : MemLp (classicalL a b c v) 2 (volume.restrict (halfDisc R)))
    (hvge : ∀ x ∈ halfDisc R, 1 ≤ v x)
    (hLv : ∀ x ∈ halfDisc R, classicalL a b c v x ≤ 0)
    (F : Pair (halfDisc R) →L[ℝ] Pair (halfDisc R) →L[ℝ] ℝ)
    (hFeq : ∀ p q, F p q =
      ∫ x in halfDisc R, inner ℝ (matrixAction (a x) (p.snd x)) (q.snd x) -
        (inner ℝ (b x) (p.snd x) + c x * p.fst x) * q.fst x)
    (hcoer : ∀ q : X (halfDisc R), δ * ‖q‖ ^ 2 ≤ F q.val q.val)
    (p : X (halfDisc R))
    (hsolve : ∀ q : X (halfDisc R), F p.val q.val =
      ∫ x in halfDisc R, c x * val (halfDisc R) q x) :
    ∀ᵐ x ∂(volume.restrict (halfDisc R)), val (halfDisc R) p x + 1 ≤ v x := by
  let U := halfDisc R
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  haveI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono (show U ⊆ Metric.ball (0 : E2) R from fun x hx => hx.1))
      measure_ball_lt_top).ne
  let w : E2 → ℝ := fun x => 2-v x
  have hw : ContDiff ℝ ∞ w := contDiff_const.sub hv
  have hgrad : planarGradient w = fun x => -planarGradient v x := planarGradient_two_sub_v468 v hv
  have hwl : MemLp w 2 (volume.restrict U) := (memLp_const 2).sub hvlp
  have hdwl : MemLp (planarGradient w) 2 (volume.restrict U) := by rw [hgrad]; exact hdvlp.neg
  have hLw : MemLp (classicalL a b c w) 2 (volume.restrict U) := by
    apply ((hclp.const_mul 2).sub hLlp).ae_eq
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact (classicalL_two_sub_v468 O hO a b c v ha hv x (hUO hx)).symm
  have hsn : ∀ q : X U, F (-p).val q.val = ∫ x in U, (-c x)*val U q x := by
    intro q
    change F (-p.val) q.val = _
    rw [map_neg,neg_apply,hsolve q]
    simp_rw [neg_mul]
    rw [integral_neg]
  have hcompare := halfdisc_native_loaded_barrier_comparison_v468 R δ hδ O hO hUO
    a b c (fun x => -c x) w ha hb hc hw hwl hdwl hclp hclp.neg hLw
    (fun x hx => by dsimp [w]; linarith [hvge x hx])
    (fun x hx => by
      rw [show classicalL a b c w x = _ from classicalL_two_sub_v468 O hO a b c v ha hv x (hUO hx)]
      linarith [hLv x hx]) F hFeq hcoer (-p) hsn
  have hn : val U (-p) =ᵐ[volume.restrict U] fun x => -val U p x :=
    Lp.coeFn_neg (valLp U p)
  filter_upwards [hcompare,hn] with x hx he
  rw [he] at hx
  dsimp [w] at hx
  linarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency
