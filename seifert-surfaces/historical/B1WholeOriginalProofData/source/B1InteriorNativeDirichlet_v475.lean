import B1InteriorCoefficientWindow_v475
import B1HalfDiscWeakComparison_v468
import B1HalfDiscSmoothDataLp_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem interior_window_native_variational_v475
    (W : InteriorCoefficientWindow_v475) (κ : ℝ) (hκ : 0 < κ)
    (htest : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc W.R →
      IntegrableOn (fun x => inner ℝ (matrixAction (W.a x) (planarGradient φ x))
        (planarGradient φ x) -
        (inner ℝ (W.b x) (planarGradient φ x) + W.c x * φ x) * φ x) (halfDisc W.R) ∧
      κ * (∫ x in halfDisc W.R, ‖planarGradient φ x‖ ^ 2) ≤
        ∫ x in halfDisc W.R, inner ℝ (matrixAction (W.a x) (planarGradient φ x))
          (planarGradient φ x) -
          (inner ℝ (W.b x) (planarGradient φ x) + W.c x * φ x) * φ x) :
    ∃ p : X (halfDisc W.R), ∀ q : X (halfDisc W.R),
      (∫ x in halfDisc W.R,
        inner ℝ (matrixAction (W.a x) (grad (halfDisc W.R) p x)) (grad (halfDisc W.R) q x) -
        (inner ℝ (W.b x) (grad (halfDisc W.R) p x) + W.c x * val (halfDisc W.R) p x) * val (halfDisc W.R) q x) =
      ∫ x in halfDisc W.R, W.c x * val (halfDisc W.R) q x := by
  obtain ⟨ha,hb,hc,A,B,C,hA,hB,hC,haBound,hbBound,hcBound⟩ :=
    interior_window_full_form_bounds_v475 W
  obtain ⟨F,heq,hint⟩ := halfdisc_full_form_data_v468 W.R W.a W.b W.c
    ha hb hc A B C hA hB hC haBound hbBound hcBound
  obtain ⟨P,hP,hpair⟩ := halfdisc_native_pair_poincare_v468
  let U := halfDisc W.R
  let μ := volume.restrict U
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono (show U ⊆ Metric.ball (0 : E2) W.R from fun x hx => hx.1))
      measure_ball_lt_top).ne
  have hcLp : MemLp W.c 2 μ := by
    apply MemLp.of_bound hc C
    have hU : MeasurableSet U := by
      change MeasurableSet (Metric.ball (0 : E2) W.R ∩ {x : E2 | 0 < x 1})
      exact (Metric.isOpen_ball.inter (isOpen_lt continuous_const
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
    filter_upwards [ae_restrict_mem hU] with x hx
    exact hcBound x hx
  let fst : X U →L[ℝ] Lp ℝ 2 μ := (WithLp.fstL 2 ℝ _ _).comp (space U).subtypeL
  let ell : X U →L[ℝ] ℝ := (innerSL ℝ (hcLp.toLp W.c)).comp fst
  let Bform : X U →L[ℝ] X U →L[ℝ] ℝ := F.bilinearComp (space U).subtypeL (space U).subtypeL
  have hcoer : ∀ p : X U, (κ / (1 + P * W.R ^ 2)) * ‖p‖ ^ 2 ≤ Bform p p :=
    halfdisc_full_form_coercivity_v468 W.R κ P W.R_pos hκ hP.le (hpair W.R W.R_pos)
      W.a W.b W.c F heq (fun φ hs hc ht => (htest φ hs hc ht).2)
  obtain ⟨p,hp,_⟩ := SeifertSurfaces.WeakSchauder.real_lax_milgram
    (fun pq => Bform pq.1 pq.2) Bform.isBoundedBilinearMap
    (κ / (1 + P * W.R ^ 2)) (by positivity) hcoer ell
  refine ⟨p,?_⟩
  intro q
  have hell : ell q = ∫ x in U, W.c x * val U q x := by
    change inner ℝ (hcLp.toLp W.c) (valLp U q) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hcLp.coeFn_toLp] with x hx
    rw [hx,Real.inner_apply]
    rfl
  have he := hp q
  change F p.val q.val = ell q at he
  rw [heq,hell] at he
  exact he


theorem interior_window_native_positive_solution_v475
    (W : InteriorCoefficientWindow_v475) (κ : ℝ) (hκ : 0 < κ)
    (hcoer : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc W.R →
      IntegrableOn (fun x => inner ℝ (matrixAction (W.a x) (planarGradient φ x))
        (planarGradient φ x) -
        (inner ℝ (W.b x) (planarGradient φ x) + W.c x * φ x) * φ x) (halfDisc W.R) ∧
      κ * (∫ x in halfDisc W.R, ‖planarGradient φ x‖ ^ 2) ≤
        ∫ x in halfDisc W.R, inner ℝ (matrixAction (W.a x) (planarGradient φ x))
          (planarGradient φ x) -
          (inner ℝ (W.b x) (planarGradient φ x) + W.c x * φ x) * φ x)
    (v : E2 → ℝ) (hvs : ContDiff ℝ ∞ v)
    (hvb : ∀ x ∈ closedHalfDisc W.R, (1/2 : ℝ) ≤ v x ∧ v x ≤ 1)
    (hvL : ∀ x ∈ halfDisc W.R, 0 ≤ classicalL W.a W.b W.c v x) :
    ∃ h : E2 → ℝ, ∃ dh : E2 → E2,
      H1On (halfDisc W.R) h dh ∧
      H10On (halfDisc W.R) (fun x => h x - 1) dh ∧
      WeakLinearEquationOn (halfDisc W.R) W.a W.b W.c h dh ∧
      (∀ᵐ x ∂(volume.restrict (halfDisc W.R)), (1/2 : ℝ) ≤ h x) := by
  let R := W.R
  have hR := W.R_pos
  obtain ⟨p,hp⟩ := interior_window_native_variational_v475 W κ hκ hcoer
  obtain ⟨ha,hb,hc,A,B,C,hA,hB,hC,haBound,hbBound,hcBound⟩ :=
    interior_window_full_form_bounds_v475 W
  obtain ⟨F,hFeq,hint⟩ := halfdisc_full_form_data_v468 R W.a W.b W.c
    ha hb hc A B C hA hB hC haBound hbBound hcBound
  obtain ⟨P,hP,hpair⟩ := halfdisc_native_pair_poincare_v468
  have hFcoer := halfdisc_full_form_coercivity_v468 R κ P hR hκ hP.le (hpair R hR)
    W.a W.b W.c F hFeq (fun φ hs hc ht => (hcoer φ hs hc ht).2)
  have hFsolve : ∀ q : X (halfDisc R), F p.val q.val =
      ∫ x in halfDisc R, W.c x * val (halfDisc R) q x := by
    intro q
    rw [hFeq]
    exact hp q
  let O := W.O
  have hO := W.isOpen_O
  have haO := W.smooth_a
  have hbO := W.smooth_b
  have hcO := W.smooth_c
  have hHO : closedHalfDisc R ⊆ O := W.closed_subset
  have hUO : halfDisc R ⊆ O := fun x hx => hHO ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  obtain ⟨hvlp,hdvlp,hLlp⟩ := halfdisc_smooth_classical_data_L2_v468 R O hO hHO
    W.a W.b W.c v haO hbO hcO hvs
  let U := halfDisc R
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  haveI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono (show U ⊆ Metric.ball (0 : E2) R from fun x hx => hx.1))
      measure_ball_lt_top).ne
  have hcLp : MemLp W.c 2 (volume.restrict U) := by
    apply MemLp.of_bound hc C
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hcBound x hx
  have hcompare := halfdisc_native_barrier_comparison_v468 R (κ/(1+P*R^2))
    (by positivity) O hO hUO W.a W.b W.c v haO hbO hcO hvs hvlp hdvlp hcLp hLlp
    (fun x hx => (hvb x ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩).2)
    hvL
    F hFeq hFcoer p hFsolve
  let h := fun x => val U p x + 1
  let dh := grad U p
  have hn := halfdisc_pair_native_h10_v468 R p
  haveI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono (show U ⊆ Metric.ball (0 : E2) R from fun x hx => hx.1))
      measure_ball_lt_top).ne
  have hh : H1On U h dh :=
    ⟨native_weak_gradient_add_one_v468 U _ _ hn.1,hn.1.2.1.add (memLp_const 1),hn.1.2.2⟩
  have htrace : H10On U (fun x => h x - 1) dh := by
    simpa only [h,add_sub_cancel_right] using hn
  have heq : WeakLinearEquationOn U W.a W.b W.c h dh := by
    exact ⟨hh.1, by
      intro φ hs hcφ htφ
      have hφH := halfdisc_native_smooth_h10_export_v468 R φ hs hcφ htφ
      let q : X U := ⟨pack U φ (planarGradient φ) hφH.1.2.1 hφH.1.2.2,
        (halfdisc_nativeH10_iff_pair_mem_export_v468 R _ _ hφH.1.2.1 hφH.1.2.2).mp hφH⟩
      have hqv : val U q =ᵐ[volume.restrict U] φ := hφH.1.2.1.coeFn_toLp
      have hqg : grad U q =ᵐ[volume.restrict U] planarGradient φ := hφH.1.2.2.coeFn_toLp
      have hload : IntegrableOn (fun x => W.c x * φ x) U := hcLp.integrable_mul hφH.1.2.1
      have hi := hint (val U p) dh φ (planarGradient φ) hn.1.2.1 hn.1.2.2 hφH.1.2.1 hφH.1.2.2
      have hih := hint h dh φ (planarGradient φ) hh.2.1 hh.2.2 hφH.1.2.1 hφH.1.2.2
      have hraw : (∫ x in U, inner ℝ (matrixAction (W.a x) (dh x)) (planarGradient φ x) -
          (inner ℝ (W.b x) (dh x) + W.c x * val U p x) * φ x) =
          ∫ x in U, W.c x * φ x := by
        convert hp q using 1
        · apply integral_congr_ae
          filter_upwards [hqv,hqg] with x hx hdx
          rw [hx,hdx]
        · apply integral_congr_ae
          filter_upwards [hqv] with x hx
          rw [hx]
      refine ⟨hih,?_⟩
      have hexp : (fun x => inner ℝ (matrixAction (W.a x) (dh x)) (planarGradient φ x) -
          (inner ℝ (W.b x) (dh x) + W.c x * h x) * φ x) =
        (fun x => inner ℝ (matrixAction (W.a x) (dh x)) (planarGradient φ x) -
          (inner ℝ (W.b x) (dh x) + W.c x * val U p x) * φ x) - (fun x => W.c x * φ x) := by
        funext x
        dsimp [h]
        ring
      rw [hexp]
      change (∫ x in U, (inner ℝ (matrixAction (W.a x) (dh x)) (planarGradient φ x) -
        (inner ℝ (W.b x) (dh x) + W.c x * val U p x) * φ x) - W.c x * φ x) = 0
      rw [integral_sub hi hload,hraw,sub_self]⟩
  refine ⟨h,dh,hh,htrace,heq,?_⟩
  filter_upwards [hcompare,ae_restrict_mem hU.measurableSet] with x hx hxU
  exact (hvb x ⟨Metric.ball_subset_closedBall hxU.1,hxU.2.le⟩).1.trans hx

#print axioms interior_window_native_variational_v475
#print axioms interior_window_native_positive_solution_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
