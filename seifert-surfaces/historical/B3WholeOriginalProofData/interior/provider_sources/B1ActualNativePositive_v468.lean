import B1HalfDiscWeakComparison_v468
import B1HalfDiscSmoothDataLp_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The original data give an actual native Dirichlet solution with a positive a.e. lower bound;
all coefficients and both trace/gradient representatives are literal. -/
theorem actual_halfdisc_native_positive_solution_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0 < R ∧ R < W.R ∧ ∃ h : E2 → ℝ, ∃ dh : E2 → E2,
      H1On (halfDisc R) h dh ∧
      H10On (halfDisc R) (fun x => h x - 1) dh ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h dh ∧
      (∀ᵐ x ∂(volume.restrict (halfDisc R)), (1/2 : ℝ) ≤ h x) := by
  obtain ⟨R₀,κ,hR₀,hR₀W,hκ,htest⟩ := actual_small_halfdisc_test_coercivity_export_v468 D s W
  obtain ⟨R₁,hR₁,hR₁W,v,hvs,hvb,hvL⟩ := actual_halfdisc_positive_barrier_v468 D s W
  let R := min R₀ R₁
  have hR : 0 < R := lt_min hR₀ hR₁
  have hRW : R < W.R := lt_of_le_of_lt (min_le_left _ _) hR₀W
  have hcoer := halfdisc_test_coercivity_mono_v468 R₀ R κ (min_le_left _ _)
    W.a W.b W.c htest
  obtain ⟨p,hp⟩ := actual_halfdisc_native_variational_at_radius_v468 D s W R κ hR hRW hκ hcoer
  obtain ⟨ha,hb,hc,A,B,C,hA,hB,hC,haBound,hbBound,hcBound⟩ :=
    actual_halfdisc_full_form_bounds_v468 D s W R hRW
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
  obtain ⟨O,hO,hWO,hOU,hjets,hf,hdf,haO,hq,hlg,hlh,hbO,hcO⟩ :=
    actual_coefficient_open_tube D s W
  have hHO : closedHalfDisc R ⊆ O := fun x hx =>
    hWO ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩
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
  have hsubH : closedHalfDisc R ⊆ closedHalfDisc R₁ := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (min_le_right _ _) hx.1,hx.2⟩
  have hsubU : halfDisc R ⊆ halfDisc R₁ := fun x hx =>
    ⟨Metric.ball_subset_ball (min_le_right _ _) hx.1,hx.2⟩
  have hcompare := halfdisc_native_barrier_comparison_v468 R (κ/(1+P*R^2))
    (by positivity) O hO hUO W.a W.b W.c v haO hbO hcO hvs hvlp hdvlp hcLp hLlp
    (fun x hx => (hvb x (hsubH ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩)).2)
    (fun x hx => le_trans (by norm_num : (0 : ℝ) ≤ 1) (hvL x (hsubU hx)))
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
  refine ⟨R,hR,hRW,h,dh,hh,htrace,heq,?_⟩
  filter_upwards [hcompare,ae_restrict_mem hU.measurableSet] with x hx hxU
  exact (hvb x (hsubH ⟨Metric.ball_subset_closedBall hxU.1,hxU.2.le⟩)).1.trans hx

end SeifertSurfaces.OriginalEndpoints.B1Tangency
