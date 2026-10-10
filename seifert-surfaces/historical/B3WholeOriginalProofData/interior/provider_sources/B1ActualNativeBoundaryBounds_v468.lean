import B1NativeLiteralDirichlet_v468
import B1FlatDirichletBarrier_v468
import B1RadialDirichletBarrierFamily_v468
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

/-- The original native Dirichlet solution admits a smooth interior representative
with a quantitative bound tending to the datum 1 on the flat edge. -/
theorem actual_halfdisc_native_two_boundary_bounds_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    ∃ R S M N : ℝ, 0 < R ∧ R ≤ S ∧ S < W.R ∧ 0 < M ∧ 0 < N ∧ ∃ f : E2 → ℝ,
      ContDiffOn ℝ ∞ f (halfDisc R) ∧
      H1On (halfDisc R) f (planarGradient f) ∧
      H10On (halfDisc R) (fun x => f x - 1) (planarGradient f) ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c f (planarGradient f) ∧
      (∀ x ∈ halfDisc R, (1/2 : ℝ) ≤ f x) ∧
      (∀ x ∈ halfDisc R, |f x-1| ≤ M*(2*S*x 1-(x 1)^2)) ∧
      (∀ x ∈ halfDisc R, |f x-1| ≤ N*(R^2-‖x‖^2)) := by
  obtain ⟨R₀,κ,hR₀,hR₀W,hκ,htest⟩ := actual_small_halfdisc_test_coercivity_export_v468 D s W
  obtain ⟨R₁,M,hR₁,hR₁W,hM,hvs,hvb,hvL⟩ := actual_flat_dirichlet_supersolution_v468 D s W
  let v : E2 → ℝ := fun x => 1+M*(2*R₁*x 1-(x 1)^2)
  let w : E2 → ℝ := fun x => 2-v x
  have hws : ContDiff ℝ ∞ w := contDiff_const.sub hvs
  obtain ⟨R₂,N,hR₂,hR₂W,hN,hRadFamily⟩ := actual_radial_dirichlet_barrier_family_v468 D s W
  let R := min R₀ (min R₁ R₂)
  have hR : 0 < R := lt_min hR₀ (lt_min hR₁ hR₂)
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
  obtain ⟨hwlp,hdwlp,hLwlp⟩ := halfdisc_smooth_classical_data_L2_v468 R O hO hHO
    W.a W.b W.c w haO hbO hcO hws
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
    ⟨Metric.closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_left _ _)) hx.1,hx.2⟩
  have hsubU : halfDisc R ⊆ halfDisc R₁ := fun x hx =>
    ⟨Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx.1,hx.2⟩
  have hcompare := halfdisc_native_barrier_comparison_v468 R (κ/(1+P*R^2))
    (by positivity) O hO hUO W.a W.b W.c w haO hbO hcO hws hwlp hdwlp hcLp hLwlp
    (fun x hx => by dsimp [w]; linarith [(hvb x (hsubH ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩)).1])
    (fun x hx => by
      rw [show classicalL W.a W.b W.c w x = _ from
        classicalL_two_sub_v468 O hO W.a W.b W.c v haO hvs x (hUO hx)]
      have hh := hvL x (hsubU hx)
      linarith [neg_abs_le (W.c x)]) F hFeq hFcoer p hFsolve
  have hupper := halfdisc_native_upper_comparison_v468 R (κ/(1+P*R^2))
    (by positivity) O hO hUO W.a W.b W.c v haO hbO hcO hvs hvlp hdvlp hcLp hLlp
    (fun x hx => (hvb x (hsubH ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩)).1)
    (fun x hx => (hvL x (hsubU hx)).trans (by linarith [abs_nonneg (W.c x)])) F hFeq hFcoer p hFsolve
  have hRR₂ : R ≤ R₂ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hradSmooth,hradBound,hradL⟩ := hRadFamily R hR hRR₂
  let rad : E2 → ℝ := fun x => 1-N*(R^2-‖x‖^2)
  let radUp : E2 → ℝ := fun x => 2-rad x
  have hradUpSmooth : ContDiff ℝ ∞ radUp := contDiff_const.sub hradSmooth
  obtain ⟨hrlp,hdrLp,hLrLp⟩ := halfdisc_smooth_classical_data_L2_v468 R O hO hHO
    W.a W.b W.c rad haO hbO hcO hradSmooth
  obtain ⟨hrulp,hdruLp,hLruLp⟩ := halfdisc_smooth_classical_data_L2_v468 R O hO hHO
    W.a W.b W.c radUp haO hbO hcO hradUpSmooth
  have hradLo := halfdisc_native_barrier_comparison_v468 R (κ/(1+P*R^2))
    (by positivity) O hO hUO W.a W.b W.c rad haO hbO hcO hradSmooth hrlp hdrLp hcLp hLrLp
    (fun x hx => (hradBound x ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩).2)
    (fun x hx => (by linarith [abs_nonneg (W.c x)] : (0:ℝ) ≤ 2*|W.c x|+1).trans (hradL x hx))
    F hFeq hFcoer p hFsolve
  have hradHi := halfdisc_native_upper_comparison_v468 R (κ/(1+P*R^2))
    (by positivity) O hO hUO W.a W.b W.c radUp haO hbO hcO hradUpSmooth hrulp hdruLp hcLp hLruLp
    (fun x hx => by dsimp [radUp]; linarith [(hradBound x ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩).2])
    (fun x hx => by
      rw [show classicalL W.a W.b W.c radUp x = _ from
        classicalL_two_sub_v468 O hO W.a W.b W.c rad haO hradSmooth x (hUO hx)]
      linarith [hradL x hx,le_abs_self (W.c x)]) F hFeq hFcoer p hFsolve
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
  have heq : WeakLinearEquationOn U W.a W.b W.c h dh :=
    (actual_halfdisc_pair_weak_literal_v468 D s W R hRW p hp).2.2
  have hpos : ∀ᵐ x ∂volume.restrict U, (1/2 : ℝ) ≤ h x := by
    filter_upwards [hcompare,ae_restrict_mem hU.measurableSet] with x hx hxU
    have hbv := (hvb x (hsubH ⟨Metric.ball_subset_closedBall hxU.1,hxU.2.le⟩)).2
    dsimp [w] at hx
    change (1/2 : ℝ) ≤ val U p x + 1
    linarith
  have hbound : ∀ᵐ x ∂volume.restrict U, |h x-1| ≤ M*(2*R₁*x 1-(x 1)^2) := by
    filter_upwards [hcompare,hupper] with x hlo hup
    rw [abs_le]
    dsimp [w,v,h] at hlo hup ⊢
    constructor <;> linarith
  have hradial : ∀ᵐ x ∂volume.restrict U, |h x-1| ≤ N*(R^2-‖x‖^2) := by
    filter_upwards [hradLo,hradHi] with x hlo hup
    rw [abs_le]
    dsimp [radUp,rad,h] at hlo hup ⊢
    constructor <;> linarith
  obtain ⟨f,hf,hae⟩ := actual_halfdisc_native_smooth_interior_v468 D s W R hRW h dh hh heq
  have hdf := native_smooth_gradient_ae_v468 U hU h f dh hh hf hae
  have h1f := native_h1_congr_ae_v468 U h f dh (planarGradient f) hh hae hdf
  have ht1f := native_h10_congr_ae_v468 U (fun x => h x-1) (fun x => f x-1) dh
    (planarGradient f) htrace (hae.mono fun x hx => by dsimp only; rw [hx]) hdf
  have heqf := native_linear_congr_ae_v468 U W.a W.b W.c h f dh (planarGradient f) hh heq hae hdf
  have hpfae : ∀ᵐ x ∂volume.restrict U, (1/2 : ℝ) ≤ f x := by
    filter_upwards [hpos,hae] with x hx he
    rw [← he]; exact hx
  have hbf : ∀ᵐ x ∂volume.restrict U, |f x-1| ≤ M*(2*R₁*x 1-(x 1)^2) := by
    filter_upwards [hbound,hae] with x hx he
    rw [← he]; exact hx
  have hpfc : ∀ x ∈ U, (1/2 : ℝ) ≤ f x := by
    have hn : (fun x => min (-f x) (-(1/2 : ℝ))) =ᵐ[volume.restrict U] fun x => -f x :=
      hpfae.mono fun x hx => min_eq_left (by linarith)
    have he := Measure.eqOn_open_of_ae_eq hn hU
      (hf.continuousOn.neg.inf continuousOn_const) hf.continuousOn.neg
    intro x hx
    have hh := min_eq_left_iff.mp (he hx)
    linarith
  have hbfc : ∀ x ∈ U, |f x-1| ≤ M*(2*R₁*x 1-(x 1)^2) := by
    have hc1 : ContinuousOn (fun x => |f x-1|) U := (hf.continuousOn.sub continuousOn_const).abs
    have hc2 : ContinuousOn (fun x : E2 => M*(2*R₁*x 1-(x 1)^2)) U := by fun_prop
    have hn : (fun x => min |f x-1| (M*(2*R₁*x 1-(x 1)^2))) =ᵐ[volume.restrict U]
        fun x => |f x-1| := hbf.mono fun x hx => min_eq_left hx
    have he := Measure.eqOn_open_of_ae_eq hn hU (hc1.inf hc2) hc1
    intro x hx
    exact min_eq_left_iff.mp (he hx)
  have hrfae : ∀ᵐ x ∂volume.restrict U, |f x-1| ≤ N*(R^2-‖x‖^2) := by
    filter_upwards [hradial,hae] with x hx he
    rw [← he]; exact hx
  have hrfc : ∀ x ∈ U, |f x-1| ≤ N*(R^2-‖x‖^2) := by
    have hc1 : ContinuousOn (fun x => |f x-1|) U := (hf.continuousOn.sub continuousOn_const).abs
    have hc2 : ContinuousOn (fun x : E2 => N*(R^2-‖x‖^2)) U := by fun_prop
    have hn : (fun x => min |f x-1| (N*(R^2-‖x‖^2))) =ᵐ[volume.restrict U]
        fun x => |f x-1| := hrfae.mono fun x hx => min_eq_left hx
    have he := Measure.eqOn_open_of_ae_eq hn hU (hc1.inf hc2) hc1
    intro x hx
    exact min_eq_left_iff.mp (he hx)
  exact ⟨R,R₁,M,N,hR,(min_le_right _ _).trans (min_le_left _ _),hR₁W,hM,hN,f,hf,h1f,ht1f,heqf,hpfc,hbfc,hrfc⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
