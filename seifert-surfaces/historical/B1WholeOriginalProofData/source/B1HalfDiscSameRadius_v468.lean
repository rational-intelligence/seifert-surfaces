import B1HalfDiscPositiveBarrier_v468
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
open SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 100000

universe v
variable {K : SeifertSurfaces.Foundations.OrientedKnot}
variable {T : SeifertSurfaces.Foundations.TubularNeighborhood K}
variable {E : SeifertSurfaces.Foundations.SmoothExterior T}
variable {g : SeifertSurfaces.MetricFoundations.SmoothMetric E.Carrier}
variable {J : LongitudeFoliation.{v} E}

/-- The native variational construction at a specified coercive radius. -/
theorem actual_halfdisc_native_variational_at_radius_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (R κ : ℝ) (hR : 0 < R) (hRW : R < W.R) (hκ : 0 < κ)
    (htest : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc R →
      IntegrableOn (fun x => inner ℝ (matrixAction (W.a x) (planarGradient φ x))
        (planarGradient φ x) -
        (inner ℝ (W.b x) (planarGradient φ x) + W.c x * φ x) * φ x) (halfDisc R) ∧
      κ * (∫ x in halfDisc R, ‖planarGradient φ x‖ ^ 2) ≤
        ∫ x in halfDisc R, inner ℝ (matrixAction (W.a x) (planarGradient φ x))
          (planarGradient φ x) -
          (inner ℝ (W.b x) (planarGradient φ x) + W.c x * φ x) * φ x) :
    ∃ p : X (halfDisc R), ∀ q : X (halfDisc R),
      (∫ x in halfDisc R,
        inner ℝ (matrixAction (W.a x) (grad (halfDisc R) p x)) (grad (halfDisc R) q x) -
        (inner ℝ (W.b x) (grad (halfDisc R) p x) + W.c x * val (halfDisc R) p x) * val (halfDisc R) q x) =
      ∫ x in halfDisc R, W.c x * val (halfDisc R) q x := by
  obtain ⟨ha,hb,hc,A,B,C,hA,hB,hC,haBound,hbBound,hcBound⟩ :=
    actual_halfdisc_full_form_bounds_v468 D s W R hRW
  obtain ⟨F,heq,hint⟩ := halfdisc_full_form_data_v468 R W.a W.b W.c
    ha hb hc A B C hA hB hC haBound hbBound hcBound
  obtain ⟨P,hP,hpair⟩ := halfdisc_native_pair_poincare_v468
  let U := halfDisc R
  let μ := volume.restrict U
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono (show U ⊆ Metric.ball (0 : E2) R from fun x hx => hx.1))
      measure_ball_lt_top).ne
  have hcLp : MemLp W.c 2 μ := by
    apply MemLp.of_bound hc C
    have hU : MeasurableSet U := by
      change MeasurableSet (Metric.ball (0 : E2) R ∩ {x : E2 | 0 < x 1})
      exact (Metric.isOpen_ball.inter (isOpen_lt continuous_const
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
    filter_upwards [ae_restrict_mem hU] with x hx
    exact hcBound x hx
  let fst : X U →L[ℝ] Lp ℝ 2 μ := (WithLp.fstL 2 ℝ _ _).comp (space U).subtypeL
  let ell : X U →L[ℝ] ℝ := (innerSL ℝ (hcLp.toLp W.c)).comp fst
  let Bform : X U →L[ℝ] X U →L[ℝ] ℝ := F.bilinearComp (space U).subtypeL (space U).subtypeL
  have hcoer : ∀ p : X U, (κ / (1 + P * R ^ 2)) * ‖p‖ ^ 2 ≤ Bform p p :=
    halfdisc_full_form_coercivity_v468 R κ P hR hκ hP.le (hpair R hR)
      W.a W.b W.c F heq (fun φ hs hc ht => (htest φ hs hc ht).2)
  obtain ⟨p,hp,_⟩ := SeifertSurfaces.WeakSchauder.real_lax_milgram
    (fun pq => Bform pq.1 pq.2) Bform.isBoundedBilinearMap
    (κ / (1 + P * R ^ 2)) (by positivity) hcoer ell
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


/-- The exact native pair supplies a weak solution at its own radius. -/
theorem actual_halfdisc_pair_to_weak_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (R : ℝ) (hRW : R < W.R) (p : X (halfDisc R))
    (hsolve : ∀ q : X (halfDisc R),
      (∫ x in halfDisc R,
        inner ℝ (matrixAction (W.a x) (grad (halfDisc R) p x)) (grad (halfDisc R) q x) -
        (inner ℝ (W.b x) (grad (halfDisc R) p x) + W.c x * val (halfDisc R) p x) * val (halfDisc R) q x) =
      ∫ x in halfDisc R, W.c x * val (halfDisc R) q x) :
    ∃ h : E2 → ℝ, ∃ dh : E2 → E2,
      H1On (halfDisc R) h dh ∧
      H10On (halfDisc R) (fun x => h x - 1) dh ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h dh := by
  let U := halfDisc R
  let μ := volume.restrict U
  have hU : MeasurableSet U := by
    change MeasurableSet (Metric.ball (0 : E2) R ∩ {x : E2 | 0 < x 1})
    exact (Metric.isOpen_ball.inter (isOpen_lt continuous_const
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono (show U ⊆ Metric.ball (0 : E2) R from fun x hx => hx.1))
      measure_ball_lt_top).ne
  have hv : MemLp (val U p) 2 μ := Lp.memLp (valLp U p)
  have hg : MemLp (grad U p) 2 μ := Lp.memLp (gradLp U p)
  have hone : MemLp (fun _ : E2 => (1 : ℝ)) 2 μ := memLp_const 1
  let h := fun x => val U p x + 1
  let dh := grad U p
  have hp := halfdisc_pair_native_h10_v468 R p
  have hweak : WeakGradientOn U h dh := native_weak_gradient_add_one_v468 U _ _ hp.1
  refine ⟨h,dh,⟨hweak,hv.add hone,hg⟩,?_,hweak,?_⟩
  · simpa only [h,add_sub_cancel_right] using hp
  · intro φ hs hc ht
    have htH10 := halfdisc_native_smooth_h10_export_v468 R φ hs hc ht
    have hφ := htH10.1.2.1
    have hdφ := htH10.1.2.2
    let q : X U := ⟨pack U φ (planarGradient φ) hφ hdφ,
      (halfdisc_nativeH10_iff_pair_mem_export_v468 R φ (planarGradient φ) hφ hdφ).mp htH10⟩
    have hqval : val U q =ᵐ[μ] φ := hφ.coeFn_toLp
    have hqgrad : grad U q =ᵐ[μ] planarGradient φ := hdφ.coeFn_toLp
    obtain ⟨ha,hb,hc',A,B,C,hA,hB,hC,haBound,hbBound,hcBound⟩ :=
      actual_halfdisc_full_form_bounds_v468 D s W R hRW
    obtain ⟨F,hFeq,hint⟩ := halfdisc_full_form_data_v468 R W.a W.b W.c
      ha hb hc' A B C hA hB hC haBound hbBound hcBound
    have hcLp : MemLp W.c 2 μ := by
      apply MemLp.of_bound hc' C
      filter_upwards [ae_restrict_mem hU] with x hx
      exact hcBound x hx
    have hiload : IntegrableOn (fun x => W.c x * φ x) U := by
      apply (L2.integrable_inner (𝕜 := ℝ) (hcLp.toLp W.c) (hφ.toLp φ)).congr
      filter_upwards [hcLp.coeFn_toLp,hφ.coeFn_toLp] with x hx hφx
      rw [hx,hφx,Real.inner_apply]
    have he := hsolve q
    have hraw : (∫ x in U,
        inner ℝ (matrixAction (W.a x) (dh x)) (planarGradient φ x) -
        (inner ℝ (W.b x) (dh x) + W.c x * val U p x) * φ x) =
        ∫ x in U, W.c x * φ x := by
      convert he using 1
      · apply integral_congr_ae
        filter_upwards [hqval,hqgrad] with x hx hdx
        rw [hx,hdx]
      · apply integral_congr_ae
        filter_upwards [hqval] with x hx
        rw [hx]
    have hi := hint (val U p) dh φ (planarGradient φ) hv hg hφ hdφ
    have hih := hint h dh φ (planarGradient φ) (hv.add hone) hg hφ hdφ
    refine ⟨hih,?_⟩
    have hfun : (fun x => inner ℝ (matrixAction (W.a x) (dh x)) (planarGradient φ x) -
        (inner ℝ (W.b x) (dh x) + W.c x * h x) * φ x) =
        (fun x => inner ℝ (matrixAction (W.a x) (dh x)) (planarGradient φ x) -
          (inner ℝ (W.b x) (dh x) + W.c x * val U p x) * φ x) -
        (fun x => W.c x * φ x) := by
      funext x
      dsimp [h]
      ring
    rw [hfun]
    change (∫ x in U, (inner ℝ (matrixAction (W.a x) (dh x)) (planarGradient φ x) -
      (inner ℝ (W.b x) (dh x) + W.c x * val U p x) * φ x) - W.c x * φ x) = 0
    rw [integral_sub hi hiload,hraw,sub_self]


/-- Small-disc coercivity persists on every smaller half-disc with unchanged coefficients. -/
theorem halfdisc_test_coercivity_mono_v468 (R r κ : ℝ) (hrR : r ≤ R)
    (a : E2 → Mat2) (b : E2 → E2) (c : E2 → ℝ)
    (htest : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc R →
      IntegrableOn (fun x => inner ℝ (matrixAction (a x) (planarGradient φ x))
        (planarGradient φ x) -
        (inner ℝ (b x) (planarGradient φ x) + c x * φ x) * φ x) (halfDisc R) ∧
      κ * (∫ x in halfDisc R, ‖planarGradient φ x‖ ^ 2) ≤
        ∫ x in halfDisc R, inner ℝ (matrixAction (a x) (planarGradient φ x))
          (planarGradient φ x) -
          (inner ℝ (b x) (planarGradient φ x) + c x * φ x) * φ x) :
    ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc r →
      IntegrableOn (fun x => inner ℝ (matrixAction (a x) (planarGradient φ x))
        (planarGradient φ x) -
        (inner ℝ (b x) (planarGradient φ x) + c x * φ x) * φ x) (halfDisc r) ∧
      κ * (∫ x in halfDisc r, ‖planarGradient φ x‖ ^ 2) ≤
        ∫ x in halfDisc r, inner ℝ (matrixAction (a x) (planarGradient φ x))
          (planarGradient φ x) -
          (inner ℝ (b x) (planarGradient φ x) + c x * φ x) * φ x := by
  intro φ hs hc ht
  have hsub : halfDisc r ⊆ halfDisc R := fun x hx =>
    ⟨Metric.ball_subset_ball hrR hx.1,hx.2⟩
  have hh := htest φ hs hc (ht.trans hsub)
  have hv (x : E2) (hx : x ∉ halfDisc r) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (ht h))
  have hg (x : E2) (hx : x ∉ halfDisc r) : planarGradient φ x = 0 := by
    have hd := fderiv_of_notMem_tsupport ℝ (fun h => hx (ht h))
    simp [planarGradient,hd]
  have hinteq (f : E2 → ℝ) (hf : ∀ x, x ∉ halfDisc r → f x = 0) :
      (∫ x in halfDisc R, f x) = ∫ x in halfDisc r, f x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hf
    · intro x hx
      exact hf x (fun h => hx (hsub h))
  refine ⟨hh.1.mono_set hsub,?_⟩
  have heqg := hinteq (fun x => ‖planarGradient φ x‖ ^ 2)
    (fun x hx => by simp [hg x hx])
  have heqe := hinteq (fun x => inner ℝ (matrixAction (a x) (planarGradient φ x))
      (planarGradient φ x) -
      (inner ℝ (b x) (planarGradient φ x) + c x * φ x) * φ x)
    (fun x hx => by simp [hg x hx,hv x hx])
  rw [heqg,heqe] at hh
  exact hh.2

/-- Original-input Dirichlet weak solution and a positive classical barrier on one radius. -/
theorem actual_halfdisc_same_radius_solution_barrier_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0 < R ∧ R < W.R ∧ ∃ h : E2 → ℝ, ∃ dh : E2 → E2, ∃ v : E2 → ℝ,
      H1On (halfDisc R) h dh ∧
      H10On (halfDisc R) (fun x => h x - 1) dh ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h dh ∧
      ContDiff ℝ ∞ v ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ) ≤ v x ∧ v x ≤ 1) ∧
      (∀ x ∈ halfDisc R, 1 ≤ classicalL W.a W.b W.c v x) := by
  obtain ⟨R₀,κ,hR₀,hR₀W,hκ,htest⟩ := actual_small_halfdisc_test_coercivity_export_v468 D s W
  obtain ⟨R₁,hR₁,hR₁W,v,hvs,hvb,hvL⟩ := actual_halfdisc_positive_barrier_v468 D s W
  let R := min R₀ R₁
  have hR : 0 < R := lt_min hR₀ hR₁
  have hRW : R < W.R := lt_of_le_of_lt (min_le_left _ _) hR₀W
  have hcoer := halfdisc_test_coercivity_mono_v468 R₀ R κ (min_le_left _ _)
    W.a W.b W.c htest
  obtain ⟨p,hp⟩ := actual_halfdisc_native_variational_at_radius_v468 D s W R κ hR hRW hκ hcoer
  obtain ⟨h,dh,hh,htrace,heq⟩ := actual_halfdisc_pair_to_weak_v468 D s W R hRW p hp
  refine ⟨R,hR,hRW,h,dh,v,hh,htrace,heq,hvs,?_,?_⟩
  · intro x hx
    exact hvb x ⟨Metric.closedBall_subset_closedBall (min_le_right _ _) hx.1,hx.2⟩
  · intro x hx
    exact hvL x ⟨Metric.ball_subset_ball (min_le_right _ _) hx.1,hx.2⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
