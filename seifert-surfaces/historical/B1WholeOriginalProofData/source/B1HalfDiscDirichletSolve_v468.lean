import B1HalfDiscDirichletForm_v468
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

/-- The native half-disc completion inherits the scale-dependent Poincaré estimate. -/
theorem halfdisc_native_pair_poincare_v468 :
    ∃ P : ℝ, 0 < P ∧ ∀ R : ℝ, 0 < R → ∀ p : X (halfDisc R),
      ‖p‖ ^ 2 ≤ (1 + P * R ^ 2) * ‖gradLp (halfDisc R) p‖ ^ 2 := by
  obtain ⟨P,hP,hp⟩ := compact_halfdisc_test_poincare_export_v468
  refine ⟨P,hP,?_⟩
  intro R hR p
  let U := halfDisc R
  have hsmooth (q : Pair U) (hq : q ∈ SmoothGraph U) :
      ‖q.fst‖ ^ 2 ≤ P * R ^ 2 * ‖q.snd‖ ^ 2 := by
    obtain ⟨φ,hu,hg,hs,hc,ht,rfl⟩ := hq
    have hvnorm : ‖hu.toLp φ‖ ^ 2 = ∫ x in U, |φ x| ^ 2 := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp] with x hx
      rw [hx,Real.inner_apply,sq_abs]
      ring
    have hgnorm : ‖hg.toLp (planarGradient φ)‖ ^ 2 =
        ∫ x in U, ‖planarGradient φ x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx,real_inner_self_eq_norm_sq]
    change ‖hu.toLp φ‖ ^ 2 ≤ P * R ^ 2 * ‖hg.toLp (planarGradient φ)‖ ^ 2
    rw [hvnorm,hgnorm]
    exact hp R hR φ hs hc ht
  have hclosed : IsClosed {q : Pair U | ‖q.fst‖ ^ 2 ≤ P * R ^ 2 * ‖q.snd‖ ^ 2} :=
    isClosed_le ((WithLp.fstL 2 ℝ (Lp ℝ 2 (volume.restrict U))
      (Lp E2 2 (volume.restrict U))).continuous.norm.pow 2)
      (continuous_const.mul ((WithLp.sndL 2 ℝ (Lp ℝ 2 (volume.restrict U))
        (Lp E2 2 (volume.restrict U))).continuous.norm.pow 2))
  have hspace : (space U : Set (Pair U)) = closure (SmoothGraph U) := by
    rw [Submodule.topologicalClosure_coe,halfdisc_smoothGraph_span_export_v468 R]
  have hmem : p.val ∈ closure (SmoothGraph U) := by rw [← hspace]; exact p.property
  have hi : ‖p.val.fst‖ ^ 2 ≤ P * R ^ 2 * ‖p.val.snd‖ ^ 2 := closure_minimal hsmooth hclosed hmem
  have hn := WithLp.prod_norm_sq_eq_of_L2 p.val
  change ‖p.val‖ ^ 2 ≤ (1 + P * R ^ 2) * ‖p.val.snd‖ ^ 2
  nlinarith

/-- Smooth-test coercivity extends by continuity to the actual native H10 completion. -/
theorem halfdisc_full_form_coercivity_v468 (R κ P : ℝ) (hR : 0 < R) (hκ : 0 < κ)
    (hP : 0 ≤ P)
    (hp : ∀ p : X (halfDisc R),
      ‖p‖ ^ 2 ≤ (1 + P * R ^ 2) * ‖gradLp (halfDisc R) p‖ ^ 2)
    (a : E2 → Mat2) (b : E2 → E2) (c : E2 → ℝ)
    (F : Pair (halfDisc R) →L[ℝ] Pair (halfDisc R) →L[ℝ] ℝ)
    (heq : ∀ p q, F p q =
      ∫ x in halfDisc R, inner ℝ (matrixAction (a x) (p.snd x)) (q.snd x) -
        (inner ℝ (b x) (p.snd x) + c x * p.fst x) * q.fst x)
    (htest : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc R → κ * (∫ x in halfDisc R, ‖planarGradient φ x‖ ^ 2) ≤
        ∫ x in halfDisc R, inner ℝ (matrixAction (a x) (planarGradient φ x))
          (planarGradient φ x) -
          (inner ℝ (b x) (planarGradient φ x) + c x * φ x) * φ x) :
    ∀ p : X (halfDisc R),
      (κ / (1 + P * R ^ 2)) * ‖p‖ ^ 2 ≤ F p.val p.val := by
  let U := halfDisc R
  have hsmooth (q : Pair U) (hq : q ∈ SmoothGraph U) : κ * ‖q.snd‖ ^ 2 ≤ F q q := by
    obtain ⟨φ,hu,hg,hs,hc,ht,rfl⟩ := hq
    have hgnorm : ‖hg.toLp (planarGradient φ)‖ ^ 2 =
        ∫ x in U, ‖planarGradient φ x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx,real_inner_self_eq_norm_sq]
    have hFeq : F (pack U φ (planarGradient φ) hu hg) (pack U φ (planarGradient φ) hu hg) =
        ∫ x in U, inner ℝ (matrixAction (a x) (planarGradient φ x)) (planarGradient φ x) -
          (inner ℝ (b x) (planarGradient φ x) + c x * φ x) * φ x := by
      rw [heq]
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp,hg.coeFn_toLp] with x hvx hgx
      change inner ℝ (matrixAction (a x) ((hg.toLp _) x)) ((hg.toLp _) x) -
        (inner ℝ (b x) ((hg.toLp _) x) + c x * (hu.toLp _) x) * (hu.toLp _) x = _
      rw [hvx,hgx]
    change κ * ‖hg.toLp (planarGradient φ)‖ ^ 2 ≤ _
    rw [hgnorm,hFeq]
    exact htest φ hs hc ht
  have hclosed : IsClosed {q : Pair U | κ * ‖q.snd‖ ^ 2 ≤ F q q} :=
    isClosed_le (continuous_const.mul ((WithLp.sndL 2 ℝ
      (Lp ℝ 2 (volume.restrict U)) (Lp E2 2 (volume.restrict U))).continuous.norm.pow 2))
      (F.continuous₂.comp (continuous_id.prodMk continuous_id))
  intro p
  have hspace : (space U : Set (Pair U)) = closure (SmoothGraph U) := by
    rw [Submodule.topologicalClosure_coe,halfdisc_smoothGraph_span_export_v468 R]
  have hmem : p.val ∈ closure (SmoothGraph U) := by rw [← hspace]; exact p.property
  have hi : κ * ‖gradLp U p‖ ^ 2 ≤ F p.val p.val := closure_minimal hsmooth hclosed hmem
  have hd : 0 < 1 + P * R ^ 2 := by positivity
  calc
    (κ / (1 + P * R ^ 2)) * ‖p‖ ^ 2 ≤
        (κ / (1 + P * R ^ 2)) * ((1 + P * R ^ 2) * ‖gradLp U p‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hp p) (div_nonneg hκ.le hd.le)
    _ = κ * ‖gradLp U p‖ ^ 2 := by rw [← mul_assoc,div_mul_cancel₀ _ hd.ne']
    _ ≤ F p.val p.val := hi

universe v
variable {K : SeifertSurfaces.Foundations.OrientedKnot}
variable {T : SeifertSurfaces.Foundations.TubularNeighborhood K}
variable {E : SeifertSurfaces.Foundations.SmoothExterior T}
variable {g : SeifertSurfaces.MetricFoundations.SmoothMetric E.Carrier}
variable {J : LongitudeFoliation.{v} E}

/-- Boundedness of the literal smooth coefficients on the supplied compact collar. -/
theorem actual_halfdisc_full_form_bounds_v468 (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) (R : ℝ) (hRW : R < W.R) :
    (∀ i j, AEStronglyMeasurable (fun x => W.a x i j) (volume.restrict (halfDisc R))) ∧
    AEStronglyMeasurable W.b (volume.restrict (halfDisc R)) ∧
    AEStronglyMeasurable W.c (volume.restrict (halfDisc R)) ∧
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧
      (∀ x ∈ halfDisc R, ∀ v, ‖matrixAction (W.a x) v‖ ≤ A * ‖v‖) ∧
      (∀ x ∈ halfDisc R, ‖W.b x‖ ≤ B) ∧
      (∀ x ∈ halfDisc R, |W.c x| ≤ C) := by
  obtain ⟨O,hO,hWO,hOU,hjets,hf,hdf,ha,hq,hlg,hlh,hb,hc⟩ :=
    actual_coefficient_open_tube D s W
  have hcompact : IsCompact (closedHalfDisc W.R) :=
    (isCompact_closedBall (0 : E2) W.R).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hUW : halfDisc R ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball hRW.le hx.1),hx.2.le⟩
  have hU : MeasurableSet (halfDisc R) := by
    change MeasurableSet (Metric.ball (0 : E2) R ∩ {x : E2 | 0 < x 1})
    exact (Metric.isOpen_ball.inter (isOpen_lt continuous_const
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  refine ⟨fun i j => ((ha i j).continuousOn.mono (hUW.trans hWO)).aestronglyMeasurable hU,
    (hb.continuousOn.mono (hUW.trans hWO)).aestronglyMeasurable hU,
    (hc.continuousOn.mono (hUW.trans hWO)).aestronglyMeasurable hU,?_⟩
  choose A hAb using (fun i j : Fin 2 =>
    hcompact.exists_bound_of_continuousOn ((ha i j).continuousOn.mono hWO))
  obtain ⟨B,hBb⟩ := hcompact.exists_bound_of_continuousOn (hb.continuousOn.mono hWO)
  obtain ⟨C,hCb⟩ := hcompact.exists_bound_of_continuousOn (hc.continuousOn.mono hWO)
  let A' := 1 + |A 0 0| + |A 0 1| + |A 1 0| + |A 1 1|
  let B' := max B 1
  let C' := max C 1
  have hA : 0 < A' := by dsimp [A']; positivity
  refine ⟨4*A',B',C',by positivity,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_,
    fun x hx => (hBb x (hUW hx)).trans (le_max_left _ _),
    fun x hx => ?_⟩
  · intro x hx v
    have he (i j : Fin 2) : ‖W.a x i j‖ ≤ A' := by
      have hh := hAb i j x (hUW hx)
      fin_cases i <;> fin_cases j <;>
        calc
          _ ≤ A _ _ := hh
          _ ≤ |A _ _| := le_abs_self _
          _ ≤ A' := by dsimp [A']; linarith [abs_nonneg (A 0 0), abs_nonneg (A 0 1), abs_nonneg (A 1 0), abs_nonneg (A 1 1)]
    let w := matrixAction (W.a x) v
    have hw (i : Fin 2) : w i = W.a x i 0 * v 0 + W.a x i 1 * v 1 := by
      simp [w,matrixAction,Fin.sum_univ_two]
    have hwb (i : Fin 2) : ‖w i‖ ≤ 2 * A' * ‖v‖ := by
      rw [hw]
      calc
        _ ≤ ‖W.a x i 0 * v 0‖ + ‖W.a x i 1 * v 1‖ := norm_add_le _ _
        _ = ‖W.a x i 0‖ * ‖v 0‖ + ‖W.a x i 1‖ * ‖v 1‖ := by rw [norm_mul,norm_mul]
        _ ≤ A' * ‖v‖ + A' * ‖v‖ := add_le_add
          (mul_le_mul (he i 0) (PiLp.norm_apply_le v 0) (norm_nonneg _) hA.le)
          (mul_le_mul (he i 1) (PiLp.norm_apply_le v 1) (norm_nonneg _) hA.le)
        _ = _ := by ring
    have hnorm : ‖w‖ ≤ ‖w 0‖ + ‖w 1‖ := by
      have hn : ‖w‖ ^ 2 = ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 := by
        simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two,Real.norm_eq_abs,sq_abs]
      nlinarith [norm_nonneg w,norm_nonneg (w 0),norm_nonneg (w 1),
        mul_nonneg (norm_nonneg (w 0)) (norm_nonneg (w 1))]
    exact hnorm.trans (by nlinarith [hwb 0,hwb 1])
  · simpa only [Real.norm_eq_abs] using (hCb x (hUW hx)).trans (le_max_left _ _)

/-- Native Dirichlet solvability with datum 1, for all actual lower-order coefficients. -/
theorem actual_halfdisc_native_variational_solution_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0 < R ∧ R < W.R ∧
    ∃ p : X (halfDisc R), ∀ q : X (halfDisc R),
      (∫ x in halfDisc R,
        inner ℝ (matrixAction (W.a x) (grad (halfDisc R) p x)) (grad (halfDisc R) q x) -
        (inner ℝ (W.b x) (grad (halfDisc R) p x) + W.c x * val (halfDisc R) p x) * val (halfDisc R) q x) =
      ∫ x in halfDisc R, W.c x * val (halfDisc R) q x := by
  obtain ⟨R,κ,hR,hRW,hκ,htest⟩ := actual_small_halfdisc_test_coercivity_export_v468 D s W
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
  refine ⟨R,hR,hRW,p,?_⟩
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

end SeifertSurfaces.OriginalEndpoints.B1Tangency
