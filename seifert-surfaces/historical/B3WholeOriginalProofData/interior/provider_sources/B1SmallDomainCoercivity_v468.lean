import VM03ExactCaller_v464
import B1GraphCoefficients

noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
open SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem compact_halfdisc_test_poincare_v468 :
    ∃ P : ℝ, 0 < P ∧ ∀ R : ℝ, 0 < R → ∀ φ : E2 → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ halfDisc R →
      (∫ x in halfDisc R, |φ x| ^ 2) ≤
        P * R ^ 2 * ∫ x in halfDisc R, ‖planarGradient φ x‖ ^ 2 := by
  obtain ⟨P,hP,hbound⟩ := nativeH10_pair_poincare
  refine ⟨P,hP,?_⟩
  intro R hR φ hs hc ht
  let U := Metric.ball (0 : E2) R
  have htU : tsupport φ ⊆ U := fun x hx => (ht hx).1
  have hn := native_smooth_h10 0 R hR φ hs hc htU
  let hu := hn.1.2.1
  let hg := hn.1.2.2
  let p : X U := ⟨pack U φ (planarGradient φ) hu hg,
    (nativeH10_iff_pair_mem 0 R hR φ (planarGradient φ) hu hg).mp hn⟩
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
  have hpair : ‖p‖ ^ 2 = ‖hu.toLp φ‖ ^ 2 + ‖hg.toLp (planarGradient φ)‖ ^ 2 := by
    change ‖pack U φ (planarGradient φ) hu hg‖ ^ 2 = _
    exact WithLp.prod_norm_sq_eq_of_L2 _
  have hb := hbound 0 R hR p
  change ‖p‖ ^ 2 ≤ (1 + P * R ^ 2) * ‖hg.toLp (planarGradient φ)‖ ^ 2 at hb
  rw [hpair] at hb
  have hval : ∀ x, x ∉ halfDisc R → φ x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (ht h))
  have hgrad : ∀ x, x ∉ halfDisc R → planarGradient φ x = 0 := by
    intro x hx
    have hd := fderiv_of_notMem_tsupport ℝ (fun h => hx (ht h))
    simp [planarGradient,hd]
  have heqval : (∫ x in U, |φ x| ^ 2) = ∫ x in halfDisc R, |φ x| ^ 2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · intro x hx; simp [hval x hx]
    · intro x hx; simp [hval x (fun h => hx h.1)]
  have heqgrad : (∫ x in U, ‖planarGradient φ x‖ ^ 2) =
      ∫ x in halfDisc R, ‖planarGradient φ x‖ ^ 2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · intro x hx; simp [hgrad x hx]
    · intro x hx; simp [hgrad x (fun h => hx h.1)]
  rw [hvnorm,hgnorm,heqval,heqgrad] at hb
  nlinarith

universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

private theorem actual_small_halfdisc_test_coercivity_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    ∃ R κ : ℝ, 0 < R ∧ R < W.R ∧ 0 < κ ∧
      ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ halfDisc R →
        IntegrableOn (fun x => inner ℝ (matrixAction (W.a x) (planarGradient φ x))
          (planarGradient φ x) -
          (inner ℝ (W.b x) (planarGradient φ x) + W.c x * φ x) * φ x) (halfDisc R) ∧
        κ * (∫ x in halfDisc R, ‖planarGradient φ x‖ ^ 2) ≤
          ∫ x in halfDisc R, inner ℝ (matrixAction (W.a x) (planarGradient φ x))
            (planarGradient φ x) -
            (inner ℝ (W.b x) (planarGradient φ x) + W.c x * φ x) * φ x := by
  obtain ⟨O,hO,hWO,hOU,hjets,hf,hdf,ha,hq,hlg,hlh,hb,hc⟩ :=
    actual_coefficient_open_tube D s W
  obtain ⟨hformula,hsym,ell,C,hell,hC,hbounds⟩ := actual_slope_hessian_uniform_bounds D s W
  have hcompact : IsCompact (closedHalfDisc W.R) :=
    (isCompact_closedBall (0 : E2) W.R).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  obtain ⟨B,hBbound⟩ := hcompact.exists_bound_of_continuousOn (hb.continuousOn.mono hWO)
  obtain ⟨Z,hZbound⟩ := hcompact.exists_bound_of_continuousOn (hc.continuousOn.mono hWO)
  let B' := max B 0
  let Z' := max Z 0
  let Q := B' ^ 2 / ell + Z'
  have hB' : 0 ≤ B' := le_max_right _ _
  have hZ' : 0 ≤ Z' := le_max_right _ _
  have hQ : 0 ≤ Q := add_nonneg (div_nonneg (sq_nonneg _) hell.le) hZ'
  obtain ⟨P,hP,hpoincare⟩ := compact_halfdisc_test_poincare_v468
  let A := 8 * (1 + Q) * (1 + P)
  have hA : 0 < A := by dsimp [A]; positivity
  let R := min (W.R / 2) (min 1 (ell / A))
  have hR : 0 < R := lt_min (half_pos W.R_pos) (lt_min zero_lt_one (div_pos hell hA))
  have hRW : R < W.R := lt_of_le_of_lt (min_le_left _ _) (by linarith [W.R_pos])
  have hR1 : R ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hRA : R ≤ ell / A := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : Q * P * R ^ 2 ≤ ell / 4 := by
    have hmul : R * A ≤ ell := (le_div_iff₀ hA).mp hRA
    have hs : R ^ 2 ≤ R := by nlinarith
    have hQP : 4 * (Q * P) ≤ A := by
      dsimp [A]
      nlinarith [mul_nonneg hQ hP.le]
    have ht := mul_le_mul_of_nonneg_left hs (mul_nonneg hQ hP.le)
    have ht2 := mul_le_mul_of_nonneg_left hQP hR.le
    nlinarith
  refine ⟨R,ell / 4,hR,hRW,by positivity,?_⟩
  intro φ hs hφc ht
  let U := halfDisc R
  let d := planarGradient φ
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hUW : U ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball hRW.le hx.1),hx.2.le⟩
  have hd : Continuous d := by
    dsimp [d,planarGradient]
    apply continuous_finsetSum
    intro i hi
    exact ((hs.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const
  have hdcompact : HasCompactSupport d := by
    apply hφc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra h
    have hder := fderiv_of_notMem_tsupport ℝ h
    apply hx
    simp [d,planarGradient,hder]
  have hdsupport : tsupport d ⊆ U := by
    apply (show tsupport d ⊆ tsupport φ from ?_).trans ht
    apply closure_minimal _ (hφc.isClosed)
    intro x hx
    by_contra h
    have hder := fderiv_of_notMem_tsupport ℝ h
    apply hx
    simp [d,planarGradient,hder]
  have product_integrable (F ψ : E2 → ℝ) (hF : ContinuousOn F U)
      (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U) :
      Integrable (fun x => F x * ψ x) := by
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp
      (((hF.mono hψs).mul hψ.continuousOn).integrableOn_compact hψc)
    intro x hx
    exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)
  have haction : ContinuousOn (fun x => matrixAction (W.a x) (d x)) U := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_finsetSum
    intro j hj
    exact ((ha i j).continuousOn.mono (hUW.trans hWO)).mul
      ((EuclideanSpace.proj j).continuous.comp hd).continuousOn
  have hleading : IntegrableOn (fun x => inner ℝ (matrixAction (W.a x) (d x)) (d x)) U := by
    change Integrable (fun x => inner ℝ (matrixAction (W.a x) (d x)) (d x)) (volume.restrict U)
    simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial, dotProduct,Fin.sum_univ_two]
    apply Integrable.add
    · simpa only [Function.comp_apply, EuclideanSpace.coe_proj, mul_comm] using (product_integrable _ _
        ((EuclideanSpace.proj 0).continuous.comp_continuousOn haction)
        ((EuclideanSpace.proj 0).continuous.comp hd)
        (hdcompact.comp_left (g := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) (map_zero _))
        ((tsupport_comp_subset (map_zero (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2))) d).trans hdsupport)).restrict
    · simpa only [Function.comp_apply, EuclideanSpace.coe_proj, mul_comm] using (product_integrable _ _
        ((EuclideanSpace.proj 1).continuous.comp_continuousOn haction)
        ((EuclideanSpace.proj 1).continuous.comp hd)
        (hdcompact.comp_left (g := EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) (map_zero _))
        ((tsupport_comp_subset (map_zero (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))) d).trans hdsupport)).restrict
  have hlower : IntegrableOn (fun x => (inner ℝ (W.b x) (d x) + W.c x * φ x) * φ x) U :=
    (product_integrable _ _ (((hb.continuousOn.mono (hUW.trans hWO)).inner hd.continuousOn).add
      ((hc.continuousOn.mono (hUW.trans hWO)).mul hs.continuous.continuousOn))
      hs.continuous hφc ht).restrict
  have henergy := hleading.sub hlower
  have hφLp : MemLp φ 2 (volume.restrict U) := (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hφc).restrict U
  have hdLp : MemLp d 2 (volume.restrict U) := (hd.memLp_of_hasCompactSupport (μ := volume) hdcompact).restrict U
  have hφsq : IntegrableOn (fun x => |φ x| ^ 2) U := by
    change Integrable _ (volume.restrict U)
    exact (hφLp.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).congr
      (Filter.Eventually.of_forall fun x => by rfl)
  have hdsq : IntegrableOn (fun x => ‖d x‖ ^ 2) U :=
    hdLp.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hpoint (x : E2) (hx : x ∈ U) :
      ell / 2 * ‖d x‖ ^ 2 - Q * |φ x| ^ 2 ≤
        inner ℝ (matrixAction (W.a x) (d x)) (d x) -
          (inner ℝ (W.b x) (d x) + W.c x * φ x) * φ x := by
    have hl := (hbounds x (hUW hx) (d x)).1
    rw [real_inner_comm] at hl
    have hbx : ‖W.b x‖ ≤ B' := (hBbound x (hUW hx)).trans (le_max_left _ _)
    have hcx : |W.c x| ≤ Z' := by
      simpa only [Real.norm_eq_abs] using (hZbound x (hUW hx)).trans (le_max_left _ _)
    have hinner := abs_real_inner_le_norm (W.b x) (d x)
    have hbterm : inner ℝ (W.b x) (d x) * φ x ≤ B' * ‖d x‖ * |φ x| := by
      calc
        inner ℝ (W.b x) (d x) * φ x ≤ |inner ℝ (W.b x) (d x) * φ x| := le_abs_self _
        _ = |inner ℝ (W.b x) (d x)| * |φ x| := abs_mul _ _
        _ ≤ (‖W.b x‖ * ‖d x‖) * |φ x| := mul_le_mul_of_nonneg_right hinner (abs_nonneg _)
        _ ≤ B' * ‖d x‖ * |φ x| := by gcongr
    have hcterm : W.c x * φ x * φ x ≤ Z' * |φ x| ^ 2 := by
      calc
        W.c x * φ x * φ x ≤ |W.c x * φ x * φ x| := le_abs_self _
        _ = |W.c x| * |φ x| ^ 2 := by rw [abs_mul,abs_mul]; ring
        _ ≤ Z' * |φ x| ^ 2 := mul_le_mul_of_nonneg_right hcx (sq_nonneg _)
    have hyoung : B' * ‖d x‖ * |φ x| ≤
        ell / 2 * ‖d x‖ ^ 2 + (B' ^ 2 / ell) * |φ x| ^ 2 := by
      have hsq := sq_nonneg (ell * ‖d x‖ - B' * |φ x|)
      have hdiv : B' ^ 2 / ell * ell = B' ^ 2 := div_mul_cancel₀ _ hell.ne'
      nlinarith [sq_nonneg (B' * |φ x|),mul_pos hell hell]
    dsimp [Q]
    nlinarith
  have hineq := integral_mono_ae ((hdsq.const_mul (ell / 2)).sub (hφsq.const_mul Q)) henergy
    (by filter_upwards [ae_restrict_mem hU.measurableSet] with x hx; exact hpoint x hx)
  simp only [Pi.sub_apply] at hineq
  rw [integral_sub (hdsq.const_mul (ell / 2)) (hφsq.const_mul Q),
    integral_const_mul,integral_const_mul] at hineq
  have hp := hpoincare R hR φ hs hφc ht
  have hnonneg : 0 ≤ ∫ x in U, ‖d x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hlow := mul_le_mul_of_nonneg_left hp hQ
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hnonneg
  refine ⟨henergy,?_⟩
  change ell / 4 * (∫ x in U, ‖d x‖ ^ 2) ≤ _
  change (∫ x in U, |φ x| ^ 2) ≤ P * R ^ 2 * ∫ x in U, ‖d x‖ ^ 2 at hp
  nlinarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet

theorem compact_halfdisc_test_poincare_export_v468 :
    ∃ P : ℝ, 0 < P ∧ ∀ R : ℝ, 0 < R → ∀ φ : E2 → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ halfDisc R →
      (∫ x in halfDisc R, |φ x| ^ 2) ≤
        P * R ^ 2 * ∫ x in halfDisc R, ‖planarGradient φ x‖ ^ 2 := compact_halfdisc_test_poincare_v468

theorem actual_small_halfdisc_test_coercivity_export_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    ∃ R κ : ℝ, 0 < R ∧ R < W.R ∧ 0 < κ ∧
      ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ halfDisc R →
        IntegrableOn (fun x => inner ℝ (matrixAction (W.a x) (planarGradient φ x))
          (planarGradient φ x) -
          (inner ℝ (W.b x) (planarGradient φ x) + W.c x * φ x) * φ x) (halfDisc R) ∧
        κ * (∫ x in halfDisc R, ‖planarGradient φ x‖ ^ 2) ≤
          ∫ x in halfDisc R, inner ℝ (matrixAction (W.a x) (planarGradient φ x))
            (planarGradient φ x) -
            (inner ℝ (W.b x) (planarGradient φ x) + W.c x * φ x) * φ x := actual_small_halfdisc_test_coercivity_v468 D s W

end SeifertSurfaces.OriginalEndpoints.B1Tangency
