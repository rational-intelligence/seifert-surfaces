import B1InteriorNativeDirichlet_v475
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem interior_window_small_test_coercivity_v475
    (W : InteriorCoefficientWindow_v475) :
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
  let O := W.O
  have hO := W.isOpen_O
  have hWO := W.closed_subset
  have ha := W.smooth_a
  have hb := W.smooth_b
  have hc := W.smooth_c
  let ell := W.ell
  have hell := W.ell_pos
  have hbounds := W.coercive
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
  obtain ⟨P,hP,hpoincare⟩ := compact_halfdisc_test_poincare_export_v468
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
    have hl := hbounds x (hUW hx) (d x)
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

private theorem interior_quadratic_gradient_v475 (R M : ℝ) :
    planarGradient (fun x : E2 => 1 - M * (R ^ 2 - ‖x‖ ^ 2)) =
      fun x => (2 * M) • x := by
  funext x
  have hs : HasFDerivAt (fun y : E2 => 1 - M * (R ^ 2 - ‖y‖ ^ 2))
      ((2 * M) • innerSL ℝ x) x := by
    convert (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).sub
      (((hasFDerivAt_const (𝕜 := ℝ) (R ^ 2) x).sub ((hasStrictFDerivAt_norm_sq x).hasFDerivAt)).const_mul M) using 1 <;>
      ext y <;> simp [innerSL_apply_apply] <;> ring
  unfold planarGradient
  rw [hs.fderiv]
  ext i
  fin_cases i <;>
    simp [Fin.sum_univ_two,coordinateVector,innerSL_apply_apply,
      EuclideanSpace.inner_single_right,EuclideanSpace.single]

private theorem interior_quadratic_classical_v475 (R M : ℝ) (a : E2 → Mat2)
    (b : E2 → E2) (c : E2 → ℝ) (x : E2)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x) :
    classicalL a b c (fun y => 1 - M * (R ^ 2 - ‖y‖ ^ 2)) x =
      2 * M * (a x 0 0 + a x 1 1 +
        (∑ i : Fin 2, ∑ j : Fin 2,
          fderiv ℝ (fun y => a y i j) x (coordinateVector 2 i) * x j) + inner ℝ (b x) x) +
      c x * (1 - M * (R ^ 2 - ‖x‖ ^ 2)) := by
  rw [classicalL,interior_quadratic_gradient_v475]
  have hflux (i : Fin 2) :
      fderiv ℝ (fun y => matrixAction (a y) ((2 * M) • y) i) x (coordinateVector 2 i) =
        2 * M * (∑ j : Fin 2,
          fderiv ℝ (fun y => a y i j) x (coordinateVector 2 i) * x j) + 2 * M * a x i i := by
    have heq : (fun y => matrixAction (a y) ((2 * M) • y) i) =
        fun y => ∑ j : Fin 2, a y i j * ((2 * M) * y j) := by
      funext y
      simp [matrixAction]
    rw [heq,fderiv_fun_sum]
    · simp only [ContinuousLinearMap.sum_apply]
      have he (j : Fin 2) :
          fderiv ℝ (fun y => a y i j * ((2 * M) * y j)) x (coordinateVector 2 i) =
            fderiv ℝ (fun y => a y i j) x (coordinateVector 2 i) * (2 * M * x j) +
              a x i j * (2 * M * (if i = j then 1 else 0)) := by
        have hp : DifferentiableAt ℝ (fun y : E2 => (2 * M) * y j) x :=
          (differentiableAt_const _).mul ((EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt)
        rw [fderiv_fun_mul (ha i j) hp]
        simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
        have hder : fderiv ℝ (fun y : E2 => (2 * M) * y j) x =
            (2 * M) • EuclideanSpace.proj (𝕜 := ℝ) j := by
          exact ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.const_mul (2 * M)).fderiv
        rw [hder]
        fin_cases i <;> fin_cases j <;> simp [coordinateVector,EuclideanSpace.single] <;> ring
      simp_rw [he]
      fin_cases i <;> simp [Fin.sum_univ_two] <;> ring
    · intro j hj
      exact (ha i j).mul ((differentiableAt_const _).mul (EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt)
  simp_rw [hflux]
  rw [inner_smul_right]
  simp [Fin.sum_univ_two]
  ring

theorem interior_window_positive_barrier_v475 (W : InteriorCoefficientWindow_v475) :
    ∃ R : ℝ, 0 < R ∧ R < W.R ∧ ∃ v : E2 → ℝ,
      ContDiff ℝ ∞ v ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ) ≤ v x ∧ v x ≤ 1) ∧
      (∀ x ∈ halfDisc R, 1 ≤ classicalL W.a W.b W.c v x) := by
  let O := W.O
  have hO := W.isOpen_O
  have hWO := W.closed_subset
  have ha := W.smooth_a
  have hb := W.smooth_b
  have hc := W.smooth_c
  let ell := W.ell
  have hell := W.ell_pos
  have hbounds := W.coercive
  have hcompact : IsCompact (closedHalfDisc W.R) :=
    (isCompact_closedBall (0 : E2) W.R).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  choose A hAb using (fun i j : Fin 2 =>
    hcompact.exists_bound_of_continuousOn
      (((ha i j).continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply continuousOn_const |>.mono hWO :
        ContinuousOn (fun x => fderiv ℝ (fun y => W.a y i j) x (coordinateVector 2 i)) (closedHalfDisc W.R)))
  obtain ⟨B,hBb⟩ := hcompact.exists_bound_of_continuousOn (hb.continuousOn.mono hWO)
  obtain ⟨C,hCb⟩ := hcompact.exists_bound_of_continuousOn (hc.continuousOn.mono hWO)
  let A' := 1 + |A 0 0| + |A 0 1| + |A 1 0| + |A 1 1|
  let B' := max B 1
  let C' := max C 1
  let L := 4 * A' + B'
  have hA : 0 < A' := by dsimp [A']; positivity
  have hB : 0 < B' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hL : 0 < L := by dsimp [L]; positivity
  let M := (C' + 1) / ell
  have hM : 0 < M := div_pos (by positivity) hell
  let R := min (W.R / 2) (min 1 (min (ell / (2 * L)) (1 / (2 * M))))
  have hR : 0 < R := lt_min (half_pos W.R_pos) (lt_min zero_lt_one
    (lt_min (div_pos hell (by positivity)) (div_pos zero_lt_one (by positivity))))
  have hRW : R < W.R := lt_of_le_of_lt (min_le_left _ _) (by linarith [W.R_pos])
  have hR1 : R ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hRL : R ≤ ell / (2 * L) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hRM : R ≤ 1 / (2 * M) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  let v : E2 → ℝ := fun x => 1 - M * (R ^ 2 - ‖x‖ ^ 2)
  have hv : ContDiff ℝ ∞ v := by
    exact contDiff_const.sub (contDiff_const.mul (contDiff_const.sub (contDiff_norm_sq (𝕜 := ℝ) (n := ∞))))
  have hsub : closedHalfDisc R ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall hRW.le hx.1,hx.2⟩
  have hvbound (x : E2) (hx : x ∈ closedHalfDisc R) : (1/2 : ℝ) ≤ v x ∧ v x ≤ 1 := by
    have hn : ‖x‖ ≤ R := by simpa only [closedDisc,Metric.mem_closedBall,dist_zero_right] using hx.1
    have hn2 : ‖x‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hn
    have hRsq : R ^ 2 ≤ R := by nlinarith
    have hRM' : R * (2 * M) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 2 * M)).mp hRM
    dsimp [v]
    constructor <;> nlinarith [sq_nonneg ‖x‖,mul_nonneg hM.le (sub_nonneg.mpr hn2)]
  refine ⟨R,hR,hRW,v,hv,hvbound,?_⟩
  intro x hx
  have hxR : x ∈ closedHalfDisc R := ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have hxW := hsub hxR
  have hxO := hWO hxW
  have hdiff (i j : Fin 2) : DifferentiableAt ℝ (fun y => W.a y i j) x :=
    ((ha i j).contDiffAt (hO.mem_nhds hxO)).differentiableAt (by simp)
  have hentry (i j : Fin 2) : |fderiv ℝ (fun y => W.a y i j) x (coordinateVector 2 i)| ≤ A' := by
    have hh := hAb i j x hxW
    fin_cases i <;> fin_cases j <;>
      calc
        _ ≤ A _ _ := by simpa only [Real.norm_eq_abs] using hh
        _ ≤ |A _ _| := le_abs_self _
        _ ≤ A' := by dsimp [A']; linarith [abs_nonneg (A 0 0),abs_nonneg (A 0 1),abs_nonneg (A 1 0),abs_nonneg (A 1 1)]
  have hn : ‖x‖ ≤ R := by simpa only [closedDisc,Metric.mem_closedBall,dist_zero_right] using hxR.1
  have hbx : ‖W.b x‖ ≤ B' := (hBb x hxW).trans (le_max_left _ _)
  have hcx : |W.c x| ≤ C' := by simpa only [Real.norm_eq_abs] using (hCb x hxW).trans (le_max_left _ _)
  have htrace : 2 * ell ≤ W.a x 0 0 + W.a x 1 1 := by
    have h0 := hbounds x hxW (coordinateVector 2 0)
    have h1 := hbounds x hxW (coordinateVector 2 1)
    simp [coordinateVector,matrixAction,Fin.sum_univ_two,
      EuclideanSpace.inner_eq_star_dotProduct,dotProduct,EuclideanSpace.single,
      EuclideanSpace.real_norm_sq_eq] at h0 h1
    linarith
  have hterm (i j : Fin 2) :
      -(A' * R) ≤ fderiv ℝ (fun y => W.a y i j) x (coordinateVector 2 i) * x j := by
    have hncoord : |x j| ≤ R := (PiLp.norm_apply_le x j).trans hn
    have hh : |fderiv ℝ (fun y => W.a y i j) x (coordinateVector 2 i) * x j| ≤ A' * R := by
      rw [abs_mul]
      exact mul_le_mul (hentry i j) hncoord (abs_nonneg _) hA.le
    exact (neg_le_neg hh).trans (neg_abs_le _)
  have hbt : -(B' * R) ≤ inner ℝ (W.b x) x := by
    have hh := (abs_real_inner_le_norm (W.b x) x).trans
      (mul_le_mul hbx hn (norm_nonneg _) hB.le)
    exact (neg_le_neg hh).trans (neg_abs_le _)
  have hbracket : ell ≤ W.a x 0 0 + W.a x 1 1 +
      (∑ i : Fin 2, ∑ j : Fin 2,
        fderiv ℝ (fun y => W.a y i j) x (coordinateVector 2 i) * x j) + inner ℝ (W.b x) x := by
    have hLR : R * (2 * L) ≤ ell := (le_div_iff₀ (by positivity : 0 < 2 * L)).mp hRL
    simp only [Fin.sum_univ_two]
    dsimp [L] at hLR
    linarith [hterm 0 0,hterm 0 1,hterm 1 0,hterm 1 1]
  have hcv : -(C') ≤ W.c x * v x := by
    have hvx := hvbound x hxR
    have habsv : |v x| ≤ 1 := by rw [abs_of_nonneg (by linarith : 0 ≤ v x)]; exact hvx.2
    have hh : |W.c x * v x| ≤ C' := by
      rw [abs_mul]
      exact (mul_le_mul hcx habsv (abs_nonneg _) hC.le).trans_eq (mul_one _)
    exact (neg_le_neg hh).trans (neg_abs_le _)
  have hMe : M * ell = C' + 1 := div_mul_cancel₀ _ hell.ne'
  rw [show classicalL W.a W.b W.c v x = _ from interior_quadratic_classical_v475 R M W.a W.b W.c x hdiff]
  have hm := mul_le_mul_of_nonneg_left hbracket (show 0 ≤ 2 * M by positivity)
  change -(C') ≤ W.c x * (1 - M * (R ^ 2 - ‖x‖ ^ 2)) at hcv
  nlinarith

#print axioms interior_window_small_test_coercivity_v475
#print axioms interior_window_positive_barrier_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
