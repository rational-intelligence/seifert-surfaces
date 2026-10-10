import B1ChartMetricProvider
import B1GraphCoefficients
import B1GraphEquation_v468
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem normalized_coefficients_v468 (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) (N : PositiveNormalization W) :
    SmoothEllipticOn N.normalizedA N.normalizedB (fun _ => 0) (closedHalfDisc (N.R / 2)) ∧
    (∀ i j, LipschitzBoundOn (fun x => N.normalizedA x i j) (closedHalfDisc (N.R / 2))) ∧
    BoundedOn N.normalizedB (closedHalfDisc (N.R / 2)) ∧
    (∀ x ∈ closedHalfDisc (N.R / 2), Matrix.det (N.normalizedA x) = 1) ∧
    (∀ x ∈ flatArc (N.R / 2), N.v x = 0) ∧
    (∀ x ∈ closedHalfDisc (N.R / 2), ContDiffAt ℝ ∞ N.factor x) := by
  classical
  let H := closedHalfDisc (N.R / 2)
  have hNW : H ⊆ closedHalfDisc W.R := by
    intro x hx
    refine ⟨Metric.closedBall_subset_closedBall (by linarith [N.R_pos, N.R_inside]) hx.1, hx.2⟩
  have hNR : H ⊆ closedHalfDisc N.R := by
    intro x hx
    exact ⟨Metric.closedBall_subset_closedBall (by linarith [N.R_pos]) hx.1, hx.2⟩
  have hcompact : IsCompact H :=
    (isCompact_closedBall (0 : E2) (N.R / 2)).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hconvex : Convex ℝ H := by
    apply (convex_closedBall (0 : E2) (N.R / 2)).inter
    exact convex_halfSpace_ge (f := fun x : E2 => x 1) ⟨by intros; rfl, by intros; rfl⟩ 0
  have hnonempty : H.Nonempty := by
    exact ⟨0, Metric.mem_closedBall_self (half_pos N.R_pos).le, by simp⟩
  obtain ⟨O, hO, hWO, hOU, hjet, hheight, hgrad, ha, hq, hlg, hlh, hb, hc⟩ :=
    actual_coefficient_open_tube D s W
  obtain ⟨hformula, hsym, ell, C, hell, hC, hbounds⟩ :=
    actual_slope_hessian_uniform_bounds D s W
  have hapos (x : E2) (hx : x ∈ H) : 0 < Matrix.det (W.a x) := by
    have hM : (W.a x).PosDef := by
      apply Matrix.posDef_iff_dotProduct_mulVec.mpr
      constructor
      · rw [Matrix.isHermitian_iff_isSymm]
        ext i j
        exact hsym x (hNW hx) j i
      · intro q hq
        let p : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm q
        have hp : p ≠ 0 := by
          intro hp
          apply hq
          simpa [p] using congrArg (EuclideanSpace.equiv (Fin 2) ℝ) hp
        have hpos : 0 < inner ℝ p (matrixAction (W.a x) p) :=
          lt_of_lt_of_le (mul_pos hell (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hp)))
            (hbounds x (hNW hx) p).1
        simpa [p, matrixAction, EuclideanSpace.inner_eq_star_dotProduct,
          Matrix.vecHead, Matrix.vecTail, mul_comm] using hpos
    exact hM.det_pos
  have hhpos (x : E2) (hx : x ∈ H) : 0 < N.h x := by
    have h := N.h_lower_bound x (hNR hx)
    linarith
  have hh : ContDiffOn ℝ ∞ N.h H := N.h_smooth_near_base.mono N.N_contains
  have hlead (i j : Fin 2) : ContDiffOn ℝ ∞ (fun x => N.leading x i j) H := by
    exact hh.mul ((ha i j).mono (hNW.trans hWO))
  have hleadpos (x : E2) (hx : x ∈ H) : 0 < Matrix.det (N.leading x) := by
    change 0 < Matrix.det (N.h x • W.a x)
    rw [Matrix.det_smul]
    change 0 < N.h x ^ 2 * Matrix.det (W.a x)
    exact mul_pos (sq_pos_of_pos (hhpos x hx)) (hapos x hx)
  have hdetsmooth : ContDiffOn ℝ ∞ (fun x => Matrix.det (N.leading x)) H := by
    simp only [Matrix.det_fin_two]
    exact ((hlead 0 0).mul (hlead 1 1)).sub ((hlead 0 1).mul (hlead 1 0))
  have hfactor : ContDiffOn ℝ ∞ N.factor H := by
    exact (hdetsmooth.sqrt (fun x hx => (hleadpos x hx).ne')).inv
      (fun x hx => (Real.sqrt_pos.2 (hleadpos x hx)).ne')
  have hfpos (x : E2) (hx : x ∈ H) : 0 < N.factor x :=
    inv_pos.mpr (Real.sqrt_pos.2 (hleadpos x hx))
  have hnormsmooth (i j : Fin 2) : ContDiffOn ℝ ∞ (fun x => N.normalizedA x i j) H :=
    hfactor.mul (hlead i j)
  let t : E2 → ℝ := fun x => N.factor x * N.h x
  have ht : ContinuousOn t H := (hfactor.mul hh).continuousOn
  have htpos (x : E2) (hx : x ∈ H) : 0 < t x := mul_pos (hfpos x hx) (hhpos x hx)
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hnonempty ht
  obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hnonempty ht
  have hquad (x p : E2) :
      inner ℝ p (matrixAction (N.normalizedA x) p) = t x * inner ℝ p (matrixAction (W.a x) p) := by
    have hact : matrixAction (N.normalizedA x) p = t x • matrixAction (W.a x) p := by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
      funext i
      delta matrixAction PositiveNormalization.normalizedA PositiveNormalization.leading
      simp only [Matrix.smul_apply, smul_eq_mul,
        Fin.sum_univ_two, map_smul, ContinuousLinearEquiv.apply_symm_apply, Pi.smul_apply, t]
      ring
    rw [hact, inner_smul_right]
  have hnSym : SymmetricOn N.normalizedA H := by
    intro x hx i j
    change N.factor x * (N.h x * W.a x i j) = N.factor x * (N.h x * W.a x j i)
    rw [hsym x (hNW hx) i j]
  have hnEll : UniformEllipticOn N.normalizedA H := by
    refine ⟨t xmin * ell, t xmax * C, mul_pos (htpos xmin hxmin) hell,
      mul_pos (htpos xmax hxmax) hC, ?_⟩
    intro x hx p
    rw [hquad]
    constructor
    · calc
        t xmin * ell * ‖p‖ ^ 2 = t xmin * (ell * ‖p‖ ^ 2) := by ring
        _ ≤ t x * (ell * ‖p‖ ^ 2) := mul_le_mul_of_nonneg_right (hmin hx) (by positivity)
        _ ≤ t x * inner ℝ p (matrixAction (W.a x) p) :=
          mul_le_mul_of_nonneg_left (hbounds x (hNW hx) p).1 (htpos x hx).le
    · calc
        t x * inner ℝ p (matrixAction (W.a x) p) ≤ t x * (C * ‖p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hbounds x (hNW hx) p).2 (htpos x hx).le
        _ ≤ t xmax * (C * ‖p‖ ^ 2) := mul_le_mul_of_nonneg_right (hmax hx) (by positivity)
        _ = t xmax * C * ‖p‖ ^ 2 := by ring
  have hnLip : ∀ i j, LipschitzBoundOn (fun x => N.normalizedA x i j) H := by
    intro i j
    obtain ⟨L, hL⟩ := (hnormsmooth i j).exists_lipschitzOnWith (by simp) hconvex hcompact
    exact ⟨L, L.coe_nonneg, fun x hx y hy => hL.dist_le_mul x hx y hy⟩
  have hnDet : ∀ x ∈ H, Matrix.det (N.normalizedA x) = 1 := by
    intro x hx
    change Matrix.det (N.factor x • N.leading x) = 1
    rw [Matrix.det_smul]
    change ((Real.sqrt (Matrix.det (N.leading x)))⁻¹) ^ 2 * Matrix.det (N.leading x) = 1
    rw [inv_pow, Real.sq_sqrt (hleadpos x hx).le]
    exact inv_mul_cancel₀ (hleadpos x hx).ne'
  have hhAt (x : E2) (hx : x ∈ H) : ContDiffAt ℝ ∞ N.h x :=
    (N.h_smooth_near_base x (N.N_contains hx)).contDiffAt
      (N.N_open.mem_nhds (N.N_contains hx))
  have haAt (i j : Fin 2) (x : E2) (hx : x ∈ H) :
      ContDiffAt ℝ ∞ (fun y => W.a y i j) x :=
    (ha i j x (hWO (hNW hx))).contDiffAt (hO.mem_nhds (hWO (hNW hx)))
  have hleadAt (i j : Fin 2) (x : E2) (hx : x ∈ H) :
      ContDiffAt ℝ ∞ (fun y => N.leading y i j) x :=
    (hhAt x hx).mul (haAt i j x hx)
  have hfactorAt (x : E2) (hx : x ∈ H) : ContDiffAt ℝ ∞ N.factor x := by
    have hd : ContDiffAt ℝ ∞ (fun y => Matrix.det (N.leading y)) x := by
      simp only [Matrix.det_fin_two]
      exact ((hleadAt 0 0 x hx).mul (hleadAt 1 1 x hx)).sub
        ((hleadAt 0 1 x hx).mul (hleadAt 1 0 x hx))
    exact (hd.sqrt (hleadpos x hx).ne').inv (Real.sqrt_pos.2 (hleadpos x hx)).ne'
  have hgradient (f : E2 → ℝ) (x : E2) (hf : ContDiffAt ℝ ∞ f x) :
      ContDiffAt ℝ ∞ (planarGradient f) x := by
    delta planarGradient
    apply ContDiffAt.sum
    intro i hi
    exact ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).smul contDiffAt_const
  have haction (a : E2 → Mat2) (p : E2 → E2) (x : E2)
      (ha : ∀ i j, ContDiffAt ℝ ∞ (fun y => a y i j) x)
      (hp : ContDiffAt ℝ ∞ p x) : ContDiffAt ℝ ∞ (fun y => matrixAction (a y) (p y)) x := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contDiffAt.comp
    apply contDiffAt_pi.mpr
    intro i
    apply ContDiffAt.sum
    intro j hj
    exact (ha i j).mul ((EuclideanSpace.proj (𝕜 := ℝ) (j : Fin 2)).contDiff.contDiffAt.comp x hp)
  have hdriftAt (x : E2) (hx : x ∈ H) : ContDiffAt ℝ ∞ N.drift x := by
    exact (haction W.a (planarGradient N.h) x (fun i j => haAt i j x hx)
      (hgradient N.h x (hhAt x hx))).add
      ((hhAt x hx).smul ((hb x (hWO (hNW hx))).contDiffAt (hO.mem_nhds (hWO (hNW hx)))))
  have hnormb : ContDiffOn ℝ ∞ N.normalizedB H := by
    intro x hx
    exact (((hfactorAt x hx).smul (hdriftAt x hx)).sub
      (haction N.leading (planarGradient N.factor) x (fun i j => hleadAt i j x hx)
        (hgradient N.factor x (hfactorAt x hx)))).contDiffWithinAt
  have hsmooth : SmoothEllipticOn N.normalizedA N.normalizedB (fun _ => 0) H :=
    ⟨hnormsmooth, hnormb, contDiffOn_const, hnSym, hnEll⟩
  obtain ⟨Cb,hCb⟩ := hcompact.exists_bound_of_continuousOn hnormb.continuousOn
  have hbb : BoundedOn N.normalizedB H :=
    ⟨max Cb 0, le_max_right _ _, fun x hx => (hCb x hx).trans (le_max_left _ _)⟩
  refine ⟨hsmooth, hnLip, hbb, hnDet, ?_, hfactorAt⟩
  intro x hx
  change D.f (localCircle D s (x 0)) (x 1) / N.h x = 0
  rw [hx.2, D.f_boundary_zero, zero_div]

theorem same_difference_positive_normalization (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) (N : PositiveNormalization W) :
    WeakLinearEquationOn (halfDisc (N.R / 2)) N.leading N.drift (fun _ => 0)
      N.v (planarGradient N.v) ∧
    WeakLinearEquationOn (halfDisc (N.R / 2)) N.normalizedA N.normalizedB (fun _ => 0)
      N.v (planarGradient N.v) ∧
    SmoothEllipticOn N.normalizedA N.normalizedB (fun _ => 0) (closedHalfDisc (N.R / 2)) ∧
    (∀ i j, LipschitzBoundOn (fun x => N.normalizedA x i j) (closedHalfDisc (N.R / 2))) ∧
    BoundedOn N.normalizedB (closedHalfDisc (N.R / 2)) ∧
    (∀ x ∈ closedHalfDisc (N.R / 2), Matrix.det (N.normalizedA x) = 1) ∧
    (∀ x ∈ flatArc (N.R / 2), N.v x = 0) := by
  have quotient_regular : ∀ x ∈ closedHalfDisc (N.R / 2), ContDiffAt ℝ ∞ N.v x := by
    have hsub : closedHalfDisc (N.R / 2) ⊆ closedHalfDisc N.R := by
      intro x hx
      exact ⟨(Metric.closedBall_subset_closedBall (by linarith [N.R_pos])) hx.1, hx.2⟩
    have hsubW : closedHalfDisc (N.R / 2) ⊆ closedHalfDisc W.R := by
      intro x hx
      exact ⟨(Metric.closedBall_subset_closedBall (by linarith [N.R_pos, N.R_inside])) hx.1, hx.2⟩
    have hregular : ∀ x ∈ closedHalfDisc (N.R / 2), ContDiffAt ℝ ∞ N.v x := by
      intro x hx
      have hh : N.h x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (N.h_lower_bound x (hsub hx)))
      change ContDiffAt ℝ ∞ (fun y => localHeight D s y / N.h y) x
      exact ((W.height_smooth x (W.U_contains (hsubW hx))).contDiffAt
        (W.U_open.mem_nhds (W.U_contains (hsubW hx)))).div
        ((N.h_smooth_near_base x (N.N_contains hx)).contDiffAt
          (N.N_open.mem_nhds (N.N_contains hx))) hh
    exact hregular
  have smooth_weak_gradient (U : Set E2) (hU : IsOpen U) (u : E2 → ℝ)
      (hu : ∀ x ∈ U, ContDiffAt ℝ ∞ u x) : WeakGradientOn U u (planarGradient u) := by
    have huc : ContinuousOn u U := fun x hx => (hu x hx).continuousAt.continuousWithinAt
    have hdu : ContinuousOn (fderiv ℝ u) U :=
      fun x hx => ((hu x hx).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
    have hgrad : ContinuousOn (planarGradient u) U := by
      unfold planarGradient
      apply continuousOn_finset_sum
      intro i hi
      exact (hdu.clm_apply continuousOn_const).smul continuousOn_const
    refine ⟨huc.locallyIntegrableOn hU.measurableSet, hgrad.locallyIntegrableOn hU.measurableSet, ?_⟩
    intro φ hφ hc hs i
    have integral_product (F ψ : E2 → ℝ) (hF : ContinuousOn F U)
        (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U) :
        Integrable (fun x => F x * ψ x) := by
      apply (integrableOn_iff_integrable_of_support_subset ?_).mp
        (((hF.mono hψs).mul hψ.continuousOn).integrableOn_compact hψc)
      intro x hx
      exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)
    have hi1 : Integrable (fun x => fderiv ℝ u x (coordinateVector 2 i) * φ x) :=
      integral_product _ _ (hdu.clm_apply continuousOn_const) hφ.continuous hc hs
    have hi2 : Integrable (fun x => u x * fderiv ℝ φ x (coordinateVector 2 i)) :=
      integral_product _ _ huc ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs)
    have hi3 : Integrable (fun x => u x * φ x) :=
      integral_product _ _ huc hφ.continuous hc hs
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
      (fun x hx => (hu x (hs hx)).differentiableAt (by simp))
      (fun x _ => hφ.differentiable (by simp) x)
    have hgcoord : ∀ x, planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
      intro x
      fin_cases i <;> simp [planarGradient, coordinateVector, Fin.sum_univ_two]
    simp_rw [hgcoord]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hibp
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
    · intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))]
      simp
  have quotient_weak_gradient :
      WeakGradientOn (halfDisc (N.R / 2)) N.v (planarGradient N.v) := by
    apply smooth_weak_gradient
    · change IsOpen (Metric.ball (0 : E2) (N.R / 2) ∩ {x : E2 | 0 < x 1})
      exact Metric.isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
    · intro x hx
      exact quotient_regular x ⟨Metric.ball_subset_closedBall hx.1, hx.2.le⟩
  have first_flux : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc (N.R / 2) →
      IntegrableOn (fun x => inner ℝ (matrixAction (N.leading x) (planarGradient N.v x))
        (planarGradient φ x) - (inner ℝ (N.drift x) (planarGradient N.v x) +
          (fun _ => 0) x * N.v x) * φ x) (halfDisc (N.R / 2)) ∧
      (∫ x in halfDisc (N.R / 2),
        inner ℝ (matrixAction (N.leading x) (planarGradient N.v x)) (planarGradient φ x) -
          (inner ℝ (N.drift x) (planarGradient N.v x) + (fun _ => 0) x * N.v x) * φ x) = 0 := by
    intro φ hφ hcompact hs
    classical
    let U := halfDisc (N.R / 2)
    let f := localHeight D s
    let Xf : E2 → E2 := fun x => matrixAction (W.a x) (planarGradient f x)
    let Xh : E2 → E2 := fun x => matrixAction (W.a x) (planarGradient N.h x)
    let X : E2 → E2 := fun x => matrixAction (N.leading x) (planarGradient N.v x)
    have hU : IsOpen U := Metric.isOpen_ball.inter
      (isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
    have hclosed (x : E2) (hx : x ∈ U) : x ∈ closedHalfDisc (N.R / 2) :=
      ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
    have hCW (x : E2) (hx : x ∈ U) : x ∈ closedHalfDisc W.R :=
      ⟨Metric.closedBall_subset_closedBall (by linarith [N.R_pos,N.R_inside])
        (Metric.ball_subset_closedBall hx.1),hx.2.le⟩
    have hCN (x : E2) (hx : x ∈ U) : x ∈ halfDisc N.R :=
      ⟨Metric.ball_subset_ball (by linarith [N.R_pos]) hx.1,hx.2⟩
    obtain ⟨O,hO,hWO,hOU,hjets,hfs,hfg,has,hqs,hlgs,hlhs,hbs,hcs⟩ :=
      actual_coefficient_open_tube D s W
    have hfAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ f x :=
      (hfs x (hWO (hCW x hx))).contDiffAt (hO.mem_nhds (hWO (hCW x hx)))
    have hhAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ N.h x :=
      (N.h_smooth_near_base x (N.N_contains (hclosed x hx))).contDiffAt
        (N.N_open.mem_nhds (N.N_contains (hclosed x hx)))
    have hvAt (x : E2) (hx : x ∈ U) := quotient_regular x (hclosed x hx)
    have haAt (x : E2) (hx : x ∈ U) (i j : Fin 2) :
        ContDiffAt ℝ ∞ (fun y => W.a y i j) x :=
      (has i j x (hWO (hCW x hx))).contDiffAt (hO.mem_nhds (hWO (hCW x hx)))
    have hgradAt (v : E2 → ℝ) (x : E2) (hv : ContDiffAt ℝ ∞ v x) :
        ContDiffAt ℝ ∞ (planarGradient v) x := by
      delta planarGradient
      apply ContDiffAt.sum
      intro i hi
      exact ((hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).smul contDiffAt_const
    have hactionAt (v : E2 → E2) (x : E2) (hx : x ∈ U)
        (hv : ContDiffAt ℝ ∞ v x) : ContDiffAt ℝ ∞ (fun y => matrixAction (W.a y) (v y)) x := by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contDiffAt.comp
      apply contDiffAt_pi.mpr
      intro i
      apply ContDiffAt.sum
      intro j hj
      exact (haAt x hx i j).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) (j : Fin 2)).contDiff.contDiffAt.comp x hv)
    have hXfAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ Xf x :=
      hactionAt _ x hx (hgradAt f x (hfAt x hx))
    have hXhAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ Xh x :=
      hactionAt _ x hx (hgradAt N.h x (hhAt x hx))
    have hhne (x : E2) (hx : x ∈ U) : N.h x ≠ 0 := by
      have h := N.h_lower_bound x ⟨Metric.ball_subset_closedBall (hCN x hx).1,hx.2.le⟩
      linarith
    have hqgrad (x : E2) (hx : x ∈ U) :
        N.h x • planarGradient N.v x = planarGradient f x - N.v x • planarGradient N.h x := by
      have hf := (hfAt x hx).differentiableAt (by simp)
      have hh := (hhAt x hx).differentiableAt (by simp)
      have hinv := (hasDerivAt_inv (hhne x hx)).comp_hasFDerivAt x hh.hasFDerivAt
      have hfd := hf.hasFDerivAt.mul hinv
      delta PositiveNormalization.v planarGradient
      simp only [div_eq_mul_inv]
      dsimp only [Pi.mul_def,Function.comp_def] at hfd
      rw [hfd.fderiv]
      simp only [add_apply,smul_apply,smul_eq_mul]
      rw [Finset.smul_sum,Finset.smul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [smul_smul]
      rw [← sub_smul]
      congr 1
      dsimp only [f]
      field_simp [hhne x hx]
      ring
    have hXeq (x : E2) (hx : x ∈ U) : X x = Xf x - N.v x • Xh x := by
      have hg := hqgrad x hx
      have hma : matrixAction (N.leading x) (planarGradient N.v x) =
          matrixAction (W.a x) (N.h x • planarGradient N.v x) := by
        ext i
        change (∑ j, (N.h x * W.a x i j) * planarGradient N.v x j) =
          ∑ j, W.a x i j * (N.h x * planarGradient N.v x j)
        apply Finset.sum_congr rfl
        intro j hj
        ring
      dsimp only [X,Xf,Xh]
      rw [hma,hg]
      ext i
      change (∑ j, W.a x i j * (planarGradient f x j - N.v x * planarGradient N.h x j)) =
        (∑ j, W.a x i j * planarGradient f x j) - N.v x * ∑ j, W.a x i j * planarGradient N.h x j
      simp only [Fin.sum_univ_two]
      ring
    have hXAt (x : E2) (hx : x ∈ U) : ContDiffAt ℝ ∞ X x := by
      apply ((hXfAt x hx).sub ((hvAt x hx).smul (hXhAt x hx))).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hXeq y hy
    have hgcoord (v : E2 → ℝ) (x : E2) (i : Fin 2) :
        planarGradient v x i = fderiv ℝ v x (coordinateVector 2 i) := by
      fin_cases i <;> simp [planarGradient,coordinateVector,Fin.sum_univ_two]
    have hclassical (x : E2) (hx : x ∈ U) :
        (∑ i : Fin 2, fderiv ℝ (fun y => X y i) x (coordinateVector 2 i)) +
          inner ℝ (N.drift x) (planarGradient N.v x) = 0 := by
      have hdx (i : Fin 2) : fderiv ℝ (fun y => X y i) x =
          fderiv ℝ (fun y => Xf y i) x -
            (N.v x • fderiv ℝ (fun y => Xh y i) x + Xh x i • fderiv ℝ N.v x) := by
        have hevent : (fun y => X y i) =ᶠ[nhds x]
            (fun y => Xf y i - N.v y * Xh y i) := by
          filter_upwards [hU.mem_nhds hx] with y hy
          exact congrArg (fun v : E2 => v i) (hXeq y hy)
        rw [hevent.fderiv_eq]
        exact (((EuclideanSpace.proj (𝕜 := ℝ) (i : Fin 2)).differentiableAt.comp x
          ((hXfAt x hx).differentiableAt (by simp))).hasFDerivAt.sub
          (((hvAt x hx).differentiableAt (by simp)).hasFDerivAt.mul
            (((EuclideanSpace.proj (𝕜 := ℝ) (i : Fin 2)).differentiableAt.comp x
              ((hXhAt x hx).differentiableAt (by simp))).hasFDerivAt))).fderiv
      have hf := (actual_difference_equation D s W).2 x (hCW x hx)
      have hh := N.h_classical x (hCN x hx)
      have hvh : f x = N.v x * N.h x := by
        change f x = (f x / N.h x) * N.h x
        rw [div_mul_cancel₀ _ (hhne x hx)]
      have hg0 := congrArg (fun v : E2 => v 0) (hqgrad x hx)
      have hg1 := congrArg (fun v : E2 => v 1) (hqgrad x hx)
      simp only [PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul] at hg0 hg1
      simp only [Fin.sum_univ_two,hdx,sub_apply,add_apply,smul_apply,smul_eq_mul]
      simp only [classicalL,Fin.sum_univ_two] at hf hh
      change fderiv ℝ (fun y => Xf y 0) x (coordinateVector 2 0) +
        fderiv ℝ (fun y => Xf y 1) x (coordinateVector 2 1) +
        inner ℝ (W.b x) (planarGradient f x) + W.c x * f x = 0 at hf
      change fderiv ℝ (fun y => Xh y 0) x (coordinateVector 2 0) +
        fderiv ℝ (fun y => Xh y 1) x (coordinateVector 2 1) +
        inner ℝ (W.b x) (planarGradient N.h x) + W.c x * N.h x = 0 at hh
      simp only [PositiveNormalization.drift]
      change _ + inner ℝ (Xh x + N.h x • W.b x) (planarGradient N.v x) = 0
      simp only [EuclideanSpace.inner_eq_star_dotProduct,Fin.sum_univ_two,
        dotProduct,star_trivial,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hf hh ⊢
      simp only [← hgcoord] at hf hh ⊢
      rw [hvh] at hf
      linear_combination hf - N.v x * hh + W.b x 0 * hg0 + W.b x 1 * hg1
    have hcX : ContinuousOn X U := fun x hx => (hXAt x hx).continuousAt.continuousWithinAt
    have hcDX (i : Fin 2) : ContinuousOn (fderiv ℝ (fun y => X y i)) U := by
      intro x hx
      exact ((((EuclideanSpace.proj (𝕜 := ℝ) (i : Fin 2)).contDiff.contDiffAt.comp x
        (hXAt x hx)).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt)
    have hch : ContinuousOn N.h U := fun x hx => (hhAt x hx).continuousAt.continuousWithinAt
    have hcb : ContinuousOn N.drift U :=
      (show ContinuousOn Xh U from fun x hx => (hXhAt x hx).continuousAt.continuousWithinAt).add
        (hch.smul (hbs.continuousOn.mono (fun x hx => hWO (hCW x hx))))
    have hcg : ContinuousOn (planarGradient N.v) U :=
      fun x hx => (hgradAt N.v x (hvAt x hx)).continuousAt.continuousWithinAt
    have product_integrable (F ψ : E2 → ℝ) (hF : ContinuousOn F U)
        (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ U) :
        Integrable (fun x => F x * ψ x) := by
      apply (integrableOn_iff_integrable_of_support_subset ?_).mp
        (((hF.mono hsψ).mul hψ.continuousOn).integrableOn_compact hcψ)
      intro x hx
      exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)
    have hiDX (i : Fin 2) : IntegrableOn (fun x =>
        fderiv ℝ (fun y => X y i) x (coordinateVector 2 i) * φ x) U :=
      (product_integrable _ _ ((hcDX i).clm_apply continuousOn_const) hφ.continuous hcompact hs).integrableOn
    have hiX (i : Fin 2) : IntegrableOn (fun x =>
        X x i * fderiv ℝ φ x (coordinateVector 2 i)) U :=
      (product_integrable _ _ ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hcX)
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hcompact.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs)).integrableOn
    have hiL : IntegrableOn (fun x => inner ℝ (N.drift x) (planarGradient N.v x) * φ x) U :=
      (product_integrable _ _ (hcb.inner hcg) hφ.continuous hcompact hs).integrableOn
    have hIBP (i : Fin 2) : (∫ x in U, X x i * fderiv ℝ φ x (coordinateVector 2 i)) =
        -(∫ x in U, fderiv ℝ (fun y => X y i) x (coordinateVector 2 i) * φ x) := by
      have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := coordinateVector 2 i)
        (product_integrable _ _ ((hcDX i).clm_apply continuousOn_const) hφ.continuous hcompact hs)
        (product_integrable _ _ ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hcX)
          ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
          (hcompact.fderiv_apply ℝ (coordinateVector 2 i)) ((tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans hs))
        (product_integrable _ _ ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hcX)
          hφ.continuous hcompact hs)
        (fun x hx => (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x
          ((hXAt x (hs hx)).differentiableAt (by simp)))
        (fun x _ => hφ.differentiable (by simp) x)
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
        setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact hibp
      · intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)),mul_zero]
      · intro x hx
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))]
        simp
    have hinner (x : E2) : inner ℝ (X x) (planarGradient φ x) =
        ∑ i : Fin 2, X x i * fderiv ℝ φ x (coordinateVector 2 i) := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct,Fin.sum_univ_two,dotProduct,star_trivial]
      rw [← hgcoord φ x 0,← hgcoord φ x 1]
      ring
    change IntegrableOn (fun x => inner ℝ (X x) (planarGradient φ x) -
      (inner ℝ (N.drift x) (planarGradient N.v x) + 0 * N.v x) * φ x) U ∧ _
    simp only [zero_mul,add_zero,hinner]
    refine ⟨(integrable_finset_sum _ (fun i hi => hiX i)).sub hiL,?_⟩
    change (∫ x in U, inner ℝ (X x) (planarGradient φ x) -
      inner ℝ (N.drift x) (planarGradient N.v x) * φ x) = 0
    simp_rw [hinner]
    rw [integral_sub (integrable_finset_sum _ (fun i hi => hiX i)) hiL,
      integral_finset_sum _ (fun i hi => hiX i)]
    simp_rw [hIBP]
    rw [Finset.sum_neg_distrib,← integral_finset_sum _ (fun i hi => hiDX i),
      sub_eq_add_neg,← neg_add,← integral_add (integrable_finset_sum _ (fun i hi => hiDX i)) hiL]
    have hzero : (∫ x in U, (∑ i : Fin 2,
        fderiv ℝ (fun y => X y i) x (coordinateVector 2 i) * φ x) +
          inner ℝ (N.drift x) (planarGradient N.v x) * φ x) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      rw [← Finset.sum_mul,← add_mul,hclassical x hx,zero_mul]
      rfl
    rw [hzero,neg_zero]
  obtain ⟨hell,hlip,hb,hdet,htrace,hfactorAt⟩ := normalized_coefficients_v468 D s W N
  have normalized_flux : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc (N.R / 2) →
      IntegrableOn (fun x => inner ℝ (matrixAction (N.normalizedA x) (planarGradient N.v x))
        (planarGradient φ x) - (inner ℝ (N.normalizedB x) (planarGradient N.v x) +
          (fun _ => 0) x * N.v x) * φ x) (halfDisc (N.R / 2)) ∧
      (∫ x in halfDisc (N.R / 2),
        inner ℝ (matrixAction (N.normalizedA x) (planarGradient N.v x)) (planarGradient φ x) -
          (inner ℝ (N.normalizedB x) (planarGradient N.v x) + (fun _ => 0) x * N.v x) * φ x) = 0 := by
    intro φ hφ hcompact hs
    classical
    let ψ : E2 → ℝ := fun x => N.factor x * φ x
    have hclosed (x : E2) (hx : x ∈ halfDisc (N.R / 2)) : x ∈ closedHalfDisc (N.R / 2) :=
      ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
    have hψ : ContDiff ℝ ∞ ψ := by
      apply contDiff_iff_contDiffAt.mpr
      intro x
      by_cases hx : x ∈ tsupport φ
      · exact (hfactorAt x (hclosed x (hs hx))).mul hφ.contDiffAt
      · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
        change N.factor y * φ y = 0
        rw [image_eq_zero_of_notMem_tsupport hy,mul_zero]
    have hcψ : HasCompactSupport ψ := hcompact.mul_left
    have hsψ : tsupport ψ ⊆ halfDisc (N.R / 2) := tsupport_mul_subset_right.trans hs
    obtain ⟨hi,hint⟩ := first_flux ψ hψ hcψ hsψ
    have hgrad (x : E2) (hx : x ∈ halfDisc (N.R / 2)) :
        planarGradient ψ x = φ x • planarGradient N.factor x + N.factor x • planarGradient φ x := by
      have hd := ((hfactorAt x (hclosed x hx)).differentiableAt (by simp)).hasFDerivAt.mul
        (hφ.differentiable (by simp) x).hasFDerivAt
      change HasFDerivAt ψ (N.factor x • fderiv ℝ φ x + φ x • fderiv ℝ N.factor x) x at hd
      delta planarGradient
      rw [hd.fderiv]
      ext i
      fin_cases i <;> simp [ψ,coordinateVector,Fin.sum_univ_two] <;> ring
    obtain ⟨hformula,hsym,hbounds⟩ := actual_slope_hessian_uniform_bounds D s W
    have hequal : EqOn
        (fun x => inner ℝ (matrixAction (N.normalizedA x) (planarGradient N.v x))
          (planarGradient φ x) - (inner ℝ (N.normalizedB x) (planarGradient N.v x) +
            (0 : ℝ) * N.v x) * φ x)
        (fun x => inner ℝ (matrixAction (N.leading x) (planarGradient N.v x))
          (planarGradient ψ x) - (inner ℝ (N.drift x) (planarGradient N.v x) +
            (0 : ℝ) * N.v x) * ψ x) (halfDisc (N.R / 2)) := by
      intro x hx
      have hxW : x ∈ closedHalfDisc W.R :=
        ⟨Metric.closedBall_subset_closedBall (by linarith [N.R_pos,N.R_inside])
          (Metric.ball_subset_closedBall hx.1),hx.2.le⟩
      have hsymx := hsym x hxW (0 : Fin 2) (1 : Fin 2)
      dsimp only
      rw [hgrad x hx]
      dsimp only [PositiveNormalization.normalizedA, PositiveNormalization.normalizedB,
        PositiveNormalization.leading,ψ]
      simp [matrixAction,EuclideanSpace.inner_eq_star_dotProduct,Fin.sum_univ_two,
        Matrix.smul_apply,hsymx]
      <;> ring
    refine ⟨hi.congr ((ae_restrict_mem ?_).mono (fun x hx => (hequal hx).symm)),?_⟩
    · change MeasurableSet (Metric.ball (0 : E2) (N.R / 2) ∩ {x : E2 | 0 < x 1})
      exact Metric.isOpen_ball.measurableSet.inter
        (isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous).measurableSet
    · rw [setIntegral_congr_fun ?_ hequal]
      · exact hint
      · change MeasurableSet (Metric.ball (0 : E2) (N.R / 2) ∩ {x : E2 | 0 < x 1})
        exact Metric.isOpen_ball.measurableSet.inter
          (isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous).measurableSet
  exact ⟨⟨quotient_weak_gradient, first_flux⟩, ⟨quotient_weak_gradient, normalized_flux⟩,
    hell,hlip,hb,hdet,htrace⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
