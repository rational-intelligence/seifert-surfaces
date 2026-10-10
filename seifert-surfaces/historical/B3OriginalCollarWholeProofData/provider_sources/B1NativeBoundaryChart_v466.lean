import B1BoundaryMetricProvider_v466
import B1GraphCoefficients
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
private theorem native_inverse_metric_data_v466 (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) (N : PositiveNormalization W) :
    Nonempty (InverseMetricData (N.R / 2) N.normalizedA) := by
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
  exact inverse_det_one_metric_data (N.R / 2) (half_pos N.R_pos) N.normalizedA
    hnSym hnEll hnLip hnDet

/-- The protected native chart consumer for the same supplied D/s/W/N. -/
theorem inverse_metric_boundary_isothermal_coordinates (D : B1OriginalData g J)
    (s : Circle) (W : CollarWindow D s) (N : PositiveNormalization W) :
    Nonempty (BoundaryIsothermalPatch N) := by
  obtain ⟨G⟩ := native_inverse_metric_data_v466 D s W N
  obtain ⟨Ω⟩ := smooth_flat_jordan_domain (N.R / 2) (half_pos N.R_pos)
  obtain ⟨P⟩ := boundary_metric_conformal_provider (N.R / 2) N.normalizedA G Ω
  obtain ⟨X⟩ := metric_parametrization_ambient_extensions P
  obtain ⟨F, hF⟩ := native_boundary_patch_from_metric_provider D s W N G Ω P X
  exact ⟨F⟩
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.inverse_metric_boundary_isothermal_coordinates
