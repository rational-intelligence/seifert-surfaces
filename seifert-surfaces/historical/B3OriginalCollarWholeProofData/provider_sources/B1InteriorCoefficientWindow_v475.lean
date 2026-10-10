import B1HalfDiscEllipticExtension_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Internal coefficient data on a compact artificial half-disc.  No geometric
source data or surface minimality premise enters this analytic record. -/
structure InteriorCoefficientWindow_v475 where
  R : ℝ
  R_pos : 0 < R
  O : Set E2
  isOpen_O : IsOpen O
  closed_subset : closedHalfDisc R ⊆ O
  a : E2 → Mat2
  b : E2 → E2
  c : E2 → ℝ
  smooth_a : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O
  smooth_b : ContDiffOn ℝ ∞ b O
  smooth_c : ContDiffOn ℝ ∞ c O
  symmetric : ∀ x ∈ closedHalfDisc R, ∀ i j, a x i j = a x j i
  ell : ℝ
  ell_pos : 0 < ell
  coercive : ∀ x ∈ closedHalfDisc R, ∀ v : E2,
    ell * ‖v‖^2 ≤ inner ℝ v (matrixAction (a x) v)

theorem interior_window_full_form_bounds_v475 (W : InteriorCoefficientWindow_v475) :
    (∀ i j, AEStronglyMeasurable (fun x => W.a x i j) (volume.restrict (halfDisc W.R))) ∧
    AEStronglyMeasurable W.b (volume.restrict (halfDisc W.R)) ∧
    AEStronglyMeasurable W.c (volume.restrict (halfDisc W.R)) ∧
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧
      (∀ x ∈ halfDisc W.R, ∀ v, ‖matrixAction (W.a x) v‖ ≤ A * ‖v‖) ∧
      (∀ x ∈ halfDisc W.R, ‖W.b x‖ ≤ B) ∧
      (∀ x ∈ halfDisc W.R, |W.c x| ≤ C) := by
  let O := W.O
  have hWO := W.closed_subset
  have ha := W.smooth_a
  have hb := W.smooth_b
  have hc := W.smooth_c
  have hcompact : IsCompact (closedHalfDisc W.R) :=
    (isCompact_closedBall (0 : E2) W.R).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hUW : halfDisc W.R ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have hU : MeasurableSet (halfDisc W.R) := by
    change MeasurableSet (Metric.ball (0 : E2) W.R ∩ {x : E2 | 0 < x 1})
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

private theorem interior_planar_inverse_coercivity_v475
    (a : Mat2) (ell A : ℝ) (hell : 0 < ell) (hA : 0 < A)
    (hlo : ∀ p : E2, ell * ‖p‖^2 ≤ inner ℝ p (matrixAction a p))
    (hhi : ∀ p : E2, ‖matrixAction a p‖ ≤ A * ‖p‖) :
    ∀ p : E2, (ell / A^2) * ‖p‖^2 ≤ inner ℝ p (matrixAction a⁻¹ p) := by
  have hz (p : E2) (hp : matrixAction a p = 0) : p = 0 := by
    have h := hlo p
    rw [hp,inner_zero_right] at h
    have hs : ‖p‖^2 ≤ 0 := (mul_le_mul_iff_right₀ hell).mp (by simpa using h)
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg p])
  have hinj : Function.Injective a.mulVec := by
    intro p q hpq
    have h0 : matrixAction a (WithLp.toLp 2 (p-q)) = 0 := by
      ext i
      change (a.mulVec (p-q)) i = 0
      rw [Matrix.mulVec_sub,hpq,sub_self]
      rfl
    have he : p-q = 0 := congrArg WithLp.ofLp (hz _ h0)
    exact sub_eq_zero.mp he
  have hdet : IsUnit a.det := (Matrix.isUnit_iff_isUnit_det a).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hinv (p : E2) : matrixAction a (matrixAction a⁻¹ p) = p := by
    ext i
    change (a.mulVec ((a⁻¹).mulVec p.ofLp)) i = p i
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv a hdet,Matrix.one_mulVec]
  intro p
  let q := matrixAction a⁻¹ p
  have he : matrixAction a q = p := hinv p
  have hl := hlo q
  rw [he,real_inner_comm] at hl
  have hh := hhi q
  rw [he] at hh
  have hs : ‖p‖^2 ≤ A^2*‖q‖^2 := by
    nlinarith [norm_nonneg p,norm_nonneg q]
  apply le_trans _ hl
  rw [div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hA)]
  nlinarith

theorem interior_window_elliptic_coeff_v475
    (W : InteriorCoefficientWindow_v475) :
    ∃ A : DeGiorgi.EllipticCoeff 2 (halfDisc W.R),
      ∀ x ∈ halfDisc W.R, A.a x = W.a x := by
  classical
  let U := halfDisc W.R
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  let O := W.O
  have hO := W.isOpen_O
  have hWO := W.closed_subset
  have ha := W.smooth_a
  have hb := W.smooth_b
  have hc := W.smooth_c
  have hUW : U ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  let ell := W.ell
  have hell := W.ell_pos
  have hsym := W.symmetric
  have hbounds := W.coercive
  obtain ⟨-, -, -, M,B,Z,hM,hB,hZ,hMa,-⟩ := interior_window_full_form_bounds_v475 W
  let a : E2 → Mat2 := fun x => if x ∈ U then W.a x else 1
  let cap := max ell (M^2/ell)
  have hcap : 0 < cap := lt_of_lt_of_le hell (le_max_left _ _)
  have hcap2 : 0 < M^2/ell := div_pos (sq_pos_of_pos hM) hell
  have hinv : cap⁻¹ ≤ ell / M^2 := by
    calc
      cap⁻¹ ≤ (M^2/ell)⁻¹ := (inv_le_inv₀ hcap hcap2).mpr (le_max_right _ _)
      _ = ell / M^2 := by rw [inv_div]
  let A : DeGiorgi.EllipticCoeff 2 U :=
    { a := a
      lam := ell
      Λ := cap
      measurable_comp := by
        intro i j
        have hm : Measurable (U.piecewise (fun x => W.a x i j)
            (fun _ => (1 : Mat2) i j)) :=
          ((ha i j).continuousOn.mono (hUW.trans hWO)).measurable_piecewise
            continuous_const.continuousOn hU.measurableSet
        convert hm using 1
        funext x
        by_cases hx : x ∈ U <;> simp [a,Set.piecewise,hx]
      hlam := hell
      hΛ := le_max_left _ _
      coercive := by
        filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        intro p
        change ell * ‖p‖^2 ≤ inner ℝ p (matrixAction (a x) p)
        simpa only [a,ite_eq_left hx] using hbounds x (hUW hx) p
      coercive_inv := by
        filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        intro p
        change cap⁻¹ * ‖p‖^2 ≤ inner ℝ p (matrixAction ((a x)⁻¹) p)
        rw [show a x = W.a x by simp only [a,ite_eq_left hx]]
        exact (mul_le_mul_of_nonneg_right hinv (sq_nonneg ‖p‖)).trans
          (interior_planar_inverse_coercivity_v475 (W.a x) ell M hell hM
            (fun q => hbounds x (hUW hx) q) (hMa x hx) p) }
  refine ⟨A,?_⟩
  intro x hx
  have hxU : x ∈ U := hx
  change a x = W.a x
  simp only [a,ite_eq_left hxU]

theorem interior_window_smooth_elliptic_extension_v475
    (W : InteriorCoefficientWindow_v475) (P : Set E2) (hP : IsCompact P)
    (hPU : P ⊆ halfDisc W.R) :
    ∃ B : SmoothEllipticBilinearForm 2 univ, ∀ x ∈ P, B.a x = W.a x := by
  classical
  let U := halfDisc W.R
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  let O := W.O
  have hO := W.isOpen_O
  have hWO := W.closed_subset
  have ha := W.smooth_a
  have hb := W.smooth_b
  have hc := W.smooth_c
  have hUW : U ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  let ell := W.ell
  have hell := W.ell_pos
  have hsym := W.symmetric
  have hbounds := W.coercive
  obtain ⟨χ,hχ,hχc,hχone,hχU,hχrange⟩ := DifferentialGeometry.Analysis.exists_bump_compact hP hU hPU
  let a : E2 → Mat2 := fun x => χ x • W.a x + (1-χ x) • (1 : Mat2)
  let lam := min ell 1
  have hlam : 0 < lam := lt_min hell zero_lt_one
  have haSmooth (i j : Fin 2) : ContDiff ℝ ∞ (fun x => a x i j) := by
    change ContDiff ℝ ∞ (fun x => χ x * W.a x i j + (1-χ x) * (1 : Mat2) i j)
    exact (DifferentialGeometry.Analysis.contDiff_cutoff_smul hU hχ hχU
      ((ha i j).mono (hUW.trans hWO))).add ((contDiff_const.sub hχ).mul contDiff_const)
  have hmat (x : E2) (p : E2) :
      matrixAction (a x) p = χ x • matrixAction (W.a x) p + (1-χ x) • p := by
    ext i
    simp only [a,matrixAction,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum,PiLp.add_apply,PiLp.smul_apply]
    simp [Matrix.one_apply]
  let B : SmoothEllipticBilinearForm 2 univ :=
    { a := a
      c := 0
      symm := by
        intro x i j
        by_cases hx : x ∈ U
        · simp only [a,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,hsym x (hUW hx) i j]
          congr 1
          simp [Matrix.one_apply,eq_comm]
        · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hχU hh))
          simp [a,hz,Matrix.one_apply,eq_comm]
      smooth_a := haSmooth
      smooth_c := contDiff_const
      lam := lam
      capLam := lam
      ellipticity_pos := hlam
      ellipticity_le_upper := le_rfl
      coercive := by
        intro x _ p
        change lam * ‖p‖^2 ≤ inner ℝ p (matrixAction (a x) p)
        rw [hmat,inner_add_right,real_inner_smul_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
        have hχx := hχrange (mem_range_self x)
        by_cases hx : x ∈ U
        · have hlo := hbounds x (hUW hx) p
          have hscaled := mul_le_mul_of_nonneg_left hlo hχx.1
          have hellam := mul_le_mul_of_nonneg_right (min_le_left ell 1) (sq_nonneg ‖p‖)
          have h1lam := mul_le_mul_of_nonneg_right (min_le_right ell 1) (sq_nonneg ‖p‖)
          have he0 := mul_le_mul_of_nonneg_left hellam hχx.1
          have he1 := mul_le_mul_of_nonneg_left h1lam (sub_nonneg.mpr hχx.2)
          dsimp only [lam] at *
          nlinarith
        · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hχU hh))
          simpa only [hz,zero_mul,sub_zero,one_mul,zero_add] using
            mul_le_mul_of_nonneg_right (min_le_right ell 1) (sq_nonneg ‖p‖) }
  refine ⟨B,?_⟩
  intro x hx
  have hxχ : χ x = 1 := hχone.self_of_nhdsSet hx
  change a x = W.a x
  simp [a,hxχ]

#print axioms interior_window_full_form_bounds_v475
#print axioms interior_window_elliptic_coeff_v475
#print axioms interior_window_smooth_elliptic_extension_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
