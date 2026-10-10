import QuasilinearLocalization

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearLocalization
open SeifertSurfaces.AppendixACoordinates

private lemma planarGradient_apply (f : E2 → ℝ) (x : E2) (i : Fin 2) :
    planarGradient f x i = fderiv ℝ f x (coordinateVector 2 i) := by
  fin_cases i <;>
    simp [planarGradient, Fin.sum_univ_succ, coordinateVector, EuclideanSpace.single,
      PiLp.single_apply]

private lemma gradient3_apply (f : E3 → ℝ) (y : E3) (i : Fin 3) :
    gradient3 f y i = fderiv ℝ f y (coordinateVector 3 i) := by
  fin_cases i <;>
    simp [gradient3, Fin.sum_univ_succ, coordinateVector, EuclideanSpace.single,
      PiLp.single_apply]

private lemma planar_expand (p : E2) :
    p = p 0 • coordinateVector 2 0 + p 1 • coordinateVector 2 1 := by
  ext i
  fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]

private lemma lifted_inner (p : E2) (s : ℝ) (ξ : E3) :
    inner ℝ (liftedPoint p s) ξ = inner ℝ p (planarPart ξ) + s * ξ 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, liftedPoint, planarPart, real_inner_comm]
  ring

private lemma matrixAction_lift (C : LinearizedCoefficients) (v : E2 → ℝ)
    (D : ℝ) (y ξ : E3) :
    matrixAction (liftMatrix C v D y) ξ =
      liftedPoint (C.a (planarPart y) (planarPart ξ) +
        ξ 2 • (v (planarPart y) • C.c (planarPart y) + C.d (planarPart y)))
        (y 2 * C.b (planarPart y) (planarPart ξ) +
          (D + y 2 * (C.q (planarPart y) * v (planarPart y) + C.f (planarPart y))) * ξ 2) := by
  have ha := congrArg (C.a (planarPart y)) (planar_expand (planarPart ξ))
  have hb := congrArg (C.b (planarPart y)) (planar_expand (planarPart ξ))
  simp only [map_add, map_smul, smul_eq_mul] at ha hb
  ext i
  fin_cases i <;>
    simp only [matrixAction, liftMatrix, liftedPoint, WithLp.ofLp_toLp, PiLp.toLp_apply,
      ha, hb, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  all_goals
    simp [planarPart, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem R3_lift_flux_identity (C : LinearizedCoefficients) (v : E2 → ℝ)
    (G : E2 → E2) (D : ℝ) (y : E3) :
    matrixAction (liftMatrix C v D y) (liftGradient G y) =
      liftedPoint (linearizedFlux C v G (planarPart y))
        (y 2 * C.b (planarPart y) (G (planarPart y)) + D +
          y 2 * (C.q (planarPart y) * v (planarPart y) + C.f (planarPart y))) := by
  have hexp (x : E2) :
      x = x 0 • coordinateVector 2 0 + x 1 • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [coordinateVector, EuclideanSpace.single, PiLp.single_apply]
  have ha := congrArg (C.a (planarPart y)) (hexp (G (planarPart y)))
  have hb := congrArg (C.b (planarPart y)) (hexp (G (planarPart y)))
  simp only [map_add, map_smul, smul_eq_mul] at ha hb
  ext i
  fin_cases i <;>
    simp [matrixAction, liftMatrix, liftGradient, liftedPoint, linearizedFlux,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, ha, hb, smul_eq_mul] <;> ring

theorem R3_lift_classical_gradient
    (B : Set E2) (hB : IsOpen B) (v : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 v B) :
    ∀ y ∈ cylinder B, gradient3 (liftFunction v) y = liftGradient (planarGradient v) y := by
  let P : E3 →L[ℝ] E2 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i => EuclideanSpace.proj (Fin.castSucc i)))
  have hP (z : E3) : P z = planarPart z := by
    ext i
    fin_cases i <;> rfl
  intro y hy
  have hv := (hC1.differentiableOn (by norm_num) (planarPart y) hy.1).differentiableAt
    (hB.mem_nhds hy.1)
  have hpd : HasFDerivAt planarPart P y := by
    rw [← show (P : E3 → E2) = planarPart from funext hP]
    exact P.hasFDerivAt
  have hd : HasFDerivAt (liftFunction v)
      ((fderiv ℝ v (planarPart y)).comp P + EuclideanSpace.proj (2 : Fin 3)) y := by
    convert
      ((hv.hasFDerivAt.comp y hpd).add
        (EuclideanSpace.proj (2 : Fin 3)).hasFDerivAt) using 1
    rfl
  have hbasis0 : P (coordinateVector 3 0) = coordinateVector 2 0 := by
    rw [hP]
    ext i
    fin_cases i <;> simp [planarPart, coordinateVector, EuclideanSpace.single, PiLp.single_apply]
  have hbasis1 : P (coordinateVector 3 1) = coordinateVector 2 1 := by
    rw [hP]
    ext i
    fin_cases i <;> simp [planarPart, coordinateVector, EuclideanSpace.single, PiLp.single_apply]
  have hbasis2 : P (coordinateVector 3 2) = 0 := by
    rw [hP]
    ext i
    fin_cases i <;> simp [planarPart, coordinateVector, EuclideanSpace.single, PiLp.single_apply]
  ext i
  rw [gradient3_apply, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  fin_cases i <;>
    rw [show P (coordinateVector 3 _) = _ from by first | exact hbasis0 | exact hbasis1 | exact hbasis2]
  all_goals
    simp [liftGradient, liftedPoint, planarGradient_apply, coordinateVector,
      EuclideanSpace.single, PiLp.single_apply, EuclideanSpace.coe_proj]

/-- Coercivity of the concrete lift, with fixed `D` independent of `h`. -/
theorem R3_lift_coercive
    (B : Set E2) (C : LinearizedCoefficients) (v : E2 → ℝ)
    (κ M L : ℝ) (hκ : 0 < κ) (hM : 1 ≤ M) (hL : 0 ≤ L)
    (hC : CoefficientBounds B C κ M) (hv : ∀ x ∈ B, |v x| ≤ L) :
    ∀ y ∈ cylinder B, ∀ ξ : E3,
      (κ / 2) * ‖planarPart ξ‖ ^ 2 + (ξ 2) ^ 2 ≤
        inner ℝ (matrixAction (liftMatrix C v (liftD κ M L) y) ξ) ξ := by
  intro y hy ξ
  let x := planarPart y
  let p := planarPart ξ
  let s := ξ 2
  let F := v x • C.c x + C.d x
  let g := C.q x * v x + C.f x
  let H := M * L + 2 * M
  let G := M * L + M
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨ha, hc, hd, hb, hq, hf⟩ := hC.2.2.2 x hy.1
  have hvx := hv x hy.1
  have hF : ‖F‖ ≤ G := by
    calc
      ‖F‖ ≤ ‖v x • C.c x‖ + ‖C.d x‖ := norm_add_le _ _
      _ = |v x| * ‖C.c x‖ + ‖C.d x‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ L * M + M := add_le_add (mul_le_mul hvx hc (norm_nonneg _) hL) hd
      _ = G := by dsimp [G]; ring
  have hg : |g| ≤ G := by
    calc
      |g| ≤ |C.q x * v x| + |C.f x| := abs_add_le _ _
      _ = |C.q x| * |v x| + |C.f x| := by rw [abs_mul]
      _ ≤ M * L + M := add_le_add (mul_le_mul hq hvx (abs_nonneg _) hM0) hf
  have hbG : |C.b x p| ≤ M * ‖p‖ := by
    exact (C.b x).le_opNorm p |>.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hiF : |inner ℝ F p| ≤ G * ‖p‖ :=
    (abs_real_inner_le_norm F p).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg _))
  have ht : |y 2| ≤ 1 := hy.2.le
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have hcros : |inner ℝ F p + y 2 * C.b x p| ≤ H * ‖p‖ := by
    calc
      |inner ℝ F p + y 2 * C.b x p| ≤ |inner ℝ F p| + |y 2 * C.b x p| := abs_add_le _ _
      _ ≤ G * ‖p‖ + M * ‖p‖ := add_le_add hiF (by
        rw [abs_mul]
        exact (mul_le_mul ht hbG (abs_nonneg _) (by positivity)).trans_eq (one_mul _))
      _ = H * ‖p‖ := by dsimp [G, H]; ring
  have hcross : -(H * ‖p‖ * |s|) ≤
      s * (inner ℝ F p + y 2 * C.b x p) := by
    have := abs_mul s (inner ℝ F p + y 2 * C.b x p)
    have hl := mul_le_mul_of_nonneg_left hcros (abs_nonneg s)
    have hn := neg_abs_le (s * (inner ℝ F p + y 2 * C.b x p))
    rw [this] at hn
    nlinarith
  have htg : -G ≤ y 2 * g := by
    have hab : |y 2 * g| ≤ G := by
      rw [abs_mul]
      exact (mul_le_mul ht hg (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
    exact (abs_le.mp hab).1
  have hquad : -G * s ^ 2 ≤ y 2 * g * s ^ 2 :=
    mul_le_mul_of_nonneg_right htg (sq_nonneg s)
  have hcoef := hC.2.2.1 x hy.1 p
  have hdiv : (H ^ 2 / (2 * κ)) * (2 * κ) = H ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  have habssq : |s| ^ 2 = s ^ 2 := sq_abs s
  have hyoung : H * ‖p‖ * |s| ≤ (κ / 2) * ‖p‖ ^ 2 +
      (H ^ 2 / (2 * κ)) * s ^ 2 := by
    have hsq := sq_nonneg (κ * ‖p‖ - H * |s|)
    have hdprod := congrArg (fun a : ℝ => a * s ^ 2) hdiv
    nlinarith
  rw [matrixAction_lift, lifted_inner, inner_add_left, real_inner_smul_left]
  change (κ / 2) * ‖p‖ ^ 2 + s ^ 2 ≤
    inner ℝ (C.a x p) p + s * inner ℝ F p +
      (y 2 * C.b x p + (liftD κ M L + y 2 * g) * s) * s
  dsimp [liftD]
  change (κ / 2) * ‖p‖ ^ 2 + s ^ 2 ≤
    inner ℝ (C.a x p) p + s * inner ℝ F p +
      (y 2 * C.b x p + (G + H ^ 2 / (2 * κ) + 1 + y 2 * g) * s) * s
  nlinarith

theorem R3_lift_entries_bounded
    (B : Set E2) (C : LinearizedCoefficients) (v : E2 → ℝ)
    (κ M L : ℝ) (hκ : 0 < κ) (hM : 1 ≤ M) (hL : 0 ≤ L)
    (hC : CoefficientBounds B C κ M) (hv : ∀ x ∈ B, |v x| ≤ L) :
    0 ≤ liftEntryBound κ M L ∧ ∀ y ∈ cylinder B, ∀ i j : Fin 3,
      |liftMatrix C v (liftD κ M L) y i j| ≤ liftEntryBound κ M L := by
  have hM0 : 0 ≤ M := by linarith
  have hD0 : 0 ≤ liftD κ M L := by unfold liftD; positivity
  have hE0 : 0 ≤ liftEntryBound κ M L := by unfold liftEntryBound; positivity
  refine ⟨hE0, ?_⟩
  intro y hy i j
  let x := planarPart y
  have hx : x ∈ B := hy.1
  obtain ⟨ha, hc, hd, hb, hq, hf⟩ := hC.2.2.2 x hx
  have hvx := hv x hx
  have hbasis (k : Fin 2) : ‖coordinateVector 2 k‖ = 1 := by
    simp [coordinateVector, EuclideanSpace.norm_single]
  have hentryA (k l : Fin 2) : |C.a x (coordinateVector 2 k) l| ≤ M := by
    calc
      |C.a x (coordinateVector 2 k) l| ≤ ‖C.a x (coordinateVector 2 k)‖ :=
        by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (C.a x (coordinateVector 2 k)) l
      _ ≤ ‖C.a x‖ * ‖coordinateVector 2 k‖ := (C.a x).le_opNorm _
      _ ≤ M := by simpa [hbasis] using ha
  have hentryF (l : Fin 2) : |(v x • C.c x + C.d x) l| ≤ M * L + M := by
    calc
      |(v x • C.c x + C.d x) l| ≤ ‖v x • C.c x + C.d x‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (v x • C.c x + C.d x) l
      _ ≤ ‖v x • C.c x‖ + ‖C.d x‖ := norm_add_le _ _
      _ = |v x| * ‖C.c x‖ + ‖C.d x‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ L * M + M := add_le_add (mul_le_mul hvx hc (norm_nonneg _) hL) hd
      _ = M * L + M := by ring
  have hentryB (k : Fin 2) : |y 2 * C.b x (coordinateVector 2 k)| ≤ M := by
    have hb' : |C.b x (coordinateVector 2 k)| ≤ M := by
      simpa [hbasis] using ((C.b x).le_opNorm (coordinateVector 2 k)).trans
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    rw [abs_mul]
    exact (mul_le_mul hy.2.le hb' (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hg : |C.q x * v x + C.f x| ≤ M * L + M := by
    calc
      |C.q x * v x + C.f x| ≤ |C.q x * v x| + |C.f x| := abs_add_le _ _
      _ = |C.q x| * |v x| + |C.f x| := by rw [abs_mul]
      _ ≤ M * L + M := add_le_add (mul_le_mul hq hvx (abs_nonneg _) hM0) hf
  have hentryD : |liftD κ M L + y 2 * (C.q x * v x + C.f x)| ≤
      liftD κ M L + M * L + M := by
    calc
      |liftD κ M L + y 2 * (C.q x * v x + C.f x)| ≤
        |liftD κ M L| + |y 2 * (C.q x * v x + C.f x)| := abs_add_le _ _
      _ ≤ liftD κ M L + (M * L + M) := by
        rw [abs_of_nonneg hD0, abs_mul]
        exact add_le_add_right
          ((mul_le_mul hy.2.le hg (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)) _
      _ = _ := by ring
  have hAM : M ≤ liftEntryBound κ M L := by unfold liftEntryBound; nlinarith
  have hFM : M * L + M ≤ liftEntryBound κ M L := by unfold liftEntryBound; nlinarith
  have hDM : liftD κ M L + M * L + M ≤ liftEntryBound κ M L := by
    unfold liftEntryBound; linarith
  fin_cases i <;> fin_cases j <;> simp only [liftMatrix]
  · exact (hentryA 0 0).trans hAM
  · exact (hentryA 1 0).trans hAM
  · exact (hentryF 0).trans hFM
  · exact (hentryA 0 1).trans hAM
  · exact (hentryA 1 1).trans hAM
  · exact (hentryF 1).trans hFM
  · exact (hentryB 0).trans hAM
  · exact (hentryB 1).trans hAM
  · exact hentryD.trans hDM

/-- Rank-free nonsymmetric inverse coercivity, required by the selected provider. -/
theorem R3_inverse_coercivity
    (A : Matrix (Fin 3) (Fin 3) ℝ) (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K)
    (hcoercive : ∀ ξ : E3, lam * ‖ξ‖ ^ 2 ≤ inner ℝ ξ (matrixAction A ξ))
    (hupper : ∀ ξ : E3, ‖matrixAction A ξ‖ ≤ K * ‖ξ‖) :
    ∀ ξ : E3, (lam / K ^ 2) * ‖ξ‖ ^ 2 ≤ inner ℝ ξ (matrixAction A⁻¹ ξ) := by
  have hzero (ξ : E3) (hξ : matrixAction A ξ = 0) : ξ = 0 := by
    have h := hcoercive ξ
    rw [hξ, inner_zero_right] at h
    have hs : ‖ξ‖ ^ 2 ≤ 0 := by
      exact (mul_le_mul_iff_right₀ hlam).mp (by simpa using h)
    have hn : ‖ξ‖ = 0 := by nlinarith [norm_nonneg ξ]
    exact norm_eq_zero.mp hn
  have hinj : Function.Injective A.mulVec := by
    intro p q hpq
    have hz : matrixAction A (WithLp.toLp 2 (p - q)) = 0 := by
      simp [matrixAction, Matrix.mulVec_sub, hpq]
    have := hzero _ hz
    have he : p - q = 0 := congrArg WithLp.ofLp this
    exact sub_eq_zero.mp he
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hinv (ξ : E3) : matrixAction A (matrixAction A⁻¹ ξ) = ξ := by
    simp [matrixAction, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet]
  intro ξ
  let η := matrixAction A⁻¹ ξ
  have he : matrixAction A η = ξ := hinv ξ
  have hl := hcoercive η
  rw [he, real_inner_comm] at hl
  have hu := hupper η
  rw [he] at hu
  have hs : ‖ξ‖ ^ 2 ≤ K ^ 2 * ‖η‖ ^ 2 := by
    nlinarith [norm_nonneg ξ, norm_nonneg η]
  have ht : (lam / K ^ 2) * ‖ξ‖ ^ 2 ≤ lam * ‖η‖ ^ 2 := by
    have hk2 : 0 < K ^ 2 := sq_pos_of_pos hK
    rw [div_mul_eq_mul_div, div_le_iff₀ hk2]
    nlinarith
  exact ht.trans hl

/-- Slicing/Fubini must use this actual product-to-ordinary-three-space volume identity. -/
theorem R3_liftedPoint_map_product_volume :
    Measure.map (fun xt : E2 × ℝ => liftedPoint xt.1 xt.2)
      ((volume : Measure E2).prod (volume : Measure ℝ)) = (volume : Measure E3) := by
  let e : WithLp 2 (E2 × ℝ) ≃ₗᵢ[ℝ] E3 := {
    toFun := fun p => liftedPoint p.ofLp.1 p.ofLp.2
    invFun := fun y => WithLp.toLp 2 (planarPart y, y 2)
    left_inv := by
      intro p
      apply WithLp.ofLp_injective
      apply Prod.ext
      · ext i
        fin_cases i <;> rfl
      · rfl
    right_inv := by
      intro y
      ext i
      fin_cases i <;> rfl
    map_add' := by
      intro p q
      ext i
      fin_cases i <;> rfl
    map_smul' := by
      intro c p
      ext i
      fin_cases i <;> rfl
    norm_map' := by
      intro p
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, liftedPoint,
        WithLp.prod_norm_sq_eq_of_L2, add_assoc] }
  exact (e.measurePreserving.comp (WithLp.volume_preserving_toLp E2 ℝ)).map_eq

/-- Continuity and the full support of Lebesgue measure identify the actual function
with a positive-exponent Hölder representative on an open set. -/
theorem R3_holder_representative_agrees
    (B : Set E3) (hB : IsOpen B) (V W : E3 → ℝ)
    (hcont : ContinuousOn V B) (K α : NNReal) (hα : 0 < α)
    (hholder : HolderOnWith K α W B)
    (hae : W =ᵐ[volume.restrict B] V) :
    ∀ y ∈ B, W y = V y := by
  exact Measure.eqOn_open_of_ae_eq hae hB (hholder.continuousOn hα) hcont

/-- Restricting a continuous Hölder lift to `t=0` gives the same planar function. -/
theorem R3_holder_restrict_zero_slice
    (B : Set E2) (v : E2 → ℝ) (K α : NNReal)
    (hholder : HolderOnWith K α (liftFunction v) (cylinder B)) :
    HolderOnWith K α v B := by
  have hp (x : E2) : planarPart (liftedPoint x 0) = x := by
    ext i
    fin_cases i <;> simp [planarPart, liftedPoint]
  have hd (x z : E2) : dist (liftedPoint x 0) (liftedPoint z 0) = dist x z := by
    simp only [dist_eq_norm]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, liftedPoint]
  have ht (x : E2) : liftedPoint x 0 2 = 0 := rfl
  have hf (x : E2) : liftFunction v (liftedPoint x 0) = v x := by
    rw [liftFunction, hp, ht, add_zero]
  intro x hx z hz
  have h := hholder (liftedPoint x 0) ⟨by rwa [hp], by rw [ht]; norm_num⟩
    (liftedPoint z 0) ⟨by rwa [hp], by rw [ht]; norm_num⟩
  simpa only [hf, edist_dist, hd] using h

/-- Uniform quotient Hölder bounds pass to the actual first derivative, without
assuming a second derivative or regularity of a chosen representative. -/
theorem R3_holder_derivative_of_differenceQuotients
    (Ω B : Set E2) (hΩ : IsOpen Ω) (hBΩ : B ⊆ Ω)
    (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω) (k : Fin 2)
    (r : ℝ) (hr : 0 < r) (K α : NNReal)
    (hholder : ∀ h : ℝ, 0 < |h| → |h| < r →
      HolderOnWith K α (differenceQuotient u k h) B) :
    HolderOnWith K α (fun x => planarGradient u x k) B := by
  have hlimit (x : E2) (hx : x ∈ B) :
      Tendsto (fun h => differenceQuotient u k h x) (𝓝[>] 0)
        (𝓝 (planarGradient u x k)) := by
    have hu := (hC1.differentiableOn (by norm_num) x (hBΩ hx)).differentiableAt
      (hΩ.mem_nhds (hBΩ hx))
    have hl : HasDerivAt (fun t : ℝ => x + t • coordinateVector 2 k)
        (coordinateVector 2 k) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector 2 k)).const_add x
    have hux : HasFDerivAt u (fderiv ℝ u x) (x + (0 : ℝ) • coordinateVector 2 k) := by
      simpa using hu.hasFDerivAt
    have hd := hux.comp_hasDerivAt 0 hl
    have ht := hd.tendsto_slope_zero_right
    simpa [differenceQuotient, shift, planarGradient_apply, div_eq_mul_inv,
      smul_eq_mul, mul_comm] using ht
  intro x hx z hz
  apply le_of_tendsto (continuous_edist.tendsto
    (planarGradient u x k, planarGradient u z k) |>.comp
      ((hlimit x hx).prodMk_nhds (hlimit z hz)))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < r from hr)).filter_mono nhdsWithin_le_nhds] with h hh hhr
  change 0 < h at hh
  exact hholder h (by simpa [abs_of_pos hh] using hh) (by simpa [abs_of_pos hh] using hhr) x hx z hz

end SeifertSurfaces.QuasilinearLocalization
