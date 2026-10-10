import Lean
import A2MetricFluxV468
noncomputable section
open Set Matrix MeasureTheory
open scoped ContDiff BigOperators
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.A2NativeNormalProjection
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
private theorem affine_basis_sum (v : E2) :
    (∑ i : Fin 2, v i • coordinateVector 2 i) = v := by
  ext i
  fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
private theorem affine_matrix_det (A : E2 ≃L[ℝ] E2) :
    (show Matrix (Fin 2) (Fin 2) ℝ from fun i j => A (coordinateVector 2 j) i).det =
      (A : E2 →L[ℝ] E2).det := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := fun i j => A (coordinateVector 2 j) i
  have hM : M = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis A.toLinearEquiv.toLinearMap := by
    ext i j
    simp [M, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply, coordinateVector]
  change M.det = (A : E2 →L[ℝ] E2).det
  rw [hM, LinearMap.det_toMatrix]
  rfl
private theorem affine_matrix_unit (A : E2 ≃L[ℝ] E2) :
    IsUnit (show Matrix (Fin 2) (Fin 2) ℝ from fun i j => A (coordinateVector 2 j) i).det := by
  rw [affine_matrix_det]
  apply isUnit_iff_ne_zero.mpr
  change LinearMap.det A.toLinearEquiv.toLinearMap ≠ 0
  have hu := A.toLinearEquiv.isUnit_det (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  rw [LinearMap.det_toMatrix] at hu
  exact hu.ne_zero
private theorem affine_gram_pullback (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (A : E2 ≃L[ℝ] E2) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := fun i j => A (coordinateVector 2 j) i
    metricGram g y (L.comp (A : E2 →L[ℝ] E2)) = Mᵀ * metricGram g y L * M := by
  dsimp only
  let M : Matrix (Fin 2) (Fin 2) ℝ := fun i j => A (coordinateVector 2 j) i
  have hA (i : Fin 2) : A (coordinateVector 2 i) =
      ∑ k : Fin 2, A (coordinateVector 2 i) k • coordinateVector 2 k :=
    (affine_basis_sum _).symm
  change metricGram g y (L.comp (A : E2 →L[ℝ] E2)) = Mᵀ * metricGram g y L * M
  ext i j
  change coordinateInner g y (L (A (coordinateVector 2 i)))
    (L (A (coordinateVector 2 j))) = (Mᵀ * metricGram g y L * M) i j
  conv_lhs => rw [hA i, hA j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp only [M, map_sum, map_add, map_smul, metricGram, coordinateInner, Fin.sum_univ_two, Fin.sum_univ_three,
    Matrix.mul_apply, Matrix.transpose_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring
private theorem affine_inverse_contraction (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (A : E2 ≃L[ℝ] E2) (a b : Fin 2) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      (metricGram g y (L.comp (A : E2 →L[ℝ] E2)))⁻¹ i j *
        A (coordinateVector 2 i) a * A (coordinateVector 2 j) b) =
      (metricGram g y L)⁻¹ a b := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := fun i j => A (coordinateVector 2 j) i
  have hM : IsUnit M.det := affine_matrix_unit A
  have h : M * (Mᵀ * metricGram g y L * M)⁻¹ * Mᵀ = (metricGram g y L)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    calc
      M * (M⁻¹ * ((metricGram g y L)⁻¹ * (Mᵀ)⁻¹)) * Mᵀ =
          (M * M⁻¹) * (metricGram g y L)⁻¹ * ((Mᵀ)⁻¹ * Mᵀ) := by
            simp only [Matrix.mul_assoc]
      _ = (metricGram g y L)⁻¹ := by
            rw [Matrix.mul_nonsing_inv M hM,
              Matrix.nonsing_inv_mul Mᵀ (by simpa only [Matrix.det_transpose] using hM)]
            simp
  have hab := congrArg (fun Q : Matrix (Fin 2) (Fin 2) ℝ => Q a b) h
  rw [affine_gram_pullback]
  let N : Matrix (Fin 2) (Fin 2) ℝ := Mᵀ * metricGram g y L * M
  change (∑ i : Fin 2, ∑ j : Fin 2, N⁻¹ i j * M a i * M b j) = _
  change (M * N⁻¹ * Mᵀ) a b = _ at hab
  calc
    _ = (M * N⁻¹ * Mᵀ) a b := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
      ring
    _ = _ := hab
private theorem affine_density (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (A : E2 ≃L[ℝ] E2)
    (hQ : (metricGram g y L).PosDef) :
    metricDensity g y (L.comp (A : E2 →L[ℝ] E2)) =
      |(A : E2 →L[ℝ] E2).det| * metricDensity g y L := by
  unfold metricDensity
  rw [affine_gram_pullback]
  let M : Matrix (Fin 2) (Fin 2) ℝ := fun i j => A (coordinateVector 2 j) i
  change Real.sqrt ((Mᵀ * metricGram g y L * M).det) = _
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [affine_matrix_det]
  rw [show (A : E2 →L[ℝ] E2).det * (metricGram g y L).det * (A : E2 →L[ℝ] E2).det =
    (A : E2 →L[ℝ] E2).det ^ 2 * (metricGram g y L).det by ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
private theorem affine_scalar_contraction (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (A : E2 ≃L[ℝ] E2) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      (metricGram g y (L.comp (A : E2 →L[ℝ] E2)))⁻¹ i j *
        (∑ a : Fin 2, ∑ b : Fin 2,
          A (coordinateVector 2 i) a * A (coordinateVector 2 j) b * B a b)) =
      ∑ a : Fin 2, ∑ b : Fin 2, (metricGram g y L)⁻¹ a b * B a b := by
  calc
    _ = ∑ a : Fin 2, ∑ b : Fin 2,
      (∑ i : Fin 2, ∑ j : Fin 2,
        (metricGram g y (L.comp (A : E2 →L[ℝ] E2)))⁻¹ i j *
          A (coordinateVector 2 i) a * A (coordinateVector 2 j) b) * B a b := by
      simp only [Fin.sum_univ_two]
      ring
    _ = _ := by simp_rw [affine_inverse_contraction]
private theorem affine_covariant_bilinear_pullback (g : MetricTensor) (W : E3 → E3)
    (y : E3) (L : E2 →L[ℝ] E3) (A : E2 ≃L[ℝ] E2) (i j : Fin 2) :
    coordinateInner g y
        (covariantFieldDerivative g W y ((L.comp (A : E2 →L[ℝ] E2)) (coordinateVector 2 i)))
        ((L.comp (A : E2 →L[ℝ] E2)) (coordinateVector 2 j)) =
      ∑ a : Fin 2, ∑ b : Fin 2,
        A (coordinateVector 2 i) a * A (coordinateVector 2 j) b *
          coordinateInner g y (covariantFieldDerivative g W y (L (coordinateVector 2 a)))
            (L (coordinateVector 2 b)) := by
  have hA (i : Fin 2) : A (coordinateVector 2 i) =
      ∑ k : Fin 2, A (coordinateVector 2 i) k • coordinateVector 2 k :=
    (affine_basis_sum _).symm
  change coordinateInner g y (covariantFieldDerivative g W y (L (A (coordinateVector 2 i))))
    (L (A (coordinateVector 2 j))) = _
  conv_lhs => rw [hA i, hA j]
  simp only [coordinateInner, covariantFieldDerivative, metricConnection, Fin.sum_univ_two,
    Fin.sum_univ_three, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring
private theorem affine_divergence (g : MetricTensor) (W : E3 → E3)
    (y : E3) (L : E2 →L[ℝ] E3) (A : E2 ≃L[ℝ] E2) :
    metricTangentialDivergence g W y (L.comp (A : E2 →L[ℝ] E2)) =
      metricTangentialDivergence g W y L := by
  unfold metricTangentialDivergence
  simp_rw [affine_covariant_bilinear_pullback]
  exact affine_scalar_contraction g y L A _
private theorem affine_halfbox_uniqueDiff (positive : Bool) (a b h : ℝ)
    (hab : a < b) (hh : 0 < h) :
    UniqueDiffOn ℝ (halfBoxDomain positive a b h) := by
  unfold halfBoxDomain
  rw [SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen.coordinates.uniqueDiffOn_preimage_iff]
  cases positive
  · simpa only [SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen.halfBox,
      Bool.false_eq_true, ↓reduceIte, Icc_prod_eq] using
      (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc (neg_lt_zero.mpr hh))
  · simpa only [SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen.halfBox,
      ↓reduceIte, Icc_prod_eq] using (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hh)
private theorem affine_normalProjection (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (A : E2 ≃L[ℝ] E2) (H : E3) :
    normalProjection g y (L.comp (A : E2 →L[ℝ] E2)) H = normalProjection g y L H := by
  unfold normalProjection
  congr 1
  have hA (i : Fin 2) : A (coordinateVector 2 i) =
      ∑ k : Fin 2, A (coordinateVector 2 i) k • coordinateVector 2 k :=
    (affine_basis_sum _).symm
  have ht (i : Fin 2) : (L.comp (A : E2 →L[ℝ] E2)) (coordinateVector 2 i) =
      ∑ k : Fin 2, A (coordinateVector 2 i) k • L (coordinateVector 2 k) := by
    change L (A (coordinateVector 2 i)) = _
    conv_lhs => rw [hA i]
    simp only [map_sum, map_smul]
  unfold tangentProjection
  simp only [inducedMetric, Finset.sum_smul]
  change (∑ i : Fin 2, ∑ j : Fin 2,
      ((metricGram g y (L.comp (A : E2 →L[ℝ] E2)))⁻¹ i j *
        coordinateInner g y ((L.comp (A : E2 →L[ℝ] E2)) (coordinateVector 2 j)) H) •
          ((L.comp (A : E2 →L[ℝ] E2)) (coordinateVector 2 i))) =
    ∑ i : Fin 2, ∑ j : Fin 2, ((metricGram g y L)⁻¹ i j *
      coordinateInner g y (L (coordinateVector 2 j)) H) • L (coordinateVector 2 i)
  simp_rw [ht]
  ext k
  have hc := affine_scalar_contraction g y L A
    (fun a b => L (coordinateVector 2 a) k * coordinateInner g y (L (coordinateVector 2 b)) H)
  convert hc using 1 <;>
    simp only [coordinateInner, Fin.sum_univ_two, Fin.sum_univ_three, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul] <;> ring
private theorem affine_fderiv (f : E2 → E3) (U : Set E2) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (A : E2 ≃L[ℝ] E2) (p x : E2)
    (hx : p + A x ∈ U) :
    fderiv ℝ (f ∘ (fun z => p + A z)) x =
      (fderiv ℝ f (p + A x)).comp (A : E2 →L[ℝ] E2) := by
  have hdf := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have ha : HasFDerivAt (fun z : E2 => p + A z) (A : E2 →L[ℝ] E2) x :=
    (A : E2 →L[ℝ] E2).hasFDerivAt.const_add p
  exact (hdf.hasFDerivAt.comp x ha).fderiv
private theorem affine_second_derivative (f : E2 → E3) (U : Set E2) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (A : E2 ≃L[ℝ] E2) (p x v w : E2)
    (hx : p + A x ∈ U) :
    fderiv ℝ (fun z => fderiv ℝ (f ∘ (fun z => p + A z)) z w) x v =
      fderiv ℝ (fderiv ℝ f) (p + A x) (A v) (A w) := by
  run_tac
    let source := System.FilePath.mk (← Lean.getFileName)
    let input := source.parent.getD (System.FilePath.mk ".") / "A2ProofData" / "affine_v470" / "A2AffineHalfboxV470.olean"
    let (data, _region) ← Lean.Core.liftIOCore <| Lean.readModuleData input
    let some ci := data.constants.find? (fun c => c.name.toString == "_private.A2AffineHalfboxV470.0.affine_second_derivative") | Lean.throwError "paid private derivative root absent"
    let some raw := ci.value? (allowOpaque := true) | Lean.throwError "paid actual value absent"
    let mut value := raw
    let mut args : Array Lean.Expr := #[]
    while true do
      match value with
      | .lam binder _ body _ =>
        let some decl := (← Lean.getLCtx).findFromUserName? binder | Lean.throwError "literal binder missing {binder}"
        let arg := Lean.mkFVar decl.fvarId
        args := args.push arg
        value := body.instantiate1 arg
      | _ => break
    let reconstructed ← Lean.Meta.mkLambdaFVars args value
    unless Lean.Expr.equal reconstructed raw && Lean.ExprStructEq.mk reconstructed == Lean.ExprStructEq.mk raw do Lean.throwError "stored value reconstruction drift"
    Lean.Meta.checkWithKernel value
    (← Lean.Elab.Tactic.getMainGoal).assign value
    Lean.Elab.Tactic.replaceMainGoal []

private theorem affine_original_second_derivative (f : E2 → E3) (U : Set E2) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (y v w : E2) (hy : y ∈ U) :
    fderiv ℝ (fun z => fderiv ℝ f z w) y v = fderiv ℝ (fderiv ℝ f) y v w := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) y :=
    ((hf.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero
  have hd := (hdf.hasFDerivAt.clm_apply (hasFDerivAt_const w y)).fderiv
  have hv := congrArg (fun D => D v) hd
  simpa only [ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using hv
private theorem affine_acceleration (g : MetricTensor) (f : E2 → E3) (U : Set E2)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (A : E2 ≃L[ℝ] E2) (p x : E2)
    (hx : p + A x ∈ U) (i j : Fin 2) :
    covariantAcceleration g (f ∘ (fun z => p + A z)) x i j =
      ∑ a : Fin 2, ∑ b : Fin 2,
        (A (coordinateVector 2 i) a * A (coordinateVector 2 j) b) •
          covariantAcceleration g f (p + A x) a b := by
  have ht (i : Fin 2) : graphTangent (f ∘ (fun z => p + A z)) x i =
      (fderiv ℝ f (p + A x)) (A (coordinateVector 2 i)) := by
    rw [graphTangent, affine_fderiv f U hU hf A p x hx]
    rfl
  have hA (i : Fin 2) : A (coordinateVector 2 i) =
      ∑ k : Fin 2, A (coordinateVector 2 i) k • coordinateVector 2 k :=
    (affine_basis_sum _).symm
  unfold covariantAcceleration
  rw [show fderiv ℝ (fun z => graphTangent (f ∘ (fun z => p + A z)) z j) x
      (coordinateVector 2 i) = fderiv ℝ (fderiv ℝ f) (p + A x)
        (A (coordinateVector 2 i)) (A (coordinateVector 2 j)) from
      affine_second_derivative f U hU hf A p x (coordinateVector 2 i) (coordinateVector 2 j) hx]
  simp_rw [ht]
  have hd (a b : Fin 2) : fderiv ℝ (fun z => graphTangent f z b) (p + A x)
      (coordinateVector 2 a) = fderiv ℝ (fderiv ℝ f) (p + A x)
        (coordinateVector 2 a) (coordinateVector 2 b) :=
    affine_original_second_derivative f U hU hf (p + A x)
      (coordinateVector 2 a) (coordinateVector 2 b) hx
  simp_rw [hd]
  conv_lhs => rw [hA i, hA j]
  ext k
  fin_cases k <;>
    simp [graphTangent, coordinateVector, EuclideanSpace.single, Function.comp_apply,
      Fin.sum_univ_two, Fin.sum_univ_three, map_add, map_smul, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul] <;> ring
private theorem affine_tracedAcceleration (g : MetricTensor) (f : E2 → E3) (U : Set E2)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (A : E2 ≃L[ℝ] E2) (p x : E2)
    (hx : p + A x ∈ U) :
    tracedAcceleration g (f ∘ (fun z => p + A z)) x = tracedAcceleration g f (p + A x) := by
  have hd := affine_fderiv f U hU hf A p x hx
  unfold tracedAcceleration
  have hq : inducedMetric g (f ∘ (fun z => p + A z)) x =
      metricGram g (f (p + A x)) ((fderiv ℝ f (p + A x)).comp (A : E2 →L[ℝ] E2)) := by
    ext i j
    change coordinateInner g (f (p + A x))
      (fderiv ℝ (f ∘ (fun z => p + A z)) x (coordinateVector 2 i))
      (fderiv ℝ (f ∘ (fun z => p + A z)) x (coordinateVector 2 j)) = _
    rw [hd]
    rfl
  have hq0 : inducedMetric g f (p + A x) =
      metricGram g (f (p + A x)) (fderiv ℝ f (p + A x)) := rfl
  rw [hq, hq0]
  simp_rw [affine_acceleration g f U hU hf A p x hx]
  ext k
  have hc := affine_scalar_contraction g (f (p + A x)) (fderiv ℝ f (p + A x)) A
    (fun a b => covariantAcceleration g f (p + A x) a b k)
  convert hc using 1 <;>
    simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring

/-- Same-frame affine reparametrization preserves the actual closed-halfbox
first differential, pays the determinant in Gram density, and preserves the
same-tensor covariant tangential divergence. -/
theorem affine_halfbox_closed_metric_reparametrization
    (g : MetricTensor) (W : E3 → E3) (f : E2 → E3)
    (D : Set E2) (hD : UniqueDiffOn ℝ D) (hf : ContDiffOn ℝ 1 f D)
    (A : E2 ≃L[ℝ] E2) (p : E2)
    (positive : Bool) (a b h : ℝ) (hab : a < b) (hh : 0 < h)
    (hmap : MapsTo (fun x => p + A x) (halfBoxDomain positive a b h) D)
    (hq : ∀ x ∈ halfBoxDomain positive a b h,
      (metricGram g (f (p + A x)) (fderivWithin ℝ f D (p + A x))).PosDef) :
    let F := f ∘ (fun x => p + A x)
    ∀ x ∈ halfBoxDomain positive a b h,
      halfBoxDifferential F positive a b h x =
        (fderivWithin ℝ f D (p + A x)).comp (A : E2 →L[ℝ] E2) ∧
      metricDensity g (F x) (halfBoxDifferential F positive a b h x) =
        |(A : E2 →L[ℝ] E2).det| *
          metricDensity g (f (p + A x)) (fderivWithin ℝ f D (p + A x)) ∧
      metricTangentialDivergence g W (F x) (halfBoxDifferential F positive a b h x) =
        metricTangentialDivergence g W (f (p + A x)) (fderivWithin ℝ f D (p + A x)) := by
  dsimp only
  intro x hx
  have hux := affine_halfbox_uniqueDiff positive a b h hab hh x hx
  have ha : HasFDerivAt (fun z : E2 => p + A z) (A : E2 →L[ℝ] E2) x :=
    (A : E2 →L[ℝ] E2).hasFDerivAt.const_add p
  have hd : halfBoxDifferential (f ∘ (fun z => p + A z)) positive a b h x =
      (fderivWithin ℝ f D (p + A x)).comp (A : E2 →L[ℝ] E2) := by
    exact (((hf.differentiableOn one_ne_zero (p + A x) (hmap hx)).hasFDerivWithinAt).comp
      x ha.hasFDerivWithinAt hmap).fderivWithin hux
  refine ⟨hd, ?_, ?_⟩
  · rw [hd]
    exact affine_density g (f (p + A x)) _ A (hq x hx)
  · rw [hd]
    exact affine_divergence g W (f (p + A x)) _ A


/-- With the same ambient metric tensor and the same affine bulk frame, the
normal projection of traced acceleration is invariant at the corresponding
point. -/
theorem affine_metric_normal_trace_reparametrization
    (g : MetricTensor) (f : E2 → E3) (U : Set E2)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (A : E2 ≃L[ℝ] E2) (p : E2) (x : E2) (hx : p + A x ∈ U)
    (hs : ∀ a b, g (f (p + A x)) a b = g (f (p + A x)) b a)
    (hq : (metricGram g (f (p + A x)) (fderiv ℝ f (p + A x))).PosDef) :
    normalTrace g (f ∘ (fun z => p + A z)) x = normalTrace g f (p + A x) := by
  unfold normalTrace
  rw [affine_fderiv f U hU hf A p x hx, affine_tracedAcceleration g f U hU hf A p x hx]
  exact affine_normalProjection g (f (p + A x)) (fderiv ℝ f (p + A x)) A _


end
