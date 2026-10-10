import IsothermalPDEData
noncomputable section
open Set Topology MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower
open SeifertSurfaces.AppendixACoordinates

/-- A1.4(d): literal conjugate coordinates and their auxiliary local inverse. -/
theorem conjugate_coordinates_local_isothermal_inverse (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (M : E2 → Mat2) (y : E2) (r : ℝ)
    (hr : 0 < r) (symmetric : SymmetricOn M (Metric.ball y r))
    (elliptic : UniformEllipticOn M (Metric.ball y r))
    (holder : ∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha (fun x => M x i j) (Metric.ball y r))
    (a b : E2 → ℝ) (a_regular : ScalarC1AlphaOn G.alpha a (Metric.ball y r))
    (b_regular : ScalarC1AlphaOn G.alpha b (Metric.ball y r))
    (gradient_close : ∀ x ∈ Metric.ball y r,
      ‖planarGradient a x - coordinateVector 2 0‖ < (1 / 2 : ℝ))
    (conjugate : ∀ x ∈ Metric.ball y r,
      planarGradient b x = rotation (matrixAction (normalizedInverse M x) (planarGradient a x))) :
    let chi := conjugateCoordinates a b
    ∃ Q T : Set E2, IsOpen Q ∧ y ∈ Q ∧ Q ⊆ Metric.ball y r ∧ IsOpen T ∧
      chi '' Q = T ∧ MapsTo chi Q T ∧
      ∃ inv : E2 → E2, MapsTo inv T Q ∧
        (∀ x ∈ Q, inv (chi x) = x) ∧ (∀ t ∈ T, chi (inv t) = t) ∧
        MapC1AlphaOn G.alpha chi Q ∧ MapC1AlphaOn G.alpha inv T ∧
        (∀ t ∈ T, jacobian inv t = (jacobian chi (inv t))⁻¹) ∧
        (∀ x ∈ Q, 0 < Matrix.det (jacobian chi x) ∧
          Matrix.det (jacobian chi x) =
            inner ℝ (planarGradient a x) (matrixAction (normalizedInverse M x) (planarGradient a x)) ∧
          (jacobian chi x).transpose * jacobian chi x =
            (inner ℝ (planarGradient a x) (matrixAction (normalizedInverse M x) (planarGradient a x)) /
              Real.sqrt (Matrix.det (M x))) • M x) ∧
        ∃ lambda : E2 → ℝ, (∀ t ∈ T, 0 < lambda t) ∧ ScalarCAlphaOn G.alpha lambda T ∧
          ∀ x ∈ Q,
            lambda (chi x) = Real.sqrt (Matrix.det (M x)) /
              inner ℝ (planarGradient a x) (matrixAction (normalizedInverse M x) (planarGradient a x)) ∧
            M x = lambda (chi x) • ((jacobian chi x).transpose * jacobian chi x) := by
  classical
  set_option maxHeartbeats 0 in
    have hMatrixPos (M : E2 → Mat2) (U : Set E2)
        (hs : SymmetricOn M U) (he : UniformEllipticOn M U) :
        ∀ x ∈ U, (M x).PosDef ∧ 0 < Matrix.det (M x) := by
      obtain ⟨ell, C, hell, hC, hb⟩ := he
      intro x hx
      have hP : (M x).PosDef := by
        apply Matrix.PosDef.of_dotProduct_mulVec_pos
        · ext i j
          simpa [Matrix.conjTranspose_apply] using hs x hx j i
        · intro p hp
          let v : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm p
          have hv : v ≠ 0 := by
            intro h
            apply hp
            ext i
            exact congrArg (fun z : E2 => z i) h
          have hpos := (mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hb x hx v).1
          rw [EuclideanSpace.inner_eq_star_dotProduct] at hpos
          change 0 < (Matrix.mulVec (M x) p) ⬝ᵥ p at hpos
          simpa only [star_trivial, dotProduct_comm] using hpos
      exact ⟨hP, hP.det_pos⟩
    have hQuad (M : E2 → Mat2) (U : Set E2)
        (hs : SymmetricOn M U) (he : UniformEllipticOn M U) (x : E2) (hx : x ∈ U)
        (p : E2) (hp : p ≠ 0) :
        0 < inner ℝ p (matrixAction (normalizedInverse M x) p) := by
      obtain ⟨ell, C, hell, hC, hb⟩ := he
      have hP : (M x).PosDef := by
        apply Matrix.PosDef.of_dotProduct_mulVec_pos
        · ext i j
          simpa [Matrix.conjTranspose_apply] using hs x hx j i
        · intro q hq
          let v : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm q
          have hv : v ≠ 0 := by
            intro h
            apply hq
            ext i
            exact congrArg (fun z : E2 => z i) h
          have hpos := (mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hb x hx v).1
          rw [EuclideanSpace.inner_eq_star_dotProduct] at hpos
          change 0 < (Matrix.mulVec (M x) q) ⬝ᵥ q at hpos
          simpa only [star_trivial, dotProduct_comm] using hpos
      have hq : (fun i => p i) ≠ 0 := by
        intro h
        apply hp
        ext i
        exact congrFun h i
      have hi := hP.inv.dotProduct_mulVec_pos hq
      have hquad : inner ℝ p (matrixAction (normalizedInverse M x) p) =
          Real.sqrt (Matrix.det (M x)) * inner ℝ p (matrixAction ((M x)⁻¹) p) := by
        dsimp only [normalizedInverse, matrixAction]
        simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
          Matrix.smul_apply, smul_eq_mul, starRingEnd_apply, star_trivial]
        change ((Real.sqrt (Matrix.det (M x)) * (M x)⁻¹ 0 0 * p 0 +
          Real.sqrt (Matrix.det (M x)) * (M x)⁻¹ 0 1 * p 1) * p 0 +
          (Real.sqrt (Matrix.det (M x)) * (M x)⁻¹ 1 0 * p 0 +
          Real.sqrt (Matrix.det (M x)) * (M x)⁻¹ 1 1 * p 1) * p 1) =
          Real.sqrt (Matrix.det (M x)) * (((M x)⁻¹ 0 0 * p 0 + (M x)⁻¹ 0 1 * p 1) * p 0 +
            ((M x)⁻¹ 1 0 * p 0 + (M x)⁻¹ 1 1 * p 1) * p 1)
        ring
      rw [hquad]
      apply mul_pos (Real.sqrt_pos.mpr hP.det_pos)
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change 0 < (Matrix.mulVec (M x)⁻¹ (fun i => p i)) ⬝ᵥ (fun i => p i)
      simpa only [star_trivial, dotProduct_comm] using hi
    have hGram (M : E2 → Mat2) (x : E2) (p : E2)
        (hs : M x 0 1 = M x 1 0) (hd : 0 < Matrix.det (M x)) :
        let q := rotation (matrixAction (normalizedInverse M x) p)
        let J : Mat2 := !![p 0, p 1; q 0, q 1]
        Matrix.det J = inner ℝ p (matrixAction (normalizedInverse M x) p) ∧
          J.transpose * J =
            (inner ℝ p (matrixAction (normalizedInverse M x) p) / Real.sqrt (Matrix.det (M x))) • M x := by
      let d := Matrix.det (M x)
      let s := Real.sqrt d
      have hspos : 0 < s := Real.sqrt_pos.mpr hd
      have hs2 : s ^ 2 = d := Real.sq_sqrt hd.le
      have hN : normalizedInverse M x = s⁻¹ • !![M x 1 1, -M x 0 1; -M x 1 0, M x 0 0] := by
        dsimp only [normalizedInverse]
        rw [Matrix.inv_def, Matrix.adjugate_fin_two, smul_smul]
        congr 1
        change s * Ring.inverse d = s⁻¹
        rw [Ring.inverse_eq_inv]
        rw [← hs2]
        field_simp
      have hinner : inner ℝ p (matrixAction (normalizedInverse M x) p) =
          s⁻¹ * ((M x 1 1 * p 0 - M x 0 1 * p 1) * p 0 +
            (-M x 1 0 * p 0 + M x 0 0 * p 1) * p 1) := by
        rw [hN]
        dsimp only [matrixAction]
        simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two,
          Matrix.smul_apply, smul_eq_mul, starRingEnd_apply, star_trivial]
        change ((s⁻¹ * M x 1 1 * p 0 + s⁻¹ * (-M x 0 1) * p 1) * p 0 +
          (s⁻¹ * (-M x 1 0) * p 0 + s⁻¹ * M x 0 0 * p 1) * p 1) = _
        ring
      have hq0 : rotation (matrixAction (normalizedInverse M x) p) 0 =
          s⁻¹ * (M x 1 0 * p 0 - M x 0 0 * p 1) := by
        rw [hN]
        dsimp only [rotation, matrixAction]
        simp only [Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
        change -((s⁻¹ * (-M x 1 0)) * p 0 + (s⁻¹ * M x 0 0) * p 1) = _
        ring
      have hq1 : rotation (matrixAction (normalizedInverse M x) p) 1 =
          s⁻¹ * (M x 1 1 * p 0 - M x 0 1 * p 1) := by
        rw [hN]
        dsimp only [rotation, matrixAction]
        simp only [Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
        change (s⁻¹ * M x 1 1) * p 0 + (s⁻¹ * (-M x 0 1)) * p 1 = _
        ring
      dsimp only
      constructor
      · simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, hq0, hq1, hinner]
        ring
      · ext i j
        have hds : M x 0 0 * M x 1 1 - M x 1 0 * M x 1 0 = s ^ 2 := by
          rw [hs2]
          dsimp only [d]
          rw [Matrix.det_fin_two, hs]
        fin_cases i <;> fin_cases j
        all_goals
          simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.of_apply,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
            hq0, hq1, hinner, Matrix.smul_apply, smul_eq_mul]
          change _ = (s⁻¹ * ((M x 1 1 * p 0 - M x 0 1 * p 1) * p 0 +
            (-M x 1 0 * p 0 + M x 0 0 * p 1) * p 1) / s) * _
        · change p 0 * p 0 + (s⁻¹ * (M x 1 0 * p 0 - M x 0 0 * p 1)) *
            (s⁻¹ * (M x 1 0 * p 0 - M x 0 0 * p 1)) =
            (s⁻¹ * ((M x 1 1 * p 0 - M x 0 1 * p 1) * p 0 +
              (-M x 1 0 * p 0 + M x 0 0 * p 1) * p 1) / s) * M x 0 0
          rw [hs]; field_simp
          linear_combination -(p 0)^2 * hds
        · change p 0 * p 1 + (s⁻¹ * (M x 1 0 * p 0 - M x 0 0 * p 1)) *
            (s⁻¹ * (M x 1 1 * p 0 - M x 0 1 * p 1)) =
            (s⁻¹ * ((M x 1 1 * p 0 - M x 0 1 * p 1) * p 0 +
              (-M x 1 0 * p 0 + M x 0 0 * p 1) * p 1) / s) * M x 0 1
          rw [hs]; field_simp
          linear_combination -(p 0 * p 1) * hds
        · change p 1 * p 0 + (s⁻¹ * (M x 1 1 * p 0 - M x 0 1 * p 1)) *
            (s⁻¹ * (M x 1 0 * p 0 - M x 0 0 * p 1)) =
            (s⁻¹ * ((M x 1 1 * p 0 - M x 0 1 * p 1) * p 0 +
              (-M x 1 0 * p 0 + M x 0 0 * p 1) * p 1) / s) * M x 1 0
          rw [hs]; field_simp
          linear_combination -(p 0 * p 1) * hds
        · change p 1 * p 1 + (s⁻¹ * (M x 1 1 * p 0 - M x 0 1 * p 1)) *
            (s⁻¹ * (M x 1 1 * p 0 - M x 0 1 * p 1)) =
            (s⁻¹ * ((M x 1 1 * p 0 - M x 0 1 * p 1) * p 0 +
              (-M x 1 0 * p 0 + M x 0 0 * p 1) * p 1) / s) * M x 1 1
          rw [hs]
          field_simp
          linear_combination -(p 1)^2 * hds
    have hForwardJac (a b : E2 → ℝ) (U : Set E2) (hU : IsOpen U)
        (ha : ContDiffOn ℝ 1 a U) (hb : ContDiffOn ℝ 1 b U) :
        ContDiffOn ℝ 1 (conjugateCoordinates a b) U ∧
          ∀ x ∈ U, jacobian (conjugateCoordinates a b) x =
            !![planarGradient a x 0, planarGradient a x 1;
               planarGradient b x 0, planarGradient b x 1] := by
      have hc : ContDiffOn ℝ 1 (conjugateCoordinates a b) U := by
        apply (contDiffOn_piLp (2 : ℝ≥0∞)).2
        intro i
        fin_cases i
        · exact ha
        · exact hb
      have hg (f : E2 → ℝ) (x : E2) (i : Fin 2) :
          planarGradient f x i = fderiv ℝ f x (coordinateVector 2 i) := by
        fin_cases i <;> simp [planarGradient, Fin.sum_univ_succ, coordinateVector,
          EuclideanSpace.single]
      refine ⟨hc, ?_⟩
      intro x hx
      have hd := (hc.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
      have hcomponent (i : Fin 2) :
          fderiv ℝ (fun z => conjugateCoordinates a b z i) x =
            (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ (conjugateCoordinates a b) x) :=
        by
          simpa only [Function.comp_def, EuclideanSpace.coe_proj] using
            (((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := conjugateCoordinates a b x)).comp x hd.hasFDerivAt).fderiv
      have hrow (i j : Fin 2) : jacobian (conjugateCoordinates a b) x i j =
          fderiv ℝ (fun z => conjugateCoordinates a b z i) x (coordinateVector 2 j) := by
        dsimp only [jacobian]
        simpa only [ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj] using
          (congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 j)) (hcomponent i)).symm
      ext i j
      fin_cases i <;> fin_cases j
      · change jacobian (conjugateCoordinates a b) x 0 0 = planarGradient a x 0
        rw [hg]; exact hrow 0 0
      · change jacobian (conjugateCoordinates a b) x 0 1 = planarGradient a x 1
        rw [hg]; exact hrow 0 1
      · change jacobian (conjugateCoordinates a b) x 1 0 = planarGradient b x 0
        rw [hg]; exact hrow 1 0
      · change jacobian (conjugateCoordinates a b) x 1 1 = planarGradient b x 1
        rw [hg]; exact hrow 1 1
    have hLocalInverse (f : E2 → E2) (U : Set E2) (hU : IsOpen U) (y : E2) (hy : y ∈ U)
        (hC : ContDiffOn ℝ 1 f U) (hdet : ∀ x ∈ U, Matrix.det (jacobian f x) ≠ 0) :
        ∃ Q T : Set E2, IsOpen Q ∧ y ∈ Q ∧ Q ⊆ U ∧ IsOpen T ∧
          f '' Q = T ∧ MapsTo f Q T ∧
          ∃ inv : E2 → E2, MapsTo inv T Q ∧
            (∀ x ∈ Q, inv (f x) = x) ∧ (∀ t ∈ T, f (inv t) = t) ∧
            ContDiffOn ℝ 1 f Q ∧ ContDiffOn ℝ 1 inv T ∧
            ∀ t ∈ T, jacobian inv t = (jacobian f (inv t))⁻¹ := by
      have hjac (g : E2 → E2) (x : E2) :
          LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (fderiv ℝ g x).toLinearMap = jacobian g x := by
        ext i j
        dsimp only [jacobian]
        simp [LinearMap.toMatrix_apply, coordinateVector, EuclideanSpace.basisFun_apply]
      have hequiv (x : E2) (hx : x ∈ U) :
          ∃ L : E2 ≃L[ℝ] E2, (L : E2 →L[ℝ] E2) = fderiv ℝ f x := by
        have hd : (fderiv ℝ f x).toLinearMap.det ≠ 0 := by
          rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, hjac]
          exact hdet x hx
        have hk : (fderiv ℝ f x).toLinearMap.ker = ⊥ := by
          by_contra h
          exact hd (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
        have hi := LinearMap.ker_eq_bot.mp hk
        have hb : Function.Bijective (fderiv ℝ f x).toLinearMap := ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
        exact ⟨(LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap hb).toContinuousLinearEquiv, by ext v; rfl⟩
      have hCy : ContDiffAt ℝ 1 f y := hC.contDiffAt (hU.mem_nhds hy)
      obtain ⟨L, hL⟩ := hequiv y hy
      have hDy : HasFDerivAt f (L : E2 →L[ℝ] E2) y := by
        rw [hL]; exact (hCy.differentiableAt one_ne_zero).hasFDerivAt
      let e := hCy.toOpenPartialHomeomorph f hDy one_ne_zero
      let Q := e.source ∩ U
      let T := e.target ∩ e.symm ⁻¹' U
      have hQ : IsOpen Q := e.open_source.inter hU
      have hT : IsOpen T := e.isOpen_inter_preimage_symm hU
      have hmaps : MapsTo e.symm T Q := by
        intro t ht
        exact ⟨e.map_target ht.1, ht.2⟩
      have hI : ContDiffOn ℝ 1 e.symm T := by
        intro t ht
        obtain ⟨Lt, hLt⟩ := hequiv (e.symm t) ht.2
        have hDt : HasFDerivAt e (Lt : E2 →L[ℝ] E2) (e.symm t) := by
          change HasFDerivAt f _ _
          rw [hLt]
          exact ((hC.contDiffAt (hU.mem_nhds ht.2)).differentiableAt one_ne_zero).hasFDerivAt
        exact (e.contDiffAt_symm ht.1 hDt (hC.contDiffAt (hU.mem_nhds ht.2))).contDiffWithinAt
      refine ⟨Q, T, hQ, ⟨hCy.mem_toOpenPartialHomeomorph_source hDy one_ne_zero, hy⟩,
        inter_subset_right, hT, e.image_source_inter_eq' U, ?_, e.symm, hmaps, ?_, ?_,
        hC.mono inter_subset_right, hI, ?_⟩
      · intro x hx
        refine ⟨e.map_source hx.1, ?_⟩
        change e.symm (e x) ∈ U
        rw [e.left_inv hx.1]
        exact hx.2
      · intro x hx; exact e.left_inv hx.1
      · intro t ht; exact e.right_inv ht.1
      · intro t ht
        have hDf : DifferentiableAt ℝ f (e.symm t) :=
          (hC.contDiffAt (hU.mem_nhds ht.2)).differentiableAt one_ne_zero
        have hDi : DifferentiableAt ℝ e.symm t := (hI.contDiffAt (hT.mem_nhds ht)).differentiableAt one_ne_zero
        have hid : (fun z => f (e.symm z)) =ᶠ[𝓝 t] id :=
          Filter.Eventually.mono (e.open_target.mem_nhds ht.1) (fun z hz => e.right_inv hz)
        have hchain := hDf.hasFDerivAt.comp t hDi.hasFDerivAt
        have hlin := (hchain.congr_of_eventuallyEq hid.symm).unique (hasFDerivAt_id t)
        have hm := congrArg (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) (congrArg ContinuousLinearMap.toLinearMap hlin)
        change LinearMap.toMatrix _ _ ((fderiv ℝ f (e.symm t)).toLinearMap.comp
          (fderiv ℝ e.symm t).toLinearMap) = LinearMap.toMatrix _ _ LinearMap.id at hm
        rw [LinearMap.toMatrix_comp _ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis _, hjac, hjac,
          LinearMap.toMatrix_id] at hm
        have hu : IsUnit (Matrix.det (jacobian f (e.symm t))) := isUnit_iff_ne_zero.mpr (hdet _ ht.2)
        calc
          jacobian e.symm t = 1 * jacobian e.symm t := (one_mul _).symm
          _ = (jacobian f (e.symm t))⁻¹ * jacobian f (e.symm t) * jacobian e.symm t := by rw [Matrix.nonsing_inv_mul _ hu]
          _ = (jacobian f (e.symm t))⁻¹ := by rw [mul_assoc, hm, mul_one]
    have hHolderSmooth {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
        (alpha : ℝ≥0) (ha : 0 < alpha) (h : E2 → D) (F : D → ℝ)
        (U : Set E2)
        (hh : ∀ x ∈ U, ∃ s : ℝ, 0 < s ∧ Metric.ball x s ⊆ U ∧
          ∃ C : ℝ≥0, HolderOnWith C alpha h (Metric.ball x s))
        (hF : ∀ x ∈ U, ContDiffAt ℝ 1 F (h x)) :
        ScalarCAlphaOn alpha (fun x => F (h x)) U := by
      intro x hx
      obtain ⟨s, hs, hsub, C, hC⟩ := hh x hx
      obtain ⟨K, V, hV, hK⟩ := (hF x hx).exists_lipschitzOnWith
      have hc : ContinuousAt h x :=
        (hC.continuousOn ha x (Metric.mem_ball_self hs)).continuousAt
          (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hs))
      obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp
        (Filter.inter_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hs))
          (hc.preimage_mem_nhds hV))
      refine ⟨d, hd, fun z hz => hsub (hball hz).1, ?_⟩
      have hcsmall := hC.mono (fun z hz => (hball hz).1)
      have hhcomp := hK.holderOnWith.comp hcsmall (fun z hz => (hball hz).2)
      exact ⟨_, by simpa only [one_mul, NNReal.coe_one, NNReal.rpow_one, Function.comp_def] using hhcomp⟩
    have hHolderMatrix (alpha : ℝ≥0) (h : E2 → Fin 2 → Fin 2 → ℝ) (U : Set E2)
        (hh : ∀ i j : Fin 2, ∃ C : ℝ≥0, HolderOnWith C alpha (fun z => h z i j) U) :
        ∃ C : ℝ≥0, HolderOnWith C alpha h U := by
      choose C hC using hh
      let K := ∑ i : Fin 2, ∑ j : Fin 2, C i j
      refine ⟨K, ?_⟩
      intro x hx y hy
      apply edist_pi_le_iff.mpr
      intro i
      apply edist_pi_le_iff.mpr
      intro j
      apply (hC i j x hx y hy).trans
      gcongr
      exact (Finset.single_le_sum (fun k _ => bot_le (a := C i k)) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun k _ => bot_le (a := ∑ l : Fin 2, C k l)) (Finset.mem_univ i))
    have hHolderCompose {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
        (alpha : ℝ≥0) (h : E2 → D) (g : E2 → E2) (U T : Set E2) (hT : IsOpen T)
        (hg : ContDiffOn ℝ 1 g T) (hmap : MapsTo g T U)
        (hh : ∀ x ∈ U, ∃ s : ℝ, 0 < s ∧ Metric.ball x s ⊆ U ∧
          ∃ C : ℝ≥0, HolderOnWith C alpha h (Metric.ball x s)) :
        ∀ t ∈ T, ∃ s : ℝ, 0 < s ∧ Metric.ball t s ⊆ T ∧
          ∃ C : ℝ≥0, HolderOnWith C alpha (fun z => h (g z)) (Metric.ball t s) := by
      intro t ht
      obtain ⟨s, hs, hsU, C, hC⟩ := hh (g t) (hmap ht)
      have hgt := hg.contDiffAt (hT.mem_nhds ht)
      obtain ⟨K, V, hV, hK⟩ := hgt.exists_lipschitzOnWith
      obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem
        (hT.mem_nhds ht) (Filter.inter_mem hV
          (hgt.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hs)))))
      refine ⟨d, hd, fun z hz => (hball hz).1, ?_⟩
      have hcomp := hC.comp (hK.mono (fun z hz => (hball hz).2.1)).holderOnWith
        (fun z hz => (hball hz).2.2)
      exact ⟨_, by simpa only [mul_one, NNReal.coe_one, Function.comp_def] using hcomp⟩
    have hHolderCollect {I : Type} [Fintype I] [Nonempty I] (alpha : ℝ≥0) (h : I → E2 → ℝ) (U : Set E2)
        (hh : ∀ i, ScalarCAlphaOn alpha (h i) U) :
        ∀ x ∈ U, ∃ s : ℝ, 0 < s ∧ Metric.ball x s ⊆ U ∧
          ∀ i, ∃ C : ℝ≥0, HolderOnWith C alpha (h i) (Metric.ball x s) := by
      intro x hx
      choose s hs hsU C hC using (fun i => hh i x hx)
      obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp
        (Filter.iInter_mem.mpr (fun i : I => (show Metric.ball x (s i) ∈ nhds x from Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hs i)))))
      refine ⟨d, hd, fun z hz => hsU (Classical.arbitrary I) (Set.mem_iInter.mp (hball hz) _), ?_⟩
      intro i
      exact ⟨C i, (hC i).mono (fun z hz => Set.mem_iInter.mp (hball hz) i)⟩
    have hSmoothInv (w : Fin 2 → Fin 2 → ℝ) (hw : Matrix.det (Matrix.of w) ≠ 0) (i j : Fin 2) :
        ContDiffAt ℝ 1 (fun v : Fin 2 → Fin 2 → ℝ => ((Matrix.of v)⁻¹) i j) w := by
      simp only [Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.det_fin_two, Ring.inverse_eq_inv,
        Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
      have hd : w 0 0 * w 1 1 - w 0 1 * w 1 0 ≠ 0 := by simpa [Matrix.det_fin_two] using hw
      fin_cases i <;> fin_cases j
      · change ContDiffAt ℝ 1 (fun v : Fin 2 → Fin 2 → ℝ => (v 0 0 * v 1 1 - v 0 1 * v 1 0)⁻¹ * v 1 1) w
        fun_prop (disch := exact hd)
      · change ContDiffAt ℝ 1 (fun v : Fin 2 → Fin 2 → ℝ => (v 0 0 * v 1 1 - v 0 1 * v 1 0)⁻¹ * (-v 0 1)) w
        fun_prop (disch := exact hd)
      · change ContDiffAt ℝ 1 (fun v : Fin 2 → Fin 2 → ℝ => (v 0 0 * v 1 1 - v 0 1 * v 1 0)⁻¹ * (-v 1 0)) w
        fun_prop (disch := exact hd)
      · change ContDiffAt ℝ 1 (fun v : Fin 2 → Fin 2 → ℝ => (v 0 0 * v 1 1 - v 0 1 * v 1 0)⁻¹ * v 0 0) w
        fun_prop (disch := exact hd)
    have hHolderPair {D F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
        [NormedAddCommGroup F] [NormedSpace ℝ F]
        (alpha : ℝ≥0) (h : E2 → D) (g : E2 → F) (U : Set E2)
        (hh : ∀ x ∈ U, ∃ s : ℝ, 0 < s ∧ Metric.ball x s ⊆ U ∧
          ∃ C : ℝ≥0, HolderOnWith C alpha h (Metric.ball x s))
        (hg : ∀ x ∈ U, ∃ s : ℝ, 0 < s ∧ Metric.ball x s ⊆ U ∧
          ∃ C : ℝ≥0, HolderOnWith C alpha g (Metric.ball x s)) :
        ∀ x ∈ U, ∃ s : ℝ, 0 < s ∧ Metric.ball x s ⊆ U ∧
          ∃ C : ℝ≥0, HolderOnWith C alpha (fun z => (h z, g z)) (Metric.ball x s) := by
      intro x hx
      obtain ⟨s, hs, hsU, C, hC⟩ := hh x hx
      obtain ⟨t, ht, htU, K, hK⟩ := hg x hx
      refine ⟨min s t, lt_min hs ht, fun z hz => hsU (Metric.ball_subset_ball (min_le_left _ _) hz), C + K, ?_⟩
      intro z hz w hw
      rw [Prod.edist_eq]
      apply max_le
      · apply (hC z (Metric.ball_subset_ball (min_le_left _ _) hz) w (Metric.ball_subset_ball (min_le_left _ _) hw)).trans
        gcongr
        exact le_add_right le_rfl
      · apply (hK z (Metric.ball_subset_ball (min_le_right _ _) hz) w (Metric.ball_subset_ball (min_le_right _ _) hw)).trans
        gcongr
        exact le_add_left le_rfl
    have hSmoothLambda (w : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ))
        (hM : 0 < Matrix.det (Matrix.of w.1)) (hJ : Matrix.det (Matrix.of w.2) ≠ 0) :
        ContDiffAt ℝ 1 (fun v : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) =>
          Real.sqrt (Matrix.det (Matrix.of v.1)) / Matrix.det (Matrix.of v.2)) w := by
      have hd : ContDiffAt ℝ 1 (fun v : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) =>
        Matrix.det (Matrix.of v.1)) w := by
        simp only [Matrix.det_fin_two, Matrix.of_apply]
        fun_prop
      have he : ContDiffAt ℝ 1 (fun v : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) =>
        Matrix.det (Matrix.of v.2)) w := by
        simp only [Matrix.det_fin_two, Matrix.of_apply]
        fun_prop
      exact (hd.sqrt hM.ne').div he hJ
    let U := Metric.ball y r
    let chi := conjugateCoordinates a b
    have hy : y ∈ U := Metric.mem_ball_self hr
    have hC : ContDiffOn ℝ 1 chi U := (hForwardJac a b U Metric.isOpen_ball a_regular.1 b_regular.1).1
    have hJ (x : E2) (hx : x ∈ U) : jacobian chi x =
        !![planarGradient a x 0, planarGradient a x 1;
           planarGradient b x 0, planarGradient b x 1] :=
      (hForwardJac a b U Metric.isOpen_ball a_regular.1 b_regular.1).2 x hx
    have hnonzero (x : E2) (hx : x ∈ U) : planarGradient a x ≠ 0 := by
      intro hz
      have hh := gradient_close x hx
      rw [hz, zero_sub, norm_neg] at hh
      have hbase : ‖coordinateVector 2 0‖ = (1 : ℝ) := by
        simp [coordinateVector]
      rw [hbase] at hh
      norm_num at hh
    have hproperties (x : E2) (hx : x ∈ U) :
        0 < Matrix.det (jacobian chi x) ∧
        Matrix.det (jacobian chi x) =
          inner ℝ (planarGradient a x) (matrixAction (normalizedInverse M x) (planarGradient a x)) ∧
        (jacobian chi x).transpose * jacobian chi x =
          (inner ℝ (planarGradient a x) (matrixAction (normalizedInverse M x) (planarGradient a x)) /
            Real.sqrt (Matrix.det (M x))) • M x := by
      have hg := hGram M x (planarGradient a x) (symmetric x hx 0 1)
        ((hMatrixPos M U symmetric elliptic x hx).2)
      change _ ∧ _ at hg
      have hjeq : jacobian chi x =
          !![planarGradient a x 0, planarGradient a x 1;
            rotation (matrixAction (normalizedInverse M x) (planarGradient a x)) 0,
            rotation (matrixAction (normalizedInverse M x) (planarGradient a x)) 1] := by
        rw [hJ x hx, conjugate x hx]
      rw [hjeq]
      exact ⟨by rw [hg.1]; exact hQuad M U symmetric elliptic x hx _ (hnonzero x hx), hg⟩
    have hMF : MapC1AlphaOn G.alpha chi U := by
      refine ⟨hC, ?_⟩
      intro x hx
      obtain ⟨sa, hsa, hUa, hHa⟩ := a_regular.2 x hx
      obtain ⟨sb, hsb, hUb, hHb⟩ := b_regular.2 x hx
      let s := min sa sb
      have hsa' : Metric.ball x s ⊆ Metric.ball x sa := Metric.ball_subset_ball (min_le_left _ _)
      have hsb' : Metric.ball x s ⊆ Metric.ball x sb := Metric.ball_subset_ball (min_le_right _ _)
      refine ⟨s, lt_min hsa hsb, fun z hz => hUa (hsa' hz), ?_⟩
      intro i j
      fin_cases i
      · obtain ⟨C, hH⟩ := hHa j
        refine ⟨C, ?_⟩
        intro z hz w hw
        change edist (jacobian chi z 0 j) (jacobian chi w 0 j) ≤ _
        rw [hJ z (hUa (hsa' hz)), hJ w (hUa (hsa' hw))]
        fin_cases j
        · change edist (planarGradient a z 0) (planarGradient a w 0) ≤ _
          exact hH z (hsa' hz) w (hsa' hw)
        · change edist (planarGradient a z 1) (planarGradient a w 1) ≤ _
          exact hH z (hsa' hz) w (hsa' hw)
      · obtain ⟨C, hH⟩ := hHb j
        refine ⟨C, ?_⟩
        intro z hz w hw
        change edist (jacobian chi z 1 j) (jacobian chi w 1 j) ≤ _
        rw [hJ z (hUb (hsb' hz)), hJ w (hUb (hsb' hw))]
        fin_cases j
        · change edist (planarGradient b z 0) (planarGradient b w 0) ≤ _
          exact hH z (hsb' hz) w (hsb' hw)
        · change edist (planarGradient b z 1) (planarGradient b w 1) ≤ _
          exact hH z (hsb' hz) w (hsb' hw)
    obtain ⟨Q, T, hQ, hyQ, hQU, hT, himage, hmaps, inv, hinvmaps, hleft, hright, hCQ, hCI, hJinv⟩ :=
      hLocalInverse chi U Metric.isOpen_ball y hy hC (fun x hx => (hproperties x hx).1.ne')
    let HJ : E2 → Fin 2 → Fin 2 → ℝ := fun x i j => jacobian chi x i j
    let HM : E2 → Fin 2 → Fin 2 → ℝ := fun x i j => M x i j
    have hHJ : ∀ x ∈ U, ∃ s : ℝ, 0 < s ∧ Metric.ball x s ⊆ U ∧
        ∃ C : ℝ≥0, HolderOnWith C G.alpha HJ (Metric.ball x s) := by
      intro x hx
      obtain ⟨s, hs, hsU, hh⟩ := hMF.2 x hx
      obtain ⟨C, hc⟩ := hHolderMatrix G.alpha HJ (Metric.ball x s) hh
      exact ⟨s, hs, hsU, C, hc⟩
    have hHM : ∀ x ∈ U, ∃ s : ℝ, 0 < s ∧ Metric.ball x s ⊆ U ∧
        ∃ C : ℝ≥0, HolderOnWith C G.alpha HM (Metric.ball x s) := by
      obtain ⟨C, hc⟩ := hHolderMatrix G.alpha HM U holder
      intro x hx
      obtain ⟨s, hs, hsU⟩ := Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hx)
      exact ⟨s, hs, hsU, C, hc.mono hsU⟩
    have hmapU : MapsTo inv T U := fun t ht => hQU (hinvmaps ht)
    have hHI := hHolderCompose G.alpha HJ inv U T hT hCI hmapU hHJ
    have hMI : MapC1AlphaOn G.alpha inv T := by
      refine ⟨hCI, ?_⟩
      have hh (ij : Fin 2 × Fin 2) : ScalarCAlphaOn G.alpha
          (fun z => jacobian inv z ij.1 ij.2) T := by
        have hentry := hHolderSmooth G.alpha G.alpha_pos
          (fun z => HJ (inv z))
          (fun v : Fin 2 → Fin 2 → ℝ => ((Matrix.of v)⁻¹) ij.1 ij.2) T hHI
          (fun t ht => hSmoothInv (HJ (inv t)) ((hproperties (inv t) (hmapU ht)).1.ne') ij.1 ij.2)
        intro t ht
        obtain ⟨s, hs, hsT, C, hc⟩ := hentry t ht
        refine ⟨s, hs, hsT, C, ?_⟩
        intro z hz w hw
        change edist (jacobian inv z ij.1 ij.2) (jacobian inv w ij.1 ij.2) ≤ _
        rw [hJinv z (hsT hz), hJinv w (hsT hw)]
        exact hc z hz w hw
      intro t ht
      obtain ⟨s, hs, hsT, hh⟩ := hHolderCollect G.alpha
        (fun ij : Fin 2 × Fin 2 => fun z => jacobian inv z ij.1 ij.2) T hh t ht
      exact ⟨s, hs, hsT, fun i j => hh (i,j)⟩
    refine ⟨Q, T, hQ, hyQ, hQU, hT, himage, hmaps, inv, hinvmaps, hleft, hright,
      ⟨hCQ, ?_⟩, hMI, hJinv, fun x hx => hproperties x (hQU hx), ?_⟩
    · intro x hx
      obtain ⟨s, hs, hsU, hH⟩ := hMF.2 x (hQU hx)
      obtain ⟨d, hd, hdQ⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds hx)
      refine ⟨min s d, lt_min hs hd, fun z hz => hdQ (Metric.ball_subset_ball (min_le_right _ _) hz), ?_⟩
      intro i j
      obtain ⟨C, hC⟩ := hH i j
      exact ⟨C, hC.mono (Metric.ball_subset_ball (min_le_left _ _))⟩
    · let lambda : E2 → ℝ := fun t =>
        Real.sqrt (Matrix.det (M (inv t))) / Matrix.det (jacobian chi (inv t))
      have hlambda : ScalarCAlphaOn G.alpha lambda T := by
        have hpair := hHolderPair G.alpha HM HJ U hHM hHJ
        have hcomp := hHolderCompose G.alpha (fun x => (HM x, HJ x)) inv U T hT hCI hmapU hpair
        exact hHolderSmooth G.alpha G.alpha_pos
          (fun z => (HM (inv z), HJ (inv z)))
          (fun v : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) =>
            Real.sqrt (Matrix.det (Matrix.of v.1)) / Matrix.det (Matrix.of v.2)) T hcomp
          (fun t ht => hSmoothLambda (HM (inv t), HJ (inv t))
            ((hMatrixPos M U symmetric elliptic (inv t) (hmapU ht)).2)
            ((hproperties (inv t) (hmapU ht)).1.ne'))
      refine ⟨lambda, ?_, hlambda, ?_⟩
      · intro t ht
        exact div_pos (Real.sqrt_pos.mpr ((hMatrixPos M U symmetric elliptic (inv t) (hmapU ht)).2))
          ((hproperties (inv t) (hmapU ht)).1)
      · intro x hx
        have hp := hproperties x (hQU hx)
        have hs : 0 < Real.sqrt (Matrix.det (M x)) :=
          Real.sqrt_pos.mpr ((hMatrixPos M U symmetric elliptic x (hQU hx)).2)
        have hv : 0 < inner ℝ (planarGradient a x)
            (matrixAction (normalizedInverse M x) (planarGradient a x)) := by
          rw [← hp.2.1]; exact hp.1
        have hlam : lambda (chi x) = Real.sqrt (Matrix.det (M x)) /
            inner ℝ (planarGradient a x) (matrixAction (normalizedInverse M x) (planarGradient a x)) := by
          dsimp only [lambda]
          rw [hleft x hx, hp.2.1]
        refine ⟨hlam, ?_⟩
        rw [hlam, hp.2.2, smul_smul]
        have hh : (Real.sqrt (Matrix.det (M x)) /
            inner ℝ (planarGradient a x) (matrixAction (normalizedInverse M x) (planarGradient a x))) *
            (inner ℝ (planarGradient a x) (matrixAction (normalizedInverse M x) (planarGradient a x)) /
            Real.sqrt (Matrix.det (M x))) = 1 := by
          field_simp
        rw [hh, one_smul]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower
