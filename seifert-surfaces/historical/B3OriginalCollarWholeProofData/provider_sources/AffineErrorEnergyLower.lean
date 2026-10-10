import GradientEstimateRescalingData
import NormalizedMetricEnergyCorollary

noncomputable section
set_option autoImplicit false
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower
open SeifertSurfaces.AppendixACoordinates

/-- The full-ball energy bound for every supplied native affine weak solution. -/
theorem affine_error_energy_bound (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (M : E2 → Mat2) (y : E2) (r : ℝ)
    (hr : 0 < r) (symmetric : SymmetricOn M (Metric.ball y r))
    (elliptic : UniformEllipticOn M (Metric.ball y r))
    (holder : ∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha (fun x => M x i j) (Metric.ball y r)) :
    ∃ r1 E : ℝ, 0 < r1 ∧ r1 ≤ r ∧ r1 ≤ 1 ∧ 0 ≤ E ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ r1 →
        ∀ (a : E2 → ℝ) (da : E2 → E2), AffineWeakSolution M y rho a da →
          (∫ x in Metric.ball y rho, ‖da x - coordinateVector 2 0‖ ^ 2) ≤
            E * rho ^ (2 + 2 * (G.alpha : ℝ)) := by
  have normalized_local :
      ∃ r1 lam Lambda : ℝ, ∃ HN : ℝ≥0,
        0 < r1 ∧ r1 ≤ r ∧ r1 ≤ 1 ∧ 0 < lam ∧
        (∀ x ∈ Metric.ball y r1, ∀ v : E2,
          lam * ‖v‖ ^ 2 ≤ inner ℝ v (matrixAction (normalizedInverse M x) v) ∧
          ‖matrixAction (normalizedInverse M x) v‖ ≤ Lambda * ‖v‖) ∧
        (∀ i j, HolderOnWith HN G.alpha (fun x => normalizedInverse M x i j)
          (Metric.ball y r1)) := by
    exact SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.MetricNormalization.normalizedInverse_energy_local_bounds R A G M y r hr symmetric elliptic holder
  have energy_conditional (alpha : ℝ≥0) (halpha : 0 < alpha) (N : E2 → Mat2) (y : E2)
    (r1 lam Lambda : ℝ) (hr1 : 0 < r1) (hlam : 0 < lam) (HN : ℝ≥0)
    (bounds : ∀ x ∈ Metric.ball y r1, ∀ v : E2,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v (matrixAction (N x) v) ∧
      ‖matrixAction (N x) v‖ ≤ Lambda * ‖v‖)
    (holder : ∀ i j, HolderOnWith HN alpha (fun x => N x i j) (Metric.ball y r1)) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ rho : ℝ, 0 < rho → rho ≤ r1 →
      ∀ (a : E2 → ℝ) (da : E2 → E2),
      H10On (Metric.ball y rho) (fun x => a x - affineDatum y x)
        (fun x => da x - coordinateVector 2 0) →
      MemLp da 2 (volume.restrict (Metric.ball y rho)) →
      WeakLinearEquationOn (Metric.ball y rho) N (fun _ => 0) (fun _ => 0) a da →
      (∫ x in Metric.ball y rho, ‖da x - coordinateVector 2 0‖ ^ 2) ≤
        E * rho ^ (2 + 2 * (alpha : ℝ)) := by
    have h10test (U : Set E2) (u : E2 → ℝ) (du q : E2 → E2)
        (hu : H10On U u du) (hq : MemLp q 2 (volume.restrict U))
        (htest : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ U →
          (∫ x in U, inner ℝ (q x) (planarGradient phi x)) = 0) :
        (∫ x in U, inner ℝ (q x) (du x)) = 0 := by
      let μ := volume.restrict U
      have hdu : MemLp du 2 μ := hu.1.2.2
      have inner_eq (f g : E2 → E2) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
          inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
        rw [hfx, hgx]
      have inner_int (f g : E2 → E2) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
          Integrable (fun x => inner ℝ (f x) (g x)) μ := by
        apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
        filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
        rw [hfx, hgx]
      have norm_sq (f : E2 → E2) (hf : MemLp f 2 μ) :
          ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
        rw [← real_inner_self_eq_norm_sq, inner_eq]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => real_inner_self_eq_norm_sq (f x)
      have hg_mem (phi : E2 → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
          MemLp (planarGradient phi) 2 μ := by
        have hm (i : Fin 2) : MemLp (fun x => fderiv ℝ phi x (coordinateVector 2 i)) 2 μ :=
          ((hp.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
            (hc.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i))
        have hs : MemLp (fun x => ∑ i : Fin 2,
            fderiv ℝ phi x (coordinateVector 2 i) • coordinateVector 2 i) 2 μ := by
          apply memLp_finsetSum
          intro i hi
          exact (hm i).continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector 2 i))
        exact hs
      have hzero : inner ℝ (hq.toLp q) (hdu.toLp du) = 0 := by
        apply eq_of_abs_sub_lt_all
        intro ε hε
        let B := ‖hq.toLp q‖ + 1
        have hB : 0 < B := by dsimp [B]; positivity
        obtain ⟨phi, hp, hc, hs, herr⟩ := hu.2 ((ε / B) ^ 2) (sq_pos_of_pos (div_pos hε hB))
        have hg := hg_mem phi hp hc
        have hd := hdu.sub hg
        have hu_diff : MemLp (fun x => u x - phi x) 2 μ := hu.1.2.1.sub
          (hp.continuous.memLp_of_hasCompactSupport hc)
        have hint1 := (memLp_two_iff_integrable_sq_norm hu_diff.aestronglyMeasurable).mp hu_diff
        have hint2 := (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
        have hsmall : ‖hd.toLp (fun x => du x - planarGradient phi x)‖ ^ 2 < (ε / B) ^ 2 := by
          rw [norm_sq]
          apply lt_of_le_of_lt (integral_mono hint2 (hint1.add hint2) ?_) herr
          intro x
          change ‖du x - planarGradient phi x‖ ^ 2 ≤ _
          change ‖du x - planarGradient phi x‖ ^ 2 ≤
            |u x - phi x| ^ 2 + ‖du x - planarGradient phi x‖ ^ 2
          exact le_add_of_nonneg_left (sq_nonneg _)
        have hsmall' : ‖hd.toLp (fun x => du x - planarGradient phi x)‖ < ε / B := by
          nlinarith [norm_nonneg (hd.toLp (fun x => du x - planarGradient phi x)), div_pos hε hB]
        have heq : inner ℝ (hq.toLp q) (hdu.toLp du) =
            inner ℝ (hq.toLp q) (hd.toLp (fun x => du x - planarGradient phi x)) := by
          rw [inner_eq, inner_eq]
          have hqi : Integrable (fun x => inner ℝ (q x) (du x)) μ := inner_int q du hq hdu
          have hqg : Integrable (fun x => inner ℝ (q x) (planarGradient phi x)) μ := inner_int q (planarGradient phi) hq hg
          simp_rw [inner_sub_right]
          rw [integral_sub hqi hqg, htest phi hp hc hs, sub_zero]
        rw [sub_zero, heq]
        calc
          |inner ℝ (hq.toLp q) (hd.toLp (fun x => du x - planarGradient phi x))| ≤
              ‖hq.toLp q‖ * ‖hd.toLp (fun x => du x - planarGradient phi x)‖ := abs_real_inner_le_norm _ _
          _ ≤ B * ‖hd.toLp (fun x => du x - planarGradient phi x)‖ :=
            mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (norm_nonneg _)
          _ < B * (ε / B) := mul_lt_mul_of_pos_left hsmall' hB
          _ = ε := mul_div_cancel₀ ε hB.ne'
      rw [inner_eq] at hzero
      exact hzero
    have inner_int {μ : Measure E2} (f g : E2 → E2) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
        Integrable (fun x => inner ℝ (f x) (g x)) μ := by
      apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
      filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
      rw [hfx, hgx]
    have grad_mem {μ : Measure E2} [IsFiniteMeasureOnCompacts μ]
        (phi : E2 → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
        MemLp (planarGradient phi) 2 μ := by
      apply memLp_finsetSum
      intro i hi
      have hh : MemLp (fun x => fderiv ℝ phi x (coordinateVector 2 i)) 2 μ :=
        ((hp.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
          (hc.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i))
      exact hh.continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector 2 i))
    have mean_grad (U : Set E2) (phi : E2 → ℝ) (hp : ContDiff ℝ ∞ phi)
        (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ U) (q : E2) :
        (∫ x in U, inner ℝ q (planarGradient phi x)) = 0 := by
      have hi (i : Fin 2) : Integrable (fun x => fderiv ℝ phi x (coordinateVector 2 i)) volume :=
        ((hp.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
          (hc.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i))
      have hz (i : Fin 2) : (∫ x in U, fderiv ℝ phi x (coordinateVector 2 i)) = 0 := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        · have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
            (f := fun _ : E2 => (1 : ℝ)) (g := phi) (v := coordinateVector 2 i)
            (by simp)
            (by simpa only [one_mul] using hi i)
            (by simpa only [one_mul] using hp.continuous.integrable_of_hasCompactSupport hc)
            (fun x _ => differentiableAt_const _) (fun x _ => hp.differentiable (by simp) x)
          simpa only [one_mul, fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, zero_mul,
            integral_zero, neg_zero] using hh
        · intro x hx
          exact image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ phi x (coordinateVector 2 i))
            (fun h => hx (hs (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i) h)))
      have hexp (x : E2) : inner ℝ q (planarGradient phi x) =
          ∑ i : Fin 2, q i * fderiv ℝ phi x (coordinateVector 2 i) := by
        delta planarGradient
        rw [inner_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [inner_smul_right]
        have he : inner ℝ q (coordinateVector 2 i) = q i := by
          delta coordinateVector
          simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul]
        rw [he, mul_comm]
      simp_rw [hexp]
      rw [integral_finsetSum Finset.univ (fun i hi' => (hi i).integrableOn.const_mul (q i))]
      simp only [integral_const_mul, hz, mul_zero, Finset.sum_const_zero]
    let E := (4 * (HN : ℝ) ^ 2 * Real.pi) / lam ^ 2
    refine ⟨E, by dsimp [E]; positivity, ?_⟩
    intro rho hrho hrhor a da hzero hda hweak
    let U := Metric.ball y rho
    let μ := volume.restrict U
    let d := fun x => da x - coordinateVector 2 0
    let flux := fun x => matrixAction (N x) (da x)
    let f := fun x => matrixAction (N y - N x) (coordinateVector 2 0)
    have hsub : U ⊆ Metric.ball y r1 := Metric.ball_subset_ball hrhor
    have hmu : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    letI := hmu
    have hdy : MemLp d 2 μ := hzero.1.2.2
    have hmem : ∀ᵐ x ∂μ, x ∈ U := ae_restrict_mem measurableSet_ball
    have hN (i j : Fin 2) : MemLp (fun x => N x i j) ∞ μ := by
      apply memLp_top_of_bound
        (((holder i j).continuousOn halpha).mono hsub |>.aestronglyMeasurable measurableSet_ball) Lambda
      filter_upwards [hmem] with x hx
      have hb := (bounds x (hsub hx) (coordinateVector 2 j)).2
      have he : matrixAction (N x) (coordinateVector 2 j) i = N x i j := by
        delta matrixAction coordinateVector
        simp only [Fin.sum_univ_two, EuclideanSpace.single_apply]
        fin_cases j <;> simp
      have hn : ‖coordinateVector 2 j‖ = 1 := by
        delta coordinateVector
        simp only [EuclideanSpace.norm_single, norm_one]
      have hcoord := PiLp.norm_apply_le (p := 2) (matrixAction (N x) (coordinateVector 2 j)) i
      rw [he] at hcoord
      exact hcoord.trans (by simpa only [hn, mul_one] using hb)
    have hflux : MemLp flux 2 μ := by
      have hc (i : Fin 2) : MemLp (fun x => ∑ j : Fin 2, N x i j * da x j) 2 μ := by
        apply memLp_finsetSum
        intro j hj
        exact (hN i j).mul (hda.eval_piLp j)
      have hv : MemLp (fun x => ∑ i : Fin 2,
          (∑ j : Fin 2, N x i j * da x j) • coordinateVector 2 i) 2 μ := by
        apply memLp_finsetSum
        intro i hi
        exact (hc i).continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector 2 i))
      convert hv using 1
      funext x
      ext k
      dsimp only [flux, matrixAction, coordinateVector]
      simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        EuclideanSpace.single_apply]
      fin_cases k <;> simp
    let c := matrixAction (N y) (coordinateVector 2 0)
    have hc : MemLp (fun _ : E2 => c) 2 μ := memLp_const c
    have hq : MemLp (fun x => flux x - c) 2 μ := hflux.sub hc
    have htest : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ U →
        (∫ x in U, inner ℝ (flux x - c) (planarGradient phi x)) = 0 := by
      intro phi hp hc' hs
      obtain ⟨hint, heq⟩ := hweak.2 phi hp hc' hs
      simp only [inner_zero_left, zero_mul, add_zero, sub_zero] at hint heq
      have hgi : IntegrableOn (fun x => inner ℝ c (planarGradient phi x)) U := by
        exact inner_int _ _ hc (grad_mem phi hp hc')
      simp_rw [inner_sub_left]
      rw [integral_sub hint hgi, heq, mean_grad U phi hp hc' hs c, sub_self]
    have heq := h10test U _ d _ hzero hq htest
    have hforce (x : E2) (hx : x ∈ U) : ‖f x‖ ≤ 2 * (HN : ℝ) * rho ^ (alpha : ℝ) := by
      have hy : y ∈ Metric.ball y r1 := Metric.mem_ball_self hr1
      have he (i : Fin 2) : f x i = N y i 0 - N x i 0 := by
        dsimp only [f, matrixAction, coordinateVector]
        simp only [Fin.sum_univ_two, EuclideanSpace.single_apply, Matrix.sub_apply]
        norm_num
      have hi (i : Fin 2) : |f x i| ≤ (HN : ℝ) * rho ^ (alpha : ℝ) := by
        have hh := (holder i 0).dist_le hy (hsub hx)
        rw [Real.dist_eq] at hh
        rw [he]
        exact hh.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow dist_nonneg
            (by have hh : dist x y < rho := hx; exact (by simpa only [dist_comm] using hh.le)) alpha.coe_nonneg)
          HN.coe_nonneg)
      have hn : ‖f x‖ ^ 2 = (f x 0) ^ 2 + (f x 1) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp only [Fin.sum_univ_two]
      have hb0 := hi 0
      have hb1 := hi 1
      have hk : 0 ≤ (HN : ℝ) * rho ^ (alpha : ℝ) := by positivity
      have h0 : (f x 0) ^ 2 ≤ ((HN : ℝ) * rho ^ (alpha : ℝ)) ^ 2 := by
        nlinarith [sq_abs (f x 0), abs_nonneg (f x 0)]
      have h1 : (f x 1) ^ 2 ≤ ((HN : ℝ) * rho ^ (alpha : ℝ)) ^ 2 := by
        nlinarith [sq_abs (f x 1), abs_nonneg (f x 1)]
      nlinarith [norm_nonneg (f x)]
    have hpoint (x : E2) (hx : x ∈ U) :
        lam ^ 2 * ‖d x‖ ^ 2 ≤ 2 * lam * inner ℝ (flux x - c) (d x) +
          (2 * (HN : ℝ) * rho ^ (alpha : ℝ)) ^ 2 := by
      have hvec : matrixAction (N x) (d x) = flux x - c + f x := by
        ext i
        dsimp only [d, flux, c, f, matrixAction]
        simp only [Fin.sum_univ_two, Matrix.sub_apply, PiLp.sub_apply, PiLp.add_apply]
        change N x i 0 * (da x 0 - coordinateVector 2 0 0) +
          N x i 1 * (da x 1 - coordinateVector 2 0 1) =
          (N x i 0 * da x 0 + N x i 1 * da x 1) -
          (N y i 0 * coordinateVector 2 0 0 + N y i 1 * coordinateVector 2 0 1) +
          ((N y i 0 - N x i 0) * coordinateVector 2 0 0 +
            (N y i 1 - N x i 1) * coordinateVector 2 0 1)
        ring
      have hb := (bounds x (hsub hx) (d x)).1
      rw [real_inner_comm, hvec, inner_add_left] at hb
      have hf := (abs_real_inner_le_norm (f x) (d x)).trans
        (mul_le_mul_of_nonneg_right (hforce x hx) (norm_nonneg (d x)))
      have hi : inner ℝ (f x) (d x) ≤ 2 * (HN : ℝ) * rho ^ (alpha : ℝ) * ‖d x‖ :=
        (le_abs_self _).trans hf
      have hbase : lam * ‖d x‖ ^ 2 ≤ inner ℝ (flux x - c) (d x) +
          2 * (HN : ℝ) * rho ^ (alpha : ℝ) * ‖d x‖ := by linarith
      have hm := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ 2 * lam)
      nlinarith [sq_nonneg (lam * ‖d x‖ - 2 * (HN : ℝ) * rho ^ (alpha : ℝ))]
    have henergy := (memLp_two_iff_integrable_sq_norm hdy.aestronglyMeasurable).mp hdy
    have hqi := inner_int _ _ hq hdy
    have hb := integral_mono_ae (henergy.const_mul (lam ^ 2))
      ((hqi.const_mul (2 * lam)).add (integrable_const _))
      (by filter_upwards [hmem] with x hx; exact hpoint x hx)
    change (∫ x, lam ^ 2 * ‖d x‖ ^ 2 ∂μ) ≤
      ∫ x, 2 * lam * inner ℝ (flux x - c) (d x) + (2 * (HN : ℝ) * rho ^ (alpha : ℝ)) ^ 2 ∂μ at hb
    rw [integral_const_mul, integral_add (hqi.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, smul_eq_mul] at hb
    rw [heq, mul_zero, zero_add] at hb
    have hvol : μ.real univ = rho ^ 2 * Real.pi := by
      dsimp [μ, U, Measure.real]
      rw [Measure.restrict_apply_univ, EuclideanSpace.volume_ball_fin_two,
        ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hrho.le,
        ENNReal.toReal_ofReal Real.pi_pos.le]
    rw [hvol] at hb
    have hpow : rho ^ (2 + 2 * (alpha : ℝ)) = rho ^ 2 * (rho ^ (alpha : ℝ)) ^ 2 := by
      rw [Real.rpow_add hrho]
      rw [Real.rpow_two]
      congr 1
      rw [mul_comm (2 : ℝ), Real.rpow_mul hrho.le, Real.rpow_two]
    change (∫ x, ‖d x‖ ^ 2 ∂μ) ≤ E * rho ^ (2 + 2 * (alpha : ℝ))
    rw [hpow]
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hlam)).mp
    calc
      lam ^ 2 * (∫ x, ‖d x‖ ^ 2 ∂μ) ≤
          (rho ^ 2 * Real.pi) * (2 * (HN : ℝ) * rho ^ (alpha : ℝ)) ^ 2 := hb
      _ = lam ^ 2 * (E * (rho ^ 2 * (rho ^ (alpha : ℝ)) ^ 2)) := by
        dsimp only [E]
        rw [← mul_assoc, mul_div_cancel₀ _ (sq_pos_of_pos hlam).ne']
        ring
  obtain ⟨r1, lam, Lambda, HN, hr1, hr1r, hr11, hlam, bounds, hholder⟩ := normalized_local
  obtain ⟨E, hE, henergy⟩ := energy_conditional G.alpha G.alpha_pos (normalizedInverse M)
    y r1 lam Lambda hr1 hlam HN bounds hholder
  refine ⟨r1, E, hr1, hr1r, hr11, hE, ?_⟩
  intro rho hrho hrhor a da ha
  exact henergy rho hrho hrhor a da ha.2.1 ha.1.2.2 ha.2.2

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower
