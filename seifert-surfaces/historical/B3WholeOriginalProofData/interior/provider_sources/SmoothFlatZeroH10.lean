import NativeBoundaryToolbox
import SmoothTransitionDerivativeBounds
set_option maxHeartbeats 5000000
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.AppendixACoordinates

theorem smooth_flat_zero_h10 (r : ℝ) (psi : E2 → ℝ) (hs : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (ht : tsupport psi ⊆ disc r)
    (hflat : ∀ y : E2, y 1 = 0 → psi y = 0) :
    H10On (halfDisc r) psi (planarGradient psi) := by
  classical
  let U := halfDisc r
  have smooth (φ : E2 → ℝ) (hs : ContDiff ℝ ∞ φ)
      (hc : HasCompactSupport φ) :
      H1On U φ (planarGradient φ) := by
      classical
      have hgcont : Continuous (planarGradient φ) := continuous_planarGradient hs
      have hgcompact : HasCompactSupport (planarGradient φ) := by
        apply hc.of_isClosed_subset (isClosed_tsupport _)
        apply closure_minimal _ (isClosed_tsupport φ)
        intro x hx
        by_contra h
        exact hx (planarGradient_eq_zero_off_support φ h)
      have huLp : MemLp φ 2 (volume.restrict (U)) :=
        (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict _
      have hgLp : MemLp (planarGradient φ) 2 (volume.restrict (U)) :=
        (hgcont.memLp_of_hasCompactSupport (μ := volume) hgcompact).restrict _
      refine ⟨?_, huLp, hgLp⟩
      refine ⟨hs.continuous.locallyIntegrable.locallyIntegrableOn _,
        hgcont.locallyIntegrable.locallyIntegrableOn _, ?_⟩
      intro ψ hψ hcψ htψ i
      have hcoord (x : E2) : planarGradient φ x i = fderiv ℝ φ x (coordinateVector 2 i) := by
        fin_cases i <;> simp [planarGradient, Fin.sum_univ_two, coordinateVector]
      have hdψ : Continuous (fun x => fderiv ℝ ψ x (coordinateVector 2 i)) :=
        (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
      have hdφ : Continuous (fun x => fderiv ℝ φ x (coordinateVector 2 i)) :=
        (hs.continuous_fderiv (by simp)).clm_apply continuous_const
      have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
        ((hdφ.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left)
        ((hs.continuous.mul hdψ).integrable_of_hasCompactSupport (hcψ.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i)).mul_left)
        ((hs.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left)
        (fun x _ => hs.differentiable (by simp) x)
        (fun x _ => hψ.differentiable (by simp) x)
      simp_rw [hcoord]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
        setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact hi
      · intro x hx
        rw [show ψ x = 0 from image_eq_zero_of_notMem_tsupport (fun h => hx (htψ h)), mul_zero]
      · intro x hx
        have hdsub : tsupport (fun x => fderiv ℝ ψ x (coordinateVector 2 i)) ⊆ U :=
          (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans htψ
        rw [show fderiv ℝ ψ x (coordinateVector 2 i) = 0 from
          image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ ψ x (coordinateVector 2 i))
            (fun h => hx (hdsub h)), mul_zero]
  refine ⟨smooth psi hs hc,?_⟩
  obtain ⟨D,hD⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hs.continuous_fderiv (by simp))
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hgcompact : HasCompactSupport (planarGradient psi) := by
    apply hc.mono'
    intro y hy
    by_contra hn
    exact hy (planarGradient_eq_zero_off_support psi hn)
  obtain ⟨G,hG⟩ := hgcompact.exists_bound_of_continuous (continuous_planarGradient hs)
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hs.continuous
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨C,hC0,hC,hCs⟩ := transition_derivative_bounds
  have hpsiFlatBound (y : E2) : |psi y| ≤ D * |y 1| := by
    let z : E2 := y - y 1 • coordinateVector 2 1
    have hz : z 1 = 0 := by simp [z,coordinateVector]
    have hn : ‖y - z‖ = |y 1| := by simp [z,coordinateVector,norm_smul,Real.norm_eq_abs]
    have hb := (convex_univ : Convex ℝ (univ : Set E2)).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hs.differentiable (by simp) x) (fun x _ => hD x)
      (mem_univ z) (mem_univ y)
    simpa only [hflat z hz,sub_zero,Real.norm_eq_abs,hn] using hb
  let k : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hk (n : ℕ) : 0 < k n := by dsimp [k]; positivity
  let chi : ℕ → E2 → ℝ := fun n y => Real.smoothTransition (k n * y 1 - 1)
  let phi : ℕ → E2 → ℝ := fun n y => chi n y * psi y
  have hχs (n : ℕ) : ContDiff ℝ ∞ (chi n) :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff).sub contDiff_const)
  have hφs (n : ℕ) : ContDiff ℝ ∞ (phi n) := (hχs n).mul hs
  have hφc (n : ℕ) : HasCompactSupport (phi n) := hc.mul_left
  have hφt (n : ℕ) : tsupport (phi n) ⊆ U := by
    have hsup : tsupport (phi n) ⊆ {y : E2 | (k n)⁻¹ ≤ y 1} := by
      apply closure_minimal _ (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
      intro y hy
      have hχ : chi n y ≠ 0 := by intro hn; exact hy (by simp [phi,hn])
      have hpos : 0 < k n * y 1 - 1 := by
        exact lt_of_not_ge (fun hz => hχ (Real.smoothTransition.zero_of_nonpos hz))
      rw [← one_div]
      exact (div_le_iff₀ (hk n)).mpr (by change 1 ≤ y 1 * k n; nlinarith)
    intro y hy
    exact ⟨ht ((tsupport_mul_subset_right (f := chi n) (g := psi)) hy),
      (inv_pos.mpr (hk n)).trans_le (hsup hy)⟩
  have hgradχ (n : ℕ) (y : E2) : planarGradient (chi n) y =
      (k n * deriv Real.smoothTransition (k n * y 1 - 1)) • coordinateVector 2 1 := by
    have hτ : Differentiable ℝ Real.smoothTransition :=
      (show ContDiff ℝ ∞ Real.smoothTransition from Real.smoothTransition.contDiff).differentiable (by simp)
    have hd := (hτ _).hasDerivAt.comp_hasFDerivAt y
      (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.const_mul (k n)).sub_const 1)
    have hf : fderiv ℝ (chi n) y = deriv Real.smoothTransition (k n * y 1 - 1) •
        (k n • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) := hd.fderiv
    unfold planarGradient
    rw [hf]
    ext i
    fin_cases i <;> simp [coordinateVector,Fin.sum_univ_two,mul_comm]
  have hprod (n : ℕ) (y : E2) : planarGradient (phi n) y =
      chi n y • planarGradient psi y + psi y • planarGradient (chi n) y := by
    unfold phi planarGradient
    rw [fderiv_fun_mul ((hχs n).differentiable (by simp) y) (hs.differentiable (by simp) y)]
    simp only [Fin.sum_univ_two,add_apply,smul_apply,smul_eq_mul,add_smul,mul_smul,smul_add]
    exact add_add_add_comm _ _ _ _
  have hχbound (n : ℕ) (y : E2) : 0 ≤ chi n y ∧ chi n y ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  have hterm (n : ℕ) (y : E2) (hy : y ∈ U) :
      ‖psi y • planarGradient (chi n) y‖ ≤ 2 * D * C := by
    rw [hgradχ,norm_smul,norm_smul]
    have hn : ‖coordinateVector 2 1‖ = 1 := by simp [coordinateVector]
    rw [hn,mul_one,Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_of_pos (hk n)]
    by_cases hz : deriv Real.smoothTransition (k n * y 1 - 1) = 0
    · rw [hz,abs_zero,mul_zero,mul_zero]
      positivity
    · have hb := hCs _ hz
      have hypos : 0 < y 1 := hy.2
      have hpy := hpsiFlatBound y
      rw [abs_of_pos hypos] at hpy
      have h0 : 0 ≤ k n * |deriv Real.smoothTransition (k n * y 1 - 1)| := by positivity
      calc
        _ ≤ (D * y 1) * (k n * |deriv Real.smoothTransition (k n * y 1 - 1)|) :=
          mul_le_mul_of_nonneg_right hpy h0
        _ ≤ (D * y 1) * (k n * C) := by gcongr; exact hC _
        _ ≤ 2 * D * C := by nlinarith [mul_nonneg hD0 hC0,mul_le_mul_of_nonneg_right hb.2 (mul_nonneg hD0 hC0)]
  have hscalar (n : ℕ) (y : E2) : |psi y - phi n y| ≤ B := by
    have hχ := hχbound n y
    have hh : |1 - chi n y| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    calc
      _ = |1-chi n y| * |psi y| := by rw [← abs_mul]; congr 1; dsimp [phi]; ring
      _ ≤ 1 * B := mul_le_mul hh (by simpa only [Real.norm_eq_abs] using hB y) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hvector (n : ℕ) (y : E2) (hy : y ∈ U) :
      ‖planarGradient psi y - planarGradient (phi n) y‖ ≤ G + 2*D*C := by
    have hχ := hχbound n y
    have hh : |1-chi n y| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    have he : planarGradient psi y - planarGradient (phi n) y =
        (1-chi n y) • planarGradient psi y - psi y • planarGradient (chi n) y := by
      rw [hprod,sub_smul,one_smul,sub_add_eq_sub_sub]
    rw [he]
    calc
      _ ≤ ‖(1-chi n y) • planarGradient psi y‖ + ‖psi y • planarGradient (chi n) y‖ := norm_sub_le _ _
      _ ≤ G + 2*D*C := by
        apply add_le_add _ (hterm n y hy)
        rw [norm_smul,Real.norm_eq_abs]
        exact (mul_le_mul hh (hG y) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  let error : ℕ → E2 → ℝ := fun n y => |psi y-phi n y|^2 + ‖planarGradient psi y-planarGradient (phi n) y‖^2
  let K : ℝ := B^2+(G+2*D*C)^2
  have hUbd : Bornology.IsBounded U := (isCompact_closedBall (0 : E2) r).isBounded.subset (fun y hy => Metric.ball_subset_closedBall hy.1)
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUbd.measure_lt_top.ne
  have hUmeas : MeasurableSet U := by
    dsimp [U]; unfold halfDisc disc
    exact (Metric.isOpen_ball.inter (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  have hlim : Tendsto (fun n => ∫ y in U, error n y) atTop (𝓝 0) := by
    have hχevent (y : E2) (hy : y ∈ U) : ∀ᶠ n in atTop,
        chi n y = 1 ∧ planarGradient (chi n) y = 0 := by
      obtain ⟨N,hN⟩ := exists_nat_gt (3 / y 1)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hypos : 0 < y 1 := hy.2
      have hkn : 3 < k n * y 1 := by
        have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
        have hh := (div_lt_iff₀ hypos).mp hN
        dsimp [k]
        nlinarith
      refine ⟨Real.smoothTransition.one_of_one_le (by linarith),?_⟩
      rw [hgradχ]
      have hd : deriv Real.smoothTransition (k n * y 1 - 1) = 0 := by
        by_contra hh
        have hb := (hCs _ hh).2
        linarith
      rw [hd,mul_zero,zero_smul]
    have hdct := tendsto_integral_of_dominated_convergence (μ := volume.restrict U) (F := error) (f := fun _ => (0 : ℝ))
      (fun _ => K) (fun n => by
        change AEStronglyMeasurable (error n) (volume.restrict U)
        apply Continuous.aestronglyMeasurable
        exact ((hs.continuous.sub (hφs n).continuous).abs.pow 2).add
          (((continuous_planarGradient hs).sub (continuous_planarGradient (hφs n))).norm.pow 2))
      (integrable_const K) (fun n => by
        filter_upwards [ae_restrict_mem hUmeas] with y hy
        change ‖error n y‖ ≤ K
        rw [Real.norm_of_nonneg (by dsimp [error]; positivity)]
        change |psi y-phi n y|^2 + ‖planarGradient psi y-planarGradient (phi n) y‖^2 ≤ K
        exact add_le_add ((sq_le_sq₀ (abs_nonneg _) hB0).mpr (hscalar n y))
          ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hvector n y hy)))
      (by
        filter_upwards [ae_restrict_mem hUmeas] with y hy
        apply tendsto_const_nhds.congr'
        filter_upwards [hχevent y hy] with n hn
        simp [error,phi,hn.1,hprod,hn.2])
    simpa using hdct
  intro eps heps
  obtain ⟨n,hn⟩ := (hlim.eventually_lt_const heps).exists
  exact ⟨phi n,hφs n,hφc n,hφt n,hn⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
