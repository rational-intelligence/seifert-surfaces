import InteriorPotentialData
import Lean
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
set_option autoImplicit false
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential
open SeifertSurfaces.AppendixACoordinates

/-- Whole-plane constancy of F4's homogeneous remainder, with its supplied
native weak gradient. Morrey printed150, planar remainder after (5.5.5);
the finite-q F4 blueprint and sealed exact residual fix this lower obligation.
No scalar global L2 or compact-gradient closure membership is assumed. -/
theorem native_planar_homogeneous_remainder_constant
    (A : Mat2) (lam Lambda : ℝ) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hSymmetric : ∀ i j : Fin 2, A i j = A j i)
    (hElliptic : ∀ t : E2,
      lam * ‖t‖ ^ 2 ≤ inner ℝ t (matrixAction A t) ∧
        ‖matrixAction A t‖ ≤ Lambda * ‖t‖)
    (W : E2 → ℝ) (dW : E2 → E2)
    (hWweak : WeakGradientOn Set.univ W dW)
    (hdW : MemLp dW 2 volume)
    (hWflux : ∀ psi : E2 → ℝ,
      ContDiff ℝ ∞ psi → HasCompactSupport psi →
        (∫ z, inner ℝ (matrixAction A (dW z)) (planarGradient psi z)) = 0) :
    ∃ c : ℝ, W =ᵐ[volume] (fun _ => c) := by
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let state ← Lean.Elab.Tactic.saveState
      let original ← Lean.getEnv
      Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory
        (← Lean.getEnv) `tactic r#"exact (by
  classical
  let e (i : Fin 2) : E2 := coordinateVector 2 i
  let a := A 0 0
  let b := A 0 1
  let c := A 1 1
  have hA10 : A 1 0 = b := hSymmetric 1 0
  have ha : 0 < a := by
    have h := (hElliptic (e 0)).1
    have he : ‖e 0‖ = 1 := by simp [e, coordinateVector]
    rw [he] at h
    simp [e, coordinateVector, matrixAction, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_two] at h
    exact hlam.trans_le h
  have hD : 0 < a*c-b^2 := by
    let v : E2 := -b • e 0 + a • e 1
    have hv : v ≠ 0 := by
      intro h
      have := congrArg (fun t : E2 => t 1) h
      simp [v, e, coordinateVector] at this
      exact ha.ne' this
    have hpos : 0 < inner ℝ v (matrixAction A v) :=
      (mul_pos hlam (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hElliptic v).1
    have heq : inner ℝ v (matrixAction A v) = a * (a*c-b^2) := by
      simp [v, e, coordinateVector, matrixAction, EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct, Fin.sum_univ_two, hA10, a, b, c]
      ring
    rw [heq] at hpos
    exact (mul_pos_iff_of_pos_left ha).mp hpos
  have hsmooth
      (g : Fin 2 → E2 → ℝ) (hg : ∀ i, ContDiff ℝ ∞ (g i))
      (hbdd : ∀ i, ∃ C : ℝ, ∀ x, ‖g i x‖ ≤ C)
      (hcurl : ∀ x, fderiv ℝ (g 1) x (coordinateVector 2 0) =
        fderiv ℝ (g 0) x (coordinateVector 2 1))
      (hdiv : ∀ x, a * fderiv ℝ (g 0) x (coordinateVector 2 0) +
        b * fderiv ℝ (g 1) x (coordinateVector 2 0) +
        b * fderiv ℝ (g 0) x (coordinateVector 2 1) +
        c * fderiv ℝ (g 1) x (coordinateVector 2 1) = 0) :
      ∀ x y i, g i x = g i y := by
    let s : ℝ := Real.sqrt (a*c-b^2)
    have hs : 0 < s := Real.sqrt_pos.2 hD
    have hs2 : s^2 = a*c-b^2 := Real.sq_sqrt hD.le
    let T : ℂ →L[ℝ] E2 :=
      Complex.reCLM.smulRight (a • coordinateVector 2 0 + b • coordinateVector 2 1) +
        Complex.imCLM.smulRight (s • coordinateVector 2 1)
    have hT (z : ℂ) : T z =
        (a*z.re) • coordinateVector 2 0 + (b*z.re+s*z.im) • coordinateVector 2 1 := by
      simp [T, add_smul, smul_add, smul_smul]
      module
    have hTsurj : Function.Surjective T := by
      intro x
      refine ⟨⟨x 0/a, (x 1-b*(x 0/a))/s⟩, ?_⟩
      rw [hT]
      ext i
      fin_cases i <;> simp [coordinateVector, ha.ne', hs.ne'] <;> field_simp <;> ring
    let F : ℂ → ℂ := fun z => (a*g 0 (T z)+b*g 1 (T z) : ℝ) -
      Complex.I * (s*g 1 (T z) : ℝ)
    have hFderiv (z : ℂ) : HasFDerivAt F
        ((Complex.ofRealCLM.comp
          (a • ((fderiv ℝ (g 0) (T z)).comp T) +
           b • ((fderiv ℝ (g 1) (T z)).comp T))) -
         Complex.I • Complex.ofRealCLM.comp
          (s • ((fderiv ℝ (g 1) (T z)).comp T))) z := by
      have h0 := ((hg 0).differentiable (by simp) (T z)).hasFDerivAt.comp z T.hasFDerivAt
      have h1 := ((hg 1).differentiable (by simp) (T z)).hasFDerivAt.comp z T.hasFDerivAt
      exact (Complex.ofRealCLM.hasFDerivAt.comp z
        ((h0.const_smul a).add (h1.const_smul b))).sub
        ((Complex.ofRealCLM.hasFDerivAt.comp z (h1.const_smul s)).const_smul Complex.I)
    have hF : Differentiable ℂ F := by
      intro z
      apply differentiableAt_complex_iff_differentiableAt_real.2
      refine ⟨(hFderiv z).differentiableAt, ?_⟩
      rw [(hFderiv z).fderiv]
      have hc := hcurl (T z)
      have hd := hdiv (T z)
      have hT1 : T 1 = a • coordinateVector 2 0 + b • coordinateVector 2 1 := by simp [T]
      have hTI : T Complex.I = s • coordinateVector 2 1 := by simp [T]
      apply Complex.ext <;>
        simp only [sub_apply, ContinuousLinearMap.comp_apply,
          smul_apply, add_apply,
          Complex.ofRealCLM_apply, hT1, hTI, map_add, map_smul, smul_eq_mul,
          Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          zero_mul, mul_zero, one_mul, add_zero, zero_add, sub_zero, zero_sub]
      · rw [hc]; ring
      · nlinarith [congrArg (fun t : ℝ => a*t) hd,
          congrArg (fun t : ℝ => t * fderiv ℝ (g 1) (T z) (coordinateVector 2 1)) hs2]
    have hFb : Bornology.IsBounded (Set.range F) := by
      obtain ⟨C0, h0⟩ := hbdd 0
      obtain ⟨C1, h1⟩ := hbdd 1
      apply isBounded_iff_forall_norm_le.2
      refine ⟨|a| * C0 + |b| * C1 + |s| * C1, ?_⟩
      rintro _ ⟨z, rfl⟩
      calc
        ‖F z‖ ≤ ‖(a*g 0 (T z)+b*g 1 (T z) : ℝ)‖ + ‖(s*g 1 (T z) : ℝ)‖ := by
          have h := norm_sub_le
            ((a*g 0 (T z)+b*g 1 (T z) : ℝ) : ℂ) (Complex.I * (s*g 1 (T z) : ℝ))
          simpa only [F, norm_mul, Complex.norm_I, one_mul, Complex.norm_real] using h
        _ ≤ |a| * ‖g 0 (T z)‖ + |b| * ‖g 1 (T z)‖ + |s| * ‖g 1 (T z)‖ := by
          simp only [norm_mul, Real.norm_eq_abs]
          simpa only [abs_mul] using add_le_add (abs_add_le (a*g 0 (T z)) (b*g 1 (T z))) (le_refl (|s| * |g 1 (T z)|))
        _ ≤ _ := by gcongr <;> apply_assumption
    intro x y i
    obtain ⟨z, rfl⟩ := hTsurj x
    obtain ⟨w, rfl⟩ := hTsurj y
    have heq := hF.apply_eq_apply_of_bounded hFb z w
    have hr := congrArg Complex.re heq
    have hi := congrArg Complex.im heq
    simp [F, hs.ne'] at hr hi
    have h1 : g 1 (T z) = g 1 (T w) := hi
    fin_cases i
    · change g 0 (T z) = g 0 (T w)
      rw [h1] at hr
      exact (mul_left_cancel₀ ha.ne') (add_right_cancel hr)
    · exact h1
  have hWi : LocallyIntegrable W volume := locallyIntegrableOn_univ.mp hWweak.1
  have hdWi (i : Fin 2) : MemLp (fun z => dW z i) 2 volume :=
    hdW.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
  have hweak (phi : E2 → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
      (i : Fin 2) :
      (∫ z, W z * fderiv ℝ phi z (e i)) = -(∫ z, dW z i * phi z) := by
    simpa [e] using hWweak.2.2 phi hp hc (Set.subset_univ _) i
  have hkernel_compact (k : E2 → ℝ) (hc : HasCompactSupport k) (x : E2) :
      HasCompactSupport (fun z => k (x-z)) := by
    let T : Homeomorph E2 E2 := (Homeomorph.neg E2).trans (Homeomorph.addLeft x)
    simpa [T, Function.comp_def, sub_eq_add_neg] using hc.comp_homeomorph T
  have hkernel_deriv (k : E2 → ℝ) (hk : ContDiff ℝ ∞ k) (x z : E2) (i : Fin 2) :
      fderiv ℝ (fun z => k (x-z)) z (e i) = -fderiv ℝ k (x-z) (e i) := by
    have h := (hk.differentiable (by simp) (x-z)).hasFDerivAt.comp z
      ((hasFDerivAt_const x z).sub (hasFDerivAt_id z))
    change HasFDerivAt (fun z => k (x-z)) _ z at h
    simp [h.fderiv]
  have hmollify (k : E2 → ℝ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
      let U := convolution W k (ContinuousLinearMap.lsmul ℝ ℝ) volume
      let g := fun i : Fin 2 => convolution (fun z => dW z i) k
        (ContinuousLinearMap.lsmul ℝ ℝ) volume
      ContDiff ℝ ∞ U ∧ (∀ i, ContDiff ℝ ∞ (g i)) ∧
      (∀ x i, fderiv ℝ U x (e i) = g i x) ∧
      (∀ i, ∃ C : ℝ, ∀ x, ‖g i x‖ ≤ C) ∧
      (∀ x, fderiv ℝ (g 1) x (e 0) = fderiv ℝ (g 0) x (e 1)) ∧
      (∀ x, a*fderiv ℝ (g 0) x (e 0) + b*fderiv ℝ (g 1) x (e 0) +
        b*fderiv ℝ (g 0) x (e 1) + c*fderiv ℝ (g 1) x (e 1) = 0) := by
    dsimp only
    let U := convolution W k (ContinuousLinearMap.lsmul ℝ ℝ) volume
    let g := fun i : Fin 2 => convolution (fun z => dW z i) k
      (ContinuousLinearMap.lsmul ℝ ℝ) volume
    have hU : ContDiff ℝ ∞ U :=
      hkc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hWi hk
    have hg (i : Fin 2) : ContDiff ℝ ∞ (g i) :=
      hkc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
        ((hdWi i).locallyIntegrable (by norm_num)) hk
    have hUg (x : E2) (i : Fin 2) : fderiv ℝ U x (e i) = g i x := by
      rw [(hkc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
        hWi (hk.of_le (by simp)) x).fderiv]
      rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hWi
        (hkc.fderiv ℝ) (hk.continuous_fderiv (by simp))]
      change (∫ z, W z * fderiv ℝ k (x-z) (e i)) = ∫ z, dW z i * k (x-z)
      have h := hweak (fun z => k (x-z)) (hk.comp (contDiff_const.sub contDiff_id))
        (hkernel_compact k hkc x) i
      simp only [hkernel_deriv k hk x, mul_neg, integral_neg, neg_inj] at h
      exact h
    have hb (i : Fin 2) : ∃ C : ℝ, ∀ x, ‖g i x‖ ≤ C := by
      have hklp : MemLp k 2 volume := hk.continuous.memLp_of_hasCompactSupport hkc
      let B := ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ * eLpNorm (fun z => dW z i) 2 volume *
        eLpNorm k 2 volume
      have hB : B ≠ ⊤ := ENNReal.mul_ne_top
        (ENNReal.mul_ne_top enorm_ne_top (hdWi i).eLpNorm_lt_top.ne) hklp.eLpNorm_lt_top.ne
      refine ⟨B.toReal, fun x => ?_⟩
      have h := enorm_convolution_le (ContinuousLinearMap.lsmul ℝ ℝ)
        (p := 2) (q := 2) (hdWi i).aestronglyMeasurable hklp.aestronglyMeasurable x
      exact (show ‖g i x‖ₑ.toReal ≤ B.toReal from ENNReal.toReal_mono hB h)
    have hcurl (x : E2) : fderiv ℝ (g 1) x (e 0) = fderiv ℝ (g 0) x (e 1) := by
      have heq (i : Fin 2) : g i = fun x => fderiv ℝ U x (e i) := by
        funext x
        exact (hUg x i).symm
      rw [heq 0, heq 1]
      have hDU : Differentiable ℝ (fderiv ℝ U) :=
        (hU.fderiv_right (m := 1) (by simp)).differentiable (by simp)
      rw [fderiv_clm_apply (hDU x) (differentiableAt_const _),
        fderiv_clm_apply (hDU x) (differentiableAt_const _)]
      simpa using hU.contDiffAt.isSymmSndFDerivAt (by simp) (e 0) (e 1)
    have hDg (x : E2) (i j : Fin 2) : fderiv ℝ (g i) x (e j) =
        ∫ z, dW z i * fderiv ℝ k (x-z) (e j) := by
      rw [(hkc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
        ((hdWi i).locallyIntegrable (by norm_num)) (hk.of_le (by simp)) x).fderiv]
      rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ)
        ((hdWi i).locallyIntegrable (by norm_num)) (hkc.fderiv ℝ)
        (hk.continuous_fderiv (by simp))]
      rfl
    have hInt (x : E2) (i j : Fin 2) :
        Integrable (fun z => dW z i * fderiv ℝ k (x-z) (e j)) :=
      (hkc.fderiv_apply ℝ (e j)).convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
        ((hdWi i).locallyIntegrable (by norm_num))
        ((hk.continuous_fderiv (by simp)).clm_apply continuous_const) x
    refine ⟨hU, hg, hUg, hb, hcurl, ?_⟩
    intro x
    have hflux := hWflux (fun z => k (x-z))
      (hk.comp (contDiff_const.sub contDiff_id)) (hkernel_compact k hkc x)
    have heq : (fun z => inner ℝ (matrixAction A (dW z)) (planarGradient (fun z => k (x-z)) z)) =
        fun z => -(a*(dW z 0*fderiv ℝ k (x-z) (e 0)) +
          b*(dW z 1*fderiv ℝ k (x-z) (e 0)) +
          b*(dW z 0*fderiv ℝ k (x-z) (e 1)) +
          c*(dW z 1*fderiv ℝ k (x-z) (e 1))) := by
      funext z
      simp only [planarGradient, Fin.sum_univ_two]
      change inner ℝ (matrixAction A (dW z))
        (fderiv ℝ (fun z => k (x-z)) z (e 0) • e 0 +
         fderiv ℝ (fun z => k (x-z)) z (e 1) • e 1) = _
      rw [hkernel_deriv k hk, hkernel_deriv k hk]
      simp [e, coordinateVector, matrixAction, EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct, Fin.sum_univ_two, hA10, a, b, c]
      ring
    rw [heq, integral_neg] at hflux
    simp only [neg_eq_zero] at hflux
    have h0 := (hInt x 0 0).const_mul a
    have h1 := (hInt x 1 0).const_mul b
    have h2 := (hInt x 0 1).const_mul b
    have h3 := (hInt x 1 1).const_mul c
    have hsum3 := integral_add ((h0.add h1).add h2) h3
    have hsum2 := integral_add (h0.add h1) h2
    have hsum1 := integral_add h0 h1
    simp only [Pi.add_apply] at hsum3 hsum2 hsum1
    rw [hsum3, hsum2, hsum1] at hflux
    simp only [g] at hDg
    simpa only [integral_const_mul, hDg] using hflux
  let delta : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hdelta (n : ℕ) : 0 < delta n := by dsimp [delta]; positivity
  let bump (n : ℕ) : ContDiffBump (0 : E2) :=
    ⟨delta n/2, delta n, half_pos (hdelta n), half_lt_self (hdelta n)⟩
  let k (n : ℕ) : E2 → ℝ := (bump n).normed volume
  have hk (n : ℕ) : ContDiff ℝ ∞ (k n) := (bump n).contDiff_normed
  have hkc (n : ℕ) : HasCompactSupport (k n) := (bump n).hasCompactSupport_normed
  have hdelta_lim : Filter.Tendsto delta Filter.atTop (𝓝 0) := by
    exact Filter.Tendsto.const_div_atTop
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop) 1
  have happrox (f : E2 → ℝ) (hf : LocallyIntegrable f volume) : ∀ᵐ x ∂volume,
      Filter.Tendsto (fun n => convolution f (k n) (ContinuousLinearMap.lsmul ℝ ℝ) volume x)
        Filter.atTop (𝓝 (f x)) := by
    have hflip : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip =
        ContinuousLinearMap.lsmul ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      exact mul_comm v u
    have hswap (n : ℕ) : convolution f (k n) (ContinuousLinearMap.lsmul ℝ ℝ) volume =
        convolution (k n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      convolution_symm _ hflip
    simpa only [hswap, k] using
      (ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
        (φ := bump) hdelta_lim (K := 2) (Filter.Eventually.of_forall (fun n => by dsimp [bump]; linarith)) hf)
  let g (n : ℕ) (i : Fin 2) : E2 → ℝ :=
    convolution (fun z => dW z i) (k n) (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hgc (n : ℕ) : ∀ x y i, g n i x = g n i y := by
    obtain ⟨hU, hg, hUg, hb, hcurl, hdiv⟩ := hmollify (k n) (hk n) (hkc n)
    exact hsmooth (g n) hg hb hcurl hdiv
  have hglim : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      Filter.Tendsto (fun n => g n i x) Filter.atTop (𝓝 (dW x i)) := by
    exact ae_all_iff.mpr (fun i => happrox (fun z => dW z i)
      ((hdWi i).locallyIntegrable (by norm_num)))
  obtain ⟨x0, hx0⟩ := hglim.exists
  have hdconst : dW =ᵐ[volume] (fun _ => dW x0) := by
    filter_upwards [hglim] with x hx
    ext i
    apply tendsto_nhds_unique (hx i)
    have heq : (fun n => g n i x) = (fun n => g n i x0) := funext (fun n => hgc n x x0 i)
    rw [heq]
    exact hx0 i
  have hd0 : dW x0 = 0 := by
    have hLp : MemLp (fun _ : E2 => dW x0) 2 volume := MemLp.ae_eq hdconst hdW
    have h := (memLp_const_iff (by norm_num) (by norm_num)).mp hLp
    simpa only [measure_univ_of_isAddLeftInvariant, lt_self_iff_false, or_false] using h
  have hdzero : dW =ᵐ[volume] (fun _ => 0) := by simpa only [hd0] using hdconst
  let U (n : ℕ) : E2 → ℝ := convolution W (k n) (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hUc (n : ℕ) : ∀ x y, U n x = U n y := by
    obtain ⟨hU, hg, hUg, hb, hcurl, hdiv⟩ := hmollify (k n) (hk n) (hkc n)
    apply is_const_of_fderiv_eq_zero (hU.differentiable (by simp))
    intro x
    have hcoord (i : Fin 2) : fderiv ℝ (U n) x (e i) = 0 := by
      rw [hUg]
      change (∫ z, dW z i * k n (x-z)) = 0
      trans ∫ z : E2, (0 : ℝ)
      · apply integral_congr_ae
        filter_upwards [hdzero] with z hz
        simp [hz]
      · simp
    ext v
    have hv : v = v 0 • e 0 + v 1 • e 1 := by
      ext i
      fin_cases i <;> simp [e, coordinateVector]
    conv_lhs => rw [hv]
    simp only [U] at hcoord
    simp only [map_add, map_smul, hcoord, smul_zero, add_zero, zero_apply]
  have hUlim := happrox W hWi
  obtain ⟨y0, hy0⟩ := hUlim.exists
  refine ⟨W y0, ?_⟩
  filter_upwards [hUlim] with x hx
  apply tendsto_nhds_unique hx
  change Filter.Tendsto (fun n => U n x) Filter.atTop (𝓝 (W y0))
  have heq : (fun n => U n x) = (fun n => U n y0) := funext (fun n => hUc n x y0)
  rw [heq]
  exact hy0

)"#))
      let result ← Lean.instantiateMVars (Lean.mkMVar goal)
      let result ← Lean.Core.transform result (pre := fun expr => do
        match expr with
        | .const name levels =>
          if (original.find? name).isSome then return .continue
          let info ← Lean.getConstInfo name
          let some value := info.value? (allowOpaque := true) |
            Lean.throwError "new auxiliary has no body: {name}"
          return .visit (value.instantiateLevelParams info.levelParams levels)
        | _ => return .continue)
      state.restore
      Lean.Meta.checkWithKernel result
      goal.assign result
      Lean.Elab.Tactic.replaceMainGoal []

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential
