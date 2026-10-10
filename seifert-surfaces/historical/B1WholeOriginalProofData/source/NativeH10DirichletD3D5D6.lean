import NativeH10DirichletD1D2

noncomputable section
set_option autoImplicit false
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
open SeifertSurfaces.AppendixACoordinates

/-- D3: one zero-boundary Poincaré constant, for all centers and positive radii. -/
theorem nativeH10_pair_poincare :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : E2) (rho : ℝ), 0 < rho →
      ∀ p : X (Metric.ball y rho),
        ‖p‖ ^ 2 ≤ (1 + C * rho ^ 2) * ‖gradLp (Metric.ball y rho) p‖ ^ 2 := by
  classical
  let K : ℝ≥0 := eLpNormLESNormFDerivOneConst (volume : Measure E2) 2
  let V : ℝ := (volume (Metric.ball (0 : E2) 1)).toReal
  let C : ℝ := 1 + (K : ℝ) ^ 2 * V
  have hC : 0 < C := by
    dsimp [C, V]
    positivity
  refine ⟨C, hC, ?_⟩
  intro y rho hrho p
  let U := Metric.ball y rho
  have hgrad (φ : E2 → ℝ) (x : E2) :
      ‖planarGradient φ x‖ = ‖fderiv ℝ φ x‖ := by
    let L := fderiv ℝ φ x
    let g := (InnerProductSpace.toDual ℝ E2).symm L
    have hg : g = planarGradient φ x := by
      have hL : (InnerProductSpace.toDual ℝ E2) g = L := by simp [g]
      ext i
      have hi : g i = L (EuclideanSpace.single i 1) := by
        rw [← hL, InnerProductSpace.toDual_apply_apply]
        simpa using (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) g).symm
      fin_cases i <;> simpa [planarGradient, coordinateVector, L] using hi
    rw [← hg]
    exact (InnerProductSpace.toDual ℝ E2).symm.norm_map L
  have hvol : (volume U).toReal = rho ^ 2 * V := by
    have hs := Measure.addHaar_ball_of_pos (volume : Measure E2) y hrho
    simp only [E2, finrank_euclideanSpace, Fintype.card_fin] at hs
    dsimp [U, V]
    rw [hs, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg rho)]
  have hsmooth (q : Pair U) (hq : q ∈ SmoothGraph U) :
      ‖q.fst‖ ^ 2 ≤ C * rho ^ 2 * ‖q.snd‖ ^ 2 := by
    obtain ⟨φ, hu, hg, hs, hc, ht, rfl⟩ := hq
    have hd : AEStronglyMeasurable (fderiv ℝ φ) volume :=
      (hs.continuous_fderiv (by simp)).aestronglyMeasurable
    have hs1 : ContDiff ℝ 1 φ := hs.of_le (by simp)
    have hsob := eLpNorm_le_eLpNorm_fderiv_one (volume : Measure E2) hs1 hc
      (p := 2) (by simpa [E2] using NNReal.HolderConjugate.two_two)
    have hder : eLpNorm (fderiv ℝ φ) 1 volume =
        eLpNorm (planarGradient φ) 1 (volume.restrict U) := by
      rw [← eLpNorm_restrict_eq_of_support_subset hd
        ((support_fderiv_subset ℝ).trans ht)]
      exact eLpNorm_congr_norm_ae hd.restrict hg.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => (hgrad φ x).symm)
    rw [hder] at hsob
    have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (p := 1) (q := 2) (by norm_num) hg.aestronglyMeasurable
    have hb : eLpNorm φ 2 (volume.restrict U) ≤
        K * (eLpNorm (planarGradient φ) 2 (volume.restrict U) *
          (volume U) ^ (1 / 2 : ℝ)) := by
      rw [eLpNorm_restrict_eq_of_support_subset hs.continuous.aestronglyMeasurable
        ((subset_tsupport φ).trans ht)]
      apply hsob.trans
      change (K : ℝ≥0∞) * _ ≤ K * _
      gcongr
      convert hcmp using 1
      norm_num
    have hfinite :
        (K : ℝ≥0∞) * (eLpNorm (planarGradient φ) 2 (volume.restrict U) *
          (volume U) ^ (1 / 2 : ℝ)) ≠ ⊤ := by
      finiteness
    have hr := ENNReal.toReal_mono hfinite hb
    have hnorm : ‖hu.toLp φ‖ ≤ (K : ℝ) *
        (‖hg.toLp (planarGradient φ)‖ * Real.sqrt (volume U).toReal) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hr
      simpa only [Lp.norm_toLp, ENNReal.coe_toReal, Real.sqrt_eq_rpow] using hr
    have hsq := sq_le_sq₀ (norm_nonneg (hu.toLp φ)) (by positivity) |>.2 hnorm
    have hroot := Real.sq_sqrt (ENNReal.toReal_nonneg (a := volume U))
    change ‖hu.toLp φ‖ ^ 2 ≤ C * rho ^ 2 * ‖hg.toLp (planarGradient φ)‖ ^ 2
    rw [mul_pow, mul_pow, hroot, hvol] at hsq
    dsimp [C]
    nlinarith [sq_nonneg rho, sq_nonneg ‖hg.toLp (planarGradient φ)‖,
      mul_nonneg (sq_nonneg rho) (sq_nonneg ‖hg.toLp (planarGradient φ)‖)]
  have hclosed : IsClosed {q : Pair U |
      ‖q.fst‖ ^ 2 ≤ C * rho ^ 2 * ‖q.snd‖ ^ 2} :=
    isClosed_le ((WithLp.fstL 2 ℝ (Lp ℝ 2 (volume.restrict U))
      (Lp E2 2 (volume.restrict U))).continuous.norm.pow 2)
      (continuous_const.mul ((WithLp.sndL 2 ℝ (Lp ℝ 2 (volume.restrict U))
        (Lp E2 2 (volume.restrict U))).continuous.norm.pow 2))
  have hspace : (space U : Set (Pair U)) = closure (SmoothGraph U) := by
    rw [Submodule.topologicalClosure_coe, smoothGraph_span y rho hrho]
  have hp : p.val ∈ closure (SmoothGraph U) := by
    rw [← hspace]
    exact p.property
  have hineq := closure_minimal hsmooth hclosed hp
  change ‖p.val.fst‖ ^ 2 ≤ C * rho ^ 2 * ‖p.val.snd‖ ^ 2 at hineq
  have hnorm := WithLp.prod_norm_sq_eq_of_L2 p.val
  change ‖p.val‖ ^ 2 ≤ (1 + C * rho ^ 2) * ‖p.val.snd‖ ^ 2
  nlinarith


/-- D5: generic bounded affine variational data on the native L²-pair space. -/
theorem nativeH10_affine_form_data
    (y : E2) (rho : ℝ) (hrho : 0 < rho)
    (N : E2 → Mat2) (lam K P : ℝ)
    (hlam : 0 < lam) (hK : 0 < K) (hP0 : 0 ≤ P)
    (hN : ∀ i j : Fin 2, AEStronglyMeasurable (fun x => N x i j)
      (volume.restrict (Metric.ball y rho)))
    (hbound : ∀ x ∈ Metric.ball y rho, ∀ v : E2,
      lam * ‖v‖ ^ 2 ≤ inner ℝ (matrixAction (N x) v) v ∧
      ‖matrixAction (N x) v‖ ≤ K * ‖v‖)
    (hP : ∀ p : X (Metric.ball y rho),
      ‖p‖ ^ 2 ≤ (1 + P * rho ^ 2) * ‖gradLp (Metric.ball y rho) p‖ ^ 2) :
    ∃ B : X (Metric.ball y rho) →L[ℝ] X (Metric.ball y rho) →L[ℝ] ℝ,
    ∃ ell : X (Metric.ball y rho) →L[ℝ] ℝ,
      (∀ p q, B p q = b (Metric.ball y rho) N p q) ∧
      (∀ q, ell q = load (Metric.ball y rho) N q) ∧
      (∀ g h : E2 → E2,
        MemLp g 2 (volume.restrict (Metric.ball y rho)) →
        MemLp h 2 (volume.restrict (Metric.ball y rho)) →
        IntegrableOn (fun x => inner ℝ (matrixAction (N x) (g x)) (h x))
          (Metric.ball y rho)) ∧
      (∀ p, (lam / (1 + P * rho ^ 2)) * ‖p‖ ^ 2 ≤ B p p) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "exact (by\n  let U := Metric.ball y rho\n  let μ := volume.restrict U\n  let G := Lp E2 2 μ\n  have maadd (x : E2) (v w : E2) :\n      matrixAction (N x) (v + w) = matrixAction (N x) v + matrixAction (N x) w := by\n    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n    ext i\n    change (∑ j, N x i j * (v j + w j)) =\n      (∑ j, N x i j * v j) + ∑ j, N x i j * w j\n    simp only [mul_add, Finset.sum_add_distrib]\n  have masmul (x : E2) (a : ℝ) (v : E2) :\n      matrixAction (N x) (a • v) = a • matrixAction (N x) v := by\n    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n    ext i\n    change (∑ j, N x i j * (a * v j)) = a * ∑ j, N x i j * v j\n    rw [Finset.mul_sum]\n    apply Finset.sum_congr rfl\n    intro j hj\n    ring\n  have mapbound (g : E2 → E2) :\n      ∀ᵐ x ∂μ, ‖matrixAction (N x) (g x)‖ ≤ K * ‖g x‖ := by\n    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx\n    exact (hbound x hx (g x)).2\n  have mapped (g : E2 → E2) (hg : MemLp g 2 μ) :\n      MemLp (fun x => matrixAction (N x) (g x)) 2 μ := by\n    have coord (j : Fin 2) : MemLp (fun x => g x j) 2 μ :=\n      hg.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)\n    have hm (i : Fin 2) : AEStronglyMeasurable (fun x => ∑ j, N x i j * g x j) μ := by\n      simp only [Fin.sum_univ_two]\n      exact ((hN i 0).mul (coord 0).aestronglyMeasurable).add\n        ((hN i 1).mul (coord 1).aestronglyMeasurable)\n    have hp : AEMeasurable (fun x => fun i : Fin 2 => ∑ j, N x i j * g x j) μ :=\n      AEMeasurable.of_eval fun i => (hm i).aemeasurable\n    have hma : AEStronglyMeasurable (fun x => matrixAction (N x) (g x)) μ :=\n      ((PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp_aemeasurable hp).aestronglyMeasurable\n    exact hg.of_le_mul hma (mapbound g)\n  let T : G → G := fun g => (mapped g (Lp.memLp g)).toLp (fun x => matrixAction (N x) (g x))\n  have Tcoe (g : G) : (T g : E2 → E2) =ᵐ[μ] fun x => matrixAction (N x) (g x) :=\n    (mapped g (Lp.memLp g)).coeFn_toLp\n  have Tadd (g h : G) : T (g + h) = T g + T h := by\n    apply Lp.ext\n    filter_upwards [Tcoe (g + h), Tcoe g, Tcoe h, Lp.coeFn_add g h,\n      Lp.coeFn_add (T g) (T h)] with x hab ha hb hgh htab\n    rw [hab, htab, hgh]\n    change matrixAction (N x) (g x + h x) = (T g) x + (T h) x\n    rw [ha, hb]\n    exact maadd x (g x) (h x)\n  have Tsmul (a : ℝ) (g : G) : T (a • g) = a • T g := by\n    apply Lp.ext\n    filter_upwards [Tcoe (a • g), Tcoe g, Lp.coeFn_smul a g,\n      Lp.coeFn_smul a (T g)] with x hag hg hag' hat\n    rw [hag, hat, hag']\n    change matrixAction (N x) (a • g x) = a • (T g) x\n    rw [hg]\n    exact masmul x a (g x)\n  let Tlin : G →ₗ[ℝ] G := { toFun := T, map_add' := Tadd, map_smul' := Tsmul }\n  have Tnorm (g : G) : ‖Tlin g‖ ≤ K * ‖g‖ := by\n    change ‖(mapped g (Lp.memLp g)).toLp (fun x => matrixAction (N x) (g x))‖ ≤ K * ‖g‖\n    rw [Lp.norm_toLp, Lp.norm_def]\n    have hh := eLpNorm_le_mul_eLpNorm_of_ae_le_mul\n      (mapped g (Lp.memLp g)).aestronglyMeasurable (mapbound g) 2\n    have hz : ENNReal.ofReal K * eLpNorm g 2 μ ≠ ⊤ :=\n      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp g).eLpNorm_lt_top.ne\n    have ht := ENNReal.toReal_mono hz hh\n    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK.le] at ht\n    exact ht\n  let Tc : G →L[ℝ] G := Tlin.mkContinuous K Tnorm\n  let gp : X U →L[ℝ] G :=\n    (WithLp.sndL 2 ℝ (Lp ℝ 2 μ) G).comp (space U).subtypeL\n  let B : X U →L[ℝ] X U →L[ℝ] ℝ := (innerSL ℝ).bilinearComp (Tc.comp gp) gp\n  have hint (g h : E2 → E2) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :\n      Integrable (fun x => inner ℝ (matrixAction (N x) (g x)) (h x)) μ := by\n    apply (L2.integrable_inner (𝕜 := ℝ)\n      ((mapped g hg).toLp (fun x => matrixAction (N x) (g x))) (hh.toLp h)).congr\n    filter_upwards [(mapped g hg).coeFn_toLp, hh.coeFn_toLp] with x hx hx'\n    rw [hx, hx']\n  have Beq (p q : X U) : B p q = b U N p q := by\n    change inner ℝ (T (gp p)) (gp q) = _\n    rw [L2.inner_def]\n    apply integral_congr_ae\n    filter_upwards [Tcoe (gp p)] with x hx\n    rw [hx]\n    rfl\n  have hfinite : IsFiniteMeasure μ := by\n    exact isFiniteMeasure_restrict.mpr (measure_ball_lt_top (μ := volume) (x := y) (r := rho)).ne\n  let _ : IsFiniteMeasure μ := hfinite\n  have hc : MemLp (fun _ : E2 => coordinateVector 2 0) 2 μ := memLp_const _\n  let c : G := hc.toLp (fun _ : E2 => coordinateVector 2 0)\n  let ell : X U →L[ℝ] ℝ := -((innerSL ℝ (Tc c)).comp gp)\n  have elleq (q : X U) : ell q = load U N q := by\n    change -(inner ℝ (T c) (gp q)) = _\n    rw [L2.inner_def]\n    congr 1\n    apply integral_congr_ae\n    filter_upwards [Tcoe c, hc.coeFn_toLp] with x hx hx'\n    rw [hx, hx']\n    rfl\n  refine ⟨B, ell, Beq, elleq, hint, ?_⟩\n  intro p\n  have he : Integrable (fun x => lam * ‖grad U p x‖ ^ 2) μ :=\n    ((Lp.memLp (gradLp U p)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul lam\n  have hb := hint (grad U p) (grad U p) (Lp.memLp (gradLp U p)) (Lp.memLp (gradLp U p))\n  have hlow : lam * ‖gradLp U p‖ ^ 2 ≤ B p p := by\n    rw [Beq]\n    have hid : ‖gradLp U p‖ ^ 2 = ∫ x, ‖grad U p x‖ ^ 2 ∂μ := by\n      rw [← real_inner_self_eq_norm_sq, L2.inner_def]\n      apply integral_congr_ae\n      exact Filter.Eventually.of_forall fun x => real_inner_self_eq_norm_sq _\n    rw [hid, ← integral_const_mul]\n    apply integral_mono_ae he hb\n    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx\n    exact (hbound x hx (grad U p x)).1\n  have hd : 0 < 1 + P * rho ^ 2 := by positivity\n  calc\n    (lam / (1 + P * rho ^ 2)) * ‖p‖ ^ 2 ≤\n        (lam / (1 + P * rho ^ 2)) * ((1 + P * rho ^ 2) * ‖gradLp U p‖ ^ 2) :=\n      mul_le_mul_of_nonneg_left (hP p) (div_nonneg hlam.le hd.le)\n    _ = lam * ‖gradLp U p‖ ^ 2 := by rw [← mul_assoc, div_mul_cancel₀ lam hd.ne']\n    _ ≤ B p p := hlow\n)"))

/-- D6: extract the exact affine native weak solution from the variational equation. -/
theorem native_affine_solution_of_variational
    (M : E2 → Mat2) (y : E2) (rho : ℝ) (hrho : 0 < rho)
    (p : X (Metric.ball y rho))
    (hint : ∀ g h : E2 → E2,
      MemLp g 2 (volume.restrict (Metric.ball y rho)) →
      MemLp h 2 (volume.restrict (Metric.ball y rho)) →
      IntegrableOn (fun x => inner ℝ
        (matrixAction (normalizedInverse M x) (g x)) (h x)) (Metric.ball y rho))
    (hsolve : ∀ q : X (Metric.ball y rho),
      b (Metric.ball y rho) (normalizedInverse M) p q =
        load (Metric.ball y rho) (normalizedInverse M) q) :
    AffineWeakSolution M y rho
      (fun x => val (Metric.ball y rho) p x + affineDatum y x)
      (fun x => grad (Metric.ball y rho) p x + coordinateVector 2 0) := by
  classical
  let U := Metric.ball y rho
  let mu := volume.restrict U
  let e : E2 := coordinateVector 2 0
  have hU : MeasurableSet U := Metric.isOpen_ball.measurableSet
  have : IsFiniteMeasure mu := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hv : MemLp (val U p) 2 mu := Lp.memLp (valLp U p)
  have hg : MemLp (grad U p) 2 mu := Lp.memLp (gradLp U p)
  have he : MemLp (fun _ : E2 => e) 2 mu := memLp_const e
  have hp : H10On U (val U p) (grad U p) := by
    apply (nativeH10_iff_pair_mem y rho hrho _ _ hv hg).mpr
    have hid : pack U (val U p) (grad U p) hv hg = p.val := by
      have hvEq : hv.toLp (val U p) = valLp U p := Lp.toLp_coeFn (valLp U p) hv
      have hgEq : hg.toLp (grad U p) = gradLp U p := Lp.toLp_coeFn (gradLp U p) hg
      unfold pack
      rw [hvEq, hgEq]
      rfl
    rw [hid]
    exact p.property
  have haSmooth : ContDiff ℝ ∞ (affineDatum y) := by
    unfold affineDatum
    fun_prop
  have haDeriv (x : E2) : HasFDerivAt (affineDatum y)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) x := by
    convert (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.sub_const (y 0) using 1
    ext z
    simp [affineDatum]
  have hda (x : E2) (i : Fin 2) :
      fderiv ℝ (affineDatum y) x (coordinateVector 2 i) = e i := by
    rw [(haDeriv x).fderiv]
    fin_cases i <;> simp [e, coordinateVector, EuclideanSpace.single]
  have ha : MemLp (affineDatum y) 2 mu := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall y rho).exists_bound_of_continuousOn
      haSmooth.continuous.continuousOn
    apply MemLp.of_bound haSmooth.continuous.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem hU] with x hx
    exact hC x (Metric.ball_subset_closedBall hx)
  have haWeak : WeakGradientOn U (affineDatum y) (fun _ => e) := by
    refine ⟨haSmooth.continuous.locallyIntegrable.locallyIntegrableOn _,
      continuous_const.locallyIntegrable.locallyIntegrableOn _, ?_⟩
    intro psi hs hc ht i
    have hdpsi : Continuous (fun x => fderiv ℝ psi x (coordinateVector 2 i)) :=
      (hs.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdaCont : Continuous (fun x => fderiv ℝ (affineDatum y) x (coordinateVector 2 i)) :=
      (haSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      ((hdaCont.mul hs.continuous).integrable_of_hasCompactSupport hc.mul_left)
      ((haSmooth.continuous.mul hdpsi).integrable_of_hasCompactSupport
        (hc.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i)).mul_left)
      ((haSmooth.continuous.mul hs.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun x _ => haSmooth.differentiable (by simp) x)
      (fun x _ => hs.differentiable (by simp) x)
    simp_rw [hda] at hibp
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hibp
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (ht h)), mul_zero]
    · intro x hx
      have hdsub : tsupport (fun x => fderiv ℝ psi x (coordinateVector 2 i)) ⊆ U :=
        (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans ht
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hdsub h)), mul_zero]
  have hsum : H1On U (fun x => val U p x + affineDatum y x)
      (fun x => grad U p x + e) := by
    refine ⟨⟨hp.1.1.1.add haWeak.1, hp.1.1.2.1.add haWeak.2.1, ?_⟩,
      hv.add ha, hg.add he⟩
    intro psi hs hc ht i
    have hpsi : MemLp psi 2 mu :=
      (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict U
    have hdpsi : MemLp (fun x => fderiv ℝ psi x (coordinateVector 2 i)) 2 mu :=
      (((hs.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (μ := volume) (hc.fderiv_apply ℝ (coordinateVector 2 i))).restrict U
    have hgi : MemLp (fun x => grad U p x i) 2 mu :=
      hg.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
    have hei : MemLp (fun _ : E2 => e i) 2 mu := memLp_const _
    have hw := hp.1.1.2.2 psi hs hc ht i
    have haw := haWeak.2.2 psi hs hc ht i
    change (∫ x in U, (val U p x + affineDatum y x) *
      fderiv ℝ psi x (coordinateVector 2 i)) =
      -(∫ x in U, (grad U p x i + e i) * psi x)
    simp_rw [add_mul]
    have hleft := integral_add (hv.integrable_mul hdpsi) (ha.integrable_mul hdpsi)
    have hright := integral_add (hgi.integrable_mul hpsi) (hei.integrable_mul hpsi)
    simp only [Pi.mul_apply] at hleft hright
    rw [hleft, hright, hw, haw]
    ring
  refine ⟨hsum, ?_, ?_⟩
  · simpa only [add_sub_cancel_right] using hp
  · refine ⟨hsum.1, ?_⟩
    intro phi hs hc ht
    have htH10 := native_smooth_h10 y rho hrho phi hs hc ht
    have hphi := htH10.1.2.1
    have hdphi := htH10.1.2.2
    let q : X U := ⟨pack U phi (planarGradient phi) hphi hdphi,
      (nativeH10_iff_pair_mem y rho hrho phi (planarGradient phi) hphi hdphi).mp htH10⟩
    have hq : grad U q =ᵐ[mu] planarGradient phi := hdphi.coeFn_toLp
    have hB : b U (normalizedInverse M) p q =
        ∫ x in U, inner ℝ (matrixAction (normalizedInverse M x) (grad U p x))
          (planarGradient phi x) := by
      apply integral_congr_ae
      filter_upwards [hq] with x hx
      rw [hx]
    have hL : load U (normalizedInverse M) q =
        -(∫ x in U, inner ℝ (matrixAction (normalizedInverse M x) e)
          (planarGradient phi x)) := by
      unfold load
      congr 1
      apply integral_congr_ae
      filter_upwards [hq] with x hx
      rw [hx]
    have hEq := hsolve q
    rw [hB, hL] at hEq
    have hi1 := hint (grad U p) (planarGradient phi) hg hdphi
    have hi2 := hint (fun _ => e) (planarGradient phi) he hdphi
    have hiSum := hint (fun x => grad U p x + e) (planarGradient phi) (hg.add he) hdphi
    have hma (A : Mat2) (s t : E2) : matrixAction A (s + t) =
        matrixAction A s + matrixAction A t := by
      ext i
      simp [matrixAction, mul_add, Finset.sum_add_distrib]
    simp only [inner_zero_left, zero_mul, add_zero, sub_zero]
    refine ⟨hiSum, ?_⟩
    change (∫ x in U, inner ℝ (matrixAction (normalizedInverse M x) (grad U p x + e))
      (planarGradient phi x)) = 0
    simp_rw [hma, inner_add_left]
    rw [integral_add hi1 hi2, hEq]
    ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
