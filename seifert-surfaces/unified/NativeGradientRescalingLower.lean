import GradientEstimateRescalingData

noncomputable section
set_option autoImplicit false
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower
open SeifertSurfaces.AppendixACoordinates

/-- Smooth-test pullback of the actual affine error equation; scalar forcing is zero. -/
theorem native_affine_error_rescaling (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (M : E2 → Mat2) (y : E2) (r : ℝ)
    (hr : 0 < r) (symmetric : SymmetricOn M (Metric.ball y r))
    (elliptic : UniformEllipticOn M (Metric.ball y r))
    (holder : ∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha (fun x => M x i j) (Metric.ball y r))
    (rho : ℝ) (hrho : 0 < rho) (hrhor : rho ≤ r)
    (a : E2 → ℝ) (da : E2 → E2) (ha : AffineWeakSolution M y rho a da) :
    DirectWeak.WeakDivergenceWithData (Metric.ball (0 : E2) 1)
      (rescaledCoefficient (normalizedInverse M) y rho)
      (rescaledForcing (normalizedInverse M) y rho) (fun _ => 0)
      (rescaledError y rho a) (rescaledErrorGradient y rho da) := by
  classical { let U := Metric.ball (0 : E2) 1; let V := Metric.ball y rho; let f : E2 → E2 := dilation y rho; let s : E2 → E2 := inverseDilation y rho; let u : E2 → ℝ := fun x => a x - affineDatum y x; let d : E2 → E2 := fun x => da x - coordinateVector 2 0; let c : ℝ≥0∞ := ENNReal.ofReal ((rho ^ (2 : ℕ))⁻¹); have hf : Measurable f := by { change Measurable (fun z : E2 => y + rho • z); fun_prop }; have hsf (z : E2) : s (f z) = z := by { dsimp only [s, f, inverseDilation, dilation]; rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hrho.ne', one_smul] }; have hfs (x : E2) : f (s x) = x := by { dsimp only [s, f, inverseDilation, dilation]; rw [smul_smul, mul_inv_cancel₀ hrho.ne', one_smul, add_sub_cancel] }; let H : E2 ≃ₜ E2 := { toFun := f, invFun := s, left_inv := hsf, right_inv := hfs, continuous_toFun := by change Continuous (fun z : E2 => y + rho • z); fun_prop, continuous_invFun := by change Continuous (fun x : E2 => rho⁻¹ • (x - y)); fun_prop }; have hp : f ⁻¹' V = U := by { ext z; change dist (y + rho • z) y < rho ↔ dist z 0 < 1; simp only [dist_eq_norm, add_sub_cancel_left, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hrho]; constructor <;> intro h <;> nlinarith }; have hm : Measure.map f (volume : Measure E2) = c • volume := by { have ht : Measure.map f volume = Measure.map (fun x : E2 => y + x) (Measure.map (fun z : E2 => rho • z) volume) := (Measure.map_map (by fun_prop) (by fun_prop)).symm; have hscale : Measure.map (fun x : E2 => y + x) (Measure.map (fun z : E2 => rho • z) volume) = Measure.map (fun x : E2 => y + x) (c • volume) := by { congr 1; simpa only [c, finrank_euclideanSpace_fin, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg rho))] using (Measure.map_addHaar_smul (volume : Measure E2) hrho.ne') }; have htranslation : Measure.map (fun x : E2 => y + x) (c • volume) = c • volume := by { rw [Measure.map_smul c (by fun_prop), (measurePreserving_add_left (volume : Measure E2) y).map_eq] }; exact ht.trans (hscale.trans htranslation) }; have hmr : Measure.map f (volume.restrict U) = c • volume.restrict V := by { rw [← hp, ← Measure.restrict_map hf measurableSet_ball, hm, Measure.restrict_smul] }; have pull {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E2 → F) (hg : IntegrableOn g V) : IntegrableOn (g ∘ f) U ∧ (∫ z in U, g (f z)) = (rho ^ (2 : ℕ))⁻¹ • (∫ x in V, g x) := by { have hgm : Integrable g (Measure.map f (volume.restrict U)) := by { rw [hmr]; exact hg.smul_measure ENNReal.ofReal_ne_top }; refine ⟨(integrable_map_measure hgm.aestronglyMeasurable hf.aemeasurable).mp hgm, ?_⟩; rw [← integral_map hf.aemeasurable hgm.aestronglyMeasurable, hmr, integral_smul_measure]; change (ENNReal.ofReal ((rho ^ (2 : ℕ))⁻¹)).toReal • (∫ x in V, g x) = _; rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg rho))] }; have test (phi : E2 → ℝ) (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ U) : ContDiff ℝ ∞ (phi ∘ s) ∧ HasCompactSupport (phi ∘ s) ∧ tsupport (phi ∘ s) ⊆ V ∧ (∀ x i, fderiv ℝ (phi ∘ s) x (coordinateVector 2 i) = rho⁻¹ * fderiv ℝ phi (s x) (coordinateVector 2 i)) ∧ (∀ x, planarGradient (phi ∘ s) x = rho⁻¹ • planarGradient phi (s x)) := by { have hsmooth : ContDiff ℝ ∞ s := by { change ContDiff ℝ ∞ (fun x : E2 => rho⁻¹ • (x - y)); fun_prop }; have hpart (x : E2) (i : Fin 2) : fderiv ℝ (phi ∘ s) x (coordinateVector 2 i) = rho⁻¹ * fderiv ℝ phi (s x) (coordinateVector 2 i) := by { have hsd : HasFDerivAt s (rho⁻¹ • ContinuousLinearMap.id ℝ E2) x := ((hasFDerivAt_id x).sub_const y).const_smul rho⁻¹; rw [((hphi.differentiable (by simp) (s x)).hasFDerivAt.comp x hsd).fderiv]; simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] }; refine ⟨hphi.comp hsmooth, hc.comp_homeomorph H.symm, ?_, hpart, ?_⟩; · { intro x hx; have hx' : s x ∈ tsupport phi := tsupport_comp_subset_preimage phi hsmooth.continuous hx; have hh : f (s x) ∈ V := by { change s x ∈ f ⁻¹' V; rw [hp]; exact hs hx' }; simpa only [hfs] using hh }; · { intro x; simp only [planarGradient, hpart, Finset.smul_sum, smul_smul] } }; have hu0 : H1On V u d := ha.2.1.1; have hup : MemLp (u ∘ f) 2 (volume.restrict U) := by { have hh : MemLp u 2 (Measure.map f (volume.restrict U)) := by { rw [hmr]; exact hu0.2.1.smul_measure ENNReal.ofReal_ne_top }; exact hh.comp_of_map hf.aemeasurable }; have hdp : MemLp (d ∘ f) 2 (volume.restrict U) := by { have hh : MemLp d 2 (Measure.map f (volume.restrict U)) := by { rw [hmr]; exact hu0.2.2.smul_measure ENNReal.ofReal_ne_top }; exact hh.comp_of_map hf.aemeasurable }; have hvr : MemLp (rescaledError y rho a) 2 (volume.restrict U) := by { convert hup.const_smul rho⁻¹ using 1; funext z; change u (f z) / rho = rho⁻¹ * u (f z); exact div_eq_inv_mul _ _ }; have hdr : MemLp (rescaledErrorGradient y rho da) 2 (volume.restrict U) := hdp; have hfinite : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne; let _ := hfinite; have h1 : H1On U (rescaledError y rho a) (rescaledErrorGradient y rho da) := by { refine ⟨⟨IntegrableOn.locallyIntegrableOn (MemLp.integrable (by norm_num) hvr), IntegrableOn.locallyIntegrableOn (MemLp.integrable (by norm_num) hdr), ?_⟩, hvr, hdr⟩; intro phi hphi hc hs i; obtain ⟨hpsi, hcpsi, hspsi, hpart, hgrad⟩ := test phi hphi hc hs; have hphiMem : MemLp (phi ∘ s) 2 (volume.restrict V) := hpsi.continuous.memLp_of_hasCompactSupport hcpsi; have hderMem : MemLp (fun x => fderiv ℝ (phi ∘ s) x (coordinateVector 2 i)) 2 (volume.restrict V) := ((hpsi.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport (hcpsi.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i)); have hl := pull _ (hu0.2.1.integrable_mul hderMem); have hr' := pull _ ((hu0.2.2.eval_piLp i).integrable_mul hphiMem); simp only [Pi.mul_apply] at hl hr'; have hw := hu0.1.2.2 (phi ∘ s) hpsi hcpsi hspsi i; have heq : (∫ z in U, u (f z) * fderiv ℝ (phi ∘ s) (f z) (coordinateVector 2 i)) = -(∫ z in U, d (f z) i * (phi ∘ s) (f z)) := by { rw [hl.2, hr'.2, hw, smul_neg] }; change (∫ z in U, (u (f z) / rho) * fderiv ℝ phi z (coordinateVector 2 i)) = -(∫ z in U, d (f z) i * phi z); simpa only [hpart, hsf, Function.comp_apply, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using heq }; let N := normalizedInverse M; let W := Metric.ball y r; have hM : ContinuousOn M W := by { apply continuousOn_pi.mpr; intro i; apply continuousOn_pi.mpr; intro j; obtain ⟨C, hC⟩ := holder i j; exact hC.continuousOn G.alpha_pos }; have hdet (x : E2) (hx : x ∈ W) : 0 < Matrix.det (M x) := by { apply Matrix.PosDef.det_pos; apply Matrix.posDef_iff_dotProduct_mulVec.mpr; refine ⟨?_, ?_⟩; · { ext i j; simpa only [Matrix.conjTranspose_apply, star_trivial] using symmetric x hx j i }; · { intro v hv; let p : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm v; have hp0 : p ≠ 0 := by { intro hh; apply hv; have he := congrArg (EuclideanSpace.equiv (Fin 2) ℝ) hh; simpa only [p, ContinuousLinearEquiv.apply_symm_apply, map_zero] using he }; obtain ⟨ell, C, hell, hC, hb⟩ := elliptic; have hq : 0 < inner ℝ p (matrixAction (M x) p) := (mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hp0))).trans_le (hb x hx p).1; change 0 < ∑ i : Fin 2, (∑ j : Fin 2, M x i j * v j) * v i at hq; simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, mul_comm] using hq } }; have hN : ContinuousOn N W := by { intro x hx; have hMx : ContinuousAt M x := hM.continuousAt (Metric.isOpen_ball.mem_nhds hx); have hdx : ContinuousAt (fun z => Matrix.det (M z)) x := continuous_id.matrix_det.continuousAt.comp hMx; have her : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext Ring.inverse_eq_inv; have hi : ContinuousAt (fun z => (M z)⁻¹) x := (continuousAt_matrix_inv (M x) (by rw [her]; exact continuousAt_inv₀ (hdet x hx).ne')).comp hMx; exact (hdx.sqrt.smul hi).continuousWithinAt }; have hNU : ContinuousOn (N ∘ f) U := (hN.mono (Metric.ball_subset_ball hrhor)).comp H.continuous_toFun.continuousOn (fun z hz => by change z ∈ f ⁻¹' V; rw [hp]; exact hz); have gcont : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → Continuous (planarGradient phi) := by { intro phi hphi; apply continuous_finsetSum; intro i hi; exact ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const }; have gsupp : ∀ (phi : E2 → ℝ) (x : E2), x ∉ tsupport phi → planarGradient phi x = 0 := by { intro phi x hx; unfold planarGradient; apply Finset.sum_eq_zero; intro i hi; rw [image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i) h)), zero_smul] }; have intsmooth (phi : E2 → ℝ) (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ U) (q : E2 → E2) (hq : ContinuousOn q U) : IntegrableOn (fun z => inner ℝ (q z) (planarGradient phi z)) U := by { have hcont := hq.inner (𝕜 := ℝ) (gcont phi hphi).continuousOn; have hsupp : Function.support (fun z => inner ℝ (q z) (planarGradient phi z)) ⊆ tsupport phi := by { intro z hz; by_contra hh; exact hz (by change inner ℝ (q z) (planarGradient phi z) = 0; rw [gsupp phi z hh, inner_zero_right]) }; exact ((integrableOn_iff_integrable_of_support_subset hsupp).mp ((hcont.mono hs).integrableOn_compact hc)).integrableOn }; have mean_grad (U : Set E2) (phi : E2 → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ U) (q : E2) : (∫ x in U, inner ℝ q (planarGradient phi x)) = 0 := by { have hi (i : Fin 2) : Integrable (fun x => fderiv ℝ phi x (coordinateVector 2 i)) volume := ((hp.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i)); have hz (i : Fin 2) : (∫ x in U, fderiv ℝ phi x (coordinateVector 2 i)) = 0 := by { rw [setIntegral_eq_integral_of_forall_compl_eq_zero]; · { have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := fun _ : E2 => (1 : ℝ)) (g := phi) (v := coordinateVector 2 i) (by simp) (by simpa only [one_mul] using hi i) (by simpa only [one_mul] using hp.continuous.integrable_of_hasCompactSupport hc) (fun x _ => differentiableAt_const _) (fun x _ => hp.differentiable (by simp) x); simpa only [one_mul, fderiv_fun_const, Pi.zero_apply, zero_apply, zero_mul, integral_zero, neg_zero] using hh }; · { intro x hx; exact image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ phi x (coordinateVector 2 i)) (fun h => hx (hs (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i) h))) } }; have hexp (x : E2) : inner ℝ q (planarGradient phi x) = ∑ i : Fin 2, q i * fderiv ℝ phi x (coordinateVector 2 i) := by { delta planarGradient; rw [inner_sum]; apply Finset.sum_congr rfl; intro i hi; rw [inner_smul_right]; have he : inner ℝ q (coordinateVector 2 i) = q i := by { delta coordinateVector; simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul] }; rw [he, mul_comm] }; simp_rw [hexp]; rw [integral_finsetSum Finset.univ (fun i hi' => (hi i).integrableOn.const_mul (q i))]; simp only [integral_const_mul, hz, mul_zero, Finset.sum_const_zero] }; refine ⟨h1, ?_⟩; intro phi hphi hc hs; obtain ⟨hpsi, hcpsi, hspsi, hpart, hgrad⟩ := test phi hphi hc hs; obtain ⟨hflux, hzero⟩ := ha.2.2.2 (phi ∘ s) hpsi hcpsi hspsi; simp only [inner_zero_left, zero_mul, add_zero, sub_zero] at hflux hzero; have pulled := pull _ hflux; have hfluxU : IntegrableOn (fun z => inner ℝ (matrixAction (N (f z)) (da (f z))) (planarGradient phi z)) U := by { have hh := pulled.1.const_mul rho; apply hh.congr; filter_upwards [] with z; simp only [Function.comp_apply, hgrad, hsf, inner_smul_right]; change rho * (rho⁻¹ * _) = _; rw [← mul_assoc, mul_inv_cancel₀ hrho.ne', one_mul] }; have hzeroU : (∫ z in U, inner ℝ (matrixAction (N (f z)) (da (f z))) (planarGradient phi z)) = 0 := by { have hh : (∫ z in U, rho * inner ℝ (matrixAction (N (f z)) (da (f z))) (planarGradient (phi ∘ s) (f z))) = 0 := by { rw [integral_const_mul, pulled.2, hzero, smul_zero, mul_zero] }; have hefun : (fun z => rho * inner ℝ (matrixAction (N (f z)) (da (f z))) (planarGradient (phi ∘ s) (f z))) = (fun z => inner ℝ (matrixAction (N (f z)) (da (f z))) (planarGradient phi z)) := by { funext z; rw [hgrad, hsf, inner_smul_right]; change rho * (rho⁻¹ * _) = _; rw [← mul_assoc, mul_inv_cancel₀ hrho.ne', one_mul] }; rw [hefun] at hh; exact hh }; have hcolumn : ContinuousOn (fun z => matrixAction (N (f z)) (coordinateVector 2 0)) U := by { change ContinuousOn (fun z => WithLp.toLp 2 (fun i : Fin 2 => ∑ j : Fin 2, N (f z) i j * coordinateVector 2 0 j)) U; apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn; apply continuousOn_pi.mpr; intro i; apply continuousOn_finsetSum; intro j hj; exact ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hNU)).mul continuousOn_const }; let q : E2 := matrixAction (N y) (coordinateVector 2 0); have hcolInt := intsmooth phi hphi hc hs _ hcolumn; have hqInt := intsmooth phi hphi hc hs (fun _ => q) continuousOn_const; have hmean : (∫ z in U, inner ℝ q (planarGradient phi z)) = 0 := mean_grad U phi hphi hc hs q; have he (z : E2) : matrixAction (N (f z)) (rescaledErrorGradient y rho da z) = matrixAction (N (f z)) (da (f z)) - matrixAction (N (f z)) (coordinateVector 2 0) := by { ext i; dsimp only [matrixAction, rescaledErrorGradient, f]; simp only [PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]; rfl }; have heforce (z : E2) : rescaledForcing N y rho z = q - matrixAction (N (f z)) (coordinateVector 2 0) := by { ext i; dsimp only [rescaledForcing, matrixAction]; simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]; rfl }; change IntegrableOn (fun z => inner ℝ (matrixAction (N (f z)) (rescaledErrorGradient y rho da z)) (planarGradient phi z)) U ∧ IntegrableOn (fun z => inner ℝ (rescaledForcing N y rho z) (planarGradient phi z) + (0 : ℝ) * phi z) U ∧ (∫ z in U, inner ℝ (matrixAction (N (f z)) (rescaledErrorGradient y rho da z)) (planarGradient phi z)) = ∫ z in U, inner ℝ (rescaledForcing N y rho z) (planarGradient phi z) + (0 : ℝ) * phi z; refine ⟨?_, ?_, ?_⟩; · { apply (hfluxU.sub hcolInt).congr; filter_upwards [] with z; rw [he, inner_sub_left]; rfl }; · { apply (hqInt.sub hcolInt).congr; filter_upwards [] with z; rw [heforce, inner_sub_left]; simp only [zero_mul, add_zero, Pi.sub_apply] }; · { simp only [he, heforce, inner_sub_left, zero_mul, add_zero]; rw [integral_sub hfluxU hcolInt, integral_sub hqInt hcolInt, hzeroU, hmean] } }

/-- Conditional transport of the same local coefficient bounds; no global extension. -/
theorem native_rescaled_coefficient_bounds (alpha : ℝ≥0) (N : E2 → Mat2)
    (y : E2) (r1 lam Lambda : ℝ) (HN : ℝ≥0)
    (symmetric : SymmetricOn N (Metric.ball y r1))
    (bounds : ∀ x ∈ Metric.ball y r1, ∀ v : E2,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v (matrixAction (N x) v) ∧
        ‖matrixAction (N x) v‖ ≤ Lambda * ‖v‖)
    (holder : ∀ i j,
      HolderOnWith HN alpha (fun x => N x i j) (Metric.ball y r1))
    (rho : ℝ) (hrho : 0 < rho) (hrhor1 : rho ≤ r1) (hrho1 : rho ≤ 1) :
    SymmetricOn (rescaledCoefficient N y rho) (Metric.ball (0 : E2) 1) ∧
    (∀ z ∈ Metric.ball (0 : E2) 1, ∀ v : E2,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v (matrixAction (rescaledCoefficient N y rho z) v) ∧
        ‖matrixAction (rescaledCoefficient N y rho z) v‖ ≤ Lambda * ‖v‖) ∧
    ∀ i j, HolderOnWith HN alpha (fun z => rescaledCoefficient N y rho z i j)
      (Metric.ball (0 : E2) 1) := by { have hmem : ∀ z ∈ Metric.ball (0 : E2) 1, dilation y rho z ∈ Metric.ball y r1 := by { intro z hz; have hn : ‖z‖ < 1 := by { simpa [Metric.mem_ball, dist_eq_norm] using hz }; have hdist : dist (dilation y rho z) y = rho * ‖z‖ := by { simp [dilation, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hrho] }; rw [Metric.mem_ball, hdist]; exact (mul_lt_mul_of_pos_left hn hrho).trans_le (by simpa using hrhor1) }; have hd : ∀ z w, dist (dilation y rho z) (dilation y rho w) ≤ dist z w := by { intro z w; simp only [dilation, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hrho]; exact mul_le_of_le_one_left (dist_nonneg) hrho1 }; refine ⟨?_, ?_, ?_⟩; { intro z hz i j; exact symmetric _ (hmem z hz) i j }; { intro z hz v; exact bounds _ (hmem z hz) v }; { intro i j z hz w hw; exact (holder i j).edist_le_of_le (hmem z hz) (hmem w hw) (by simpa only [edist_dist] using ENNReal.ofReal_le_ofReal (hd z w)) } }
  

/-- One forcing constant precedes every radius; the same forcing has both bounds. -/
theorem native_rescaled_forcing_bounds (alpha : ℝ≥0) (halpha : 0 < alpha)
    (N : E2 → Mat2) (y : E2) (r1 : ℝ) (hr1 : 0 < r1) (HN : ℝ≥0)
    (holder : ∀ i j,
      HolderOnWith HN alpha (fun x => N x i j) (Metric.ball y r1)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ r1 →
        ∃ BF : ℝ, ∃ HF : ℝ≥0, 0 ≤ BF ∧
          (∀ z ∈ Metric.ball (0 : E2) 1, ‖rescaledForcing N y rho z‖ ≤ BF) ∧
          HolderOnWith HF alpha (rescaledForcing N y rho) (Metric.ball (0 : E2) 1) ∧
          BF + (HF : ℝ) ≤ K * rho ^ (alpha : ℝ) := by
  run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "exact (by\n  classical\n  refine ⟨4 * (HN : ℝ), by positivity, ?_⟩\n  intro rho hrho hrhor1\n  have hrpow : 0 ≤ rho ^ (alpha : ℝ) := Real.rpow_nonneg hrho.le _\n  let B : ℝ := 2 * (HN : ℝ) * rho ^ (alpha : ℝ)\n  have hB : 0 ≤ B := by dsimp [B]; positivity\n  let H : ℝ≥0 := ⟨B, hB⟩\n  have hin (z : E2) (hz : z ∈ Metric.ball (0 : E2) 1) : dilation y rho z ∈ Metric.ball y r1 := by\n    rw [Metric.mem_ball, dist_zero_right] at hz\n    rw [Metric.mem_ball]\n    change dist (y + rho • z) y < r1\n    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hrho]\n    exact lt_of_lt_of_le (by nlinarith) hrhor1\n  have hdist (u v : E2) : dist (dilation y rho u) (dilation y rho v) = rho * dist u v := by\n    change dist (y + rho • u) (y + rho • v) = _\n    rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hrho]\n  have hcoord (z : E2) (i : Fin 2) : rescaledForcing N y rho z i = N y i 0 - N (dilation y rho z) i 0 := by\n    dsimp [rescaledForcing, matrixAction, coordinateVector]\n    simp [Fin.sum_univ_two]\n  have hnorm (v : E2) : ‖v‖ ≤ |v 0| + |v 1| := by\n    have heq := EuclideanSpace.norm_sq_eq v\n    rw [Fin.sum_univ_two] at heq\n    simp only [Real.norm_eq_abs, sq_abs] at heq\n    nlinarith [norm_nonneg v, abs_nonneg (v 0), abs_nonneg (v 1), sq_abs (v 0), sq_abs (v 1), mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1))]\n  have hdiff (u : E2) (hu : u ∈ Metric.ball (0 : E2) 1)\n      (v : E2) (hv : v ∈ Metric.ball (0 : E2) 1) :\n      dist (rescaledForcing N y rho u) (rescaledForcing N y rho v) ≤ B * dist u v ^ (alpha : ℝ) := by\n    have hc (i : Fin 2) : |rescaledForcing N y rho u i - rescaledForcing N y rho v i| ≤\n        (HN : ℝ) * (rho ^ (alpha : ℝ) * dist u v ^ (alpha : ℝ)) := by\n      have h := (holder i 0).dist_le (hin u hu) (hin v hv)\n      rw [hdist, Real.mul_rpow hrho.le dist_nonneg] at h\n      rw [hcoord, hcoord]\n      have heq : (N y i 0 - N (dilation y rho u) i 0) - (N y i 0 - N (dilation y rho v) i 0) =\n          -(N (dilation y rho u) i 0 - N (dilation y rho v) i 0) := by ring\n      rw [heq, abs_neg]\n      exact h\n    rw [dist_eq_norm]\n    have hn := hnorm (rescaledForcing N y rho u - rescaledForcing N y rho v)\n    simp only [PiLp.sub_apply] at hn\n    dsimp [B]\n    nlinarith [hc 0, hc 1]\n  have hy : y ∈ Metric.ball y r1 := Metric.mem_ball_self hr1\n  have hbound (z : E2) (hz : z ∈ Metric.ball (0 : E2) 1) : ‖rescaledForcing N y rho z‖ ≤ B := by\n    have hc (i : Fin 2) : |rescaledForcing N y rho z i| ≤ (HN : ℝ) * rho ^ (alpha : ℝ) := by\n      have hd : dist y (dilation y rho z) ≤ rho := by\n        rw [dist_comm]\n        change dist (y + rho • z) y ≤ rho\n        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hrho]\n        have hz' : ‖z‖ < 1 := by\n          change dist z 0 < 1 at hz\n          rwa [dist_zero_right] at hz\n        nlinarith\n      have h := (holder i 0).dist_le_of_le hy (hin z hz) hd\n      rw [hcoord]\n      exact h\n    have hn := hnorm (rescaledForcing N y rho z)\n    dsimp [B]\n    linarith [hc 0, hc 1]\n  have hholder : HolderOnWith H alpha (rescaledForcing N y rho) (Metric.ball (0 : E2) 1) := by\n    intro u hu v hv\n    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg alpha.coe_nonneg,\n      ← ENNReal.ofReal_coe_nnreal]\n    change ENNReal.ofReal (dist (rescaledForcing N y rho u) (rescaledForcing N y rho v)) ≤\n      ENNReal.ofReal B * ENNReal.ofReal (dist u v ^ (alpha : ℝ))\n    rw [← ENNReal.ofReal_mul hB]\n    exact ENNReal.ofReal_le_ofReal (hdiff u hu v hv)\n  refine ⟨B, H, hB, hbound, hholder, ?_⟩\n  change B + B ≤ 4 * (HN : ℝ) * rho ^ (alpha : ℝ)\n  dsimp [B]\n  ring_nf\n  exact le_rfl\n)"))

/-- The actual planar Jacobian and the resulting original-alpha square-root bound. -/
theorem native_rescaled_error_energy (alpha : ℝ≥0) (y : E2) (rho : ℝ)
    (hrho : 0 < rho) (da : E2 → E2)
    (hda : MemLp (fun x => da x - coordinateVector 2 0) 2
      (volume.restrict (Metric.ball y rho)))
    (E : ℝ) (hE : 0 ≤ E)
    (energy : (∫ x in Metric.ball y rho, ‖da x - coordinateVector 2 0‖ ^ 2) ≤
      E * rho ^ (2 + 2 * (alpha : ℝ))) :
    MemLp (rescaledErrorGradient y rho da) 2
      (volume.restrict (Metric.ball (0 : E2) 1)) ∧
    IntegrableOn (fun x => ‖da x - coordinateVector 2 0‖ ^ 2) (Metric.ball y rho) ∧
    IntegrableOn (fun z => ‖rescaledErrorGradient y rho da z‖ ^ 2)
      (Metric.ball (0 : E2) 1) ∧
    (∫ z in Metric.ball (0 : E2) 1, ‖rescaledErrorGradient y rho da z‖ ^ 2) =
      (rho ^ (2 : ℕ))⁻¹ * (∫ x in Metric.ball y rho, ‖da x - coordinateVector 2 0‖ ^ 2) ∧
    Real.sqrt (∫ z in Metric.ball (0 : E2) 1, ‖rescaledErrorGradient y rho da z‖ ^ 2) ≤
      Real.sqrt E * rho ^ (alpha : ℝ) := by
  classical
  let d : E2 → E2 := fun x => da x - coordinateVector 2 0
  let f : E2 → E2 := dilation y rho
  let U : Set E2 := Metric.ball (0 : E2) 1
  let V : Set E2 := Metric.ball y rho
  let c : ℝ≥0∞ := ENNReal.ofReal ((rho ^ (2 : ℕ))⁻¹)
  have hf : Measurable f := by
    change Measurable (fun z : E2 => y + rho • z)
    fun_prop
  have hp : f ⁻¹' V = U := by
    ext z
    change dist (y + rho • z) y < rho ↔ dist z 0 < 1
    simp only [dist_eq_norm, add_sub_cancel_left, sub_zero, norm_smul,
      Real.norm_eq_abs, abs_of_pos hrho]
    constructor <;> intro h <;> nlinarith
  have hm : Measure.map f (volume : Measure E2) = c • volume := by
    calc
      Measure.map f volume = Measure.map (fun x : E2 => y + x)
          (Measure.map (fun z : E2 => rho • z) volume) :=
        (Measure.map_map (by fun_prop) (by fun_prop)).symm
      _ = Measure.map (fun x : E2 => y + x) (c • volume) := by
        congr 1
        simpa only [c, finrank_euclideanSpace_fin,
          abs_of_nonneg (inv_nonneg.mpr (sq_nonneg rho))] using
          (Measure.map_addHaar_smul (volume : Measure E2) hrho.ne')
      _ = c • volume := by
        rw [Measure.map_smul c (by fun_prop),
          (measurePreserving_add_left (volume : Measure E2) y).map_eq]
  have hmr : Measure.map f (volume.restrict U) = c • volume.restrict V := by
    rw [← hp, ← Measure.restrict_map hf (measurableSet_ball), hm, Measure.restrict_smul]
  have hdm : MemLp d 2 (Measure.map f (volume.restrict U)) := by
    rw [hmr]
    exact hda.smul_measure ENNReal.ofReal_ne_top
  have hdu : MemLp (d ∘ f) 2 (volume.restrict U) := hdm.comp_of_map hf.aemeasurable
  have hdi : Integrable (fun x => ‖d x‖ ^ (2 : ℕ)) (volume.restrict V) :=
    hda.integrable_norm_pow (by decide)
  have hdui : Integrable (fun z => ‖d (f z)‖ ^ (2 : ℕ)) (volume.restrict U) :=
    hdu.integrable_norm_pow (by decide)
  have hdmi : Integrable (fun x => ‖d x‖ ^ (2 : ℕ))
      (Measure.map f (volume.restrict U)) := hdm.integrable_norm_pow (by decide)
  have hj : (∫ z in U, ‖d (f z)‖ ^ (2 : ℕ)) =
      (rho ^ (2 : ℕ))⁻¹ * (∫ x in V, ‖d x‖ ^ (2 : ℕ)) := by
    rw [← integral_map hf.aemeasurable hdmi.aestronglyMeasurable,
      hmr, integral_smul_measure]
    change (ENNReal.ofReal ((rho ^ (2 : ℕ))⁻¹)).toReal •
      (∫ x in V, ‖d x‖ ^ (2 : ℕ)) = _
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg rho)), smul_eq_mul]
  change MemLp (d ∘ f) 2 (volume.restrict U) ∧
    Integrable (fun x => ‖d x‖ ^ (2 : ℕ)) (volume.restrict V) ∧
    Integrable (fun z => ‖d (f z)‖ ^ (2 : ℕ)) (volume.restrict U) ∧
    (∫ z in U, ‖d (f z)‖ ^ (2 : ℕ)) =
      (rho ^ (2 : ℕ))⁻¹ * (∫ x in V, ‖d x‖ ^ (2 : ℕ)) ∧
    Real.sqrt (∫ z in U, ‖d (f z)‖ ^ (2 : ℕ)) ≤ Real.sqrt E * rho ^ (alpha : ℝ)
  refine ⟨hdu, hdi, hdui, hj, ?_⟩
  apply (Real.sqrt_le_left (mul_nonneg (Real.sqrt_nonneg E)
    (Real.rpow_nonneg hrho.le _))).mpr
  rw [mul_pow, Real.sq_sqrt hE, hj]
  have hpow : rho ^ (2 + 2 * (alpha : ℝ)) = rho ^ (2 : ℕ) * (rho ^ (alpha : ℝ)) ^ 2 := by
    rw [Real.rpow_add hrho, Real.rpow_two]
    congr 1
    rw [mul_comm (2 : ℝ), Real.rpow_mul hrho.le, Real.rpow_two]
  calc
    (rho ^ (2 : ℕ))⁻¹ * (∫ x in V, ‖d x‖ ^ (2 : ℕ)) ≤
        (rho ^ (2 : ℕ))⁻¹ * (E * rho ^ (2 + 2 * (alpha : ℝ))) :=
      mul_le_mul_of_nonneg_left energy (inv_nonneg.mpr (sq_nonneg rho))
    _ = ((rho ^ (2 : ℕ))⁻¹ * rho ^ (2 : ℕ)) * (E * (rho ^ (alpha : ℝ)) ^ 2) := by
      rw [hpow]
      ring
    _ = E * (rho ^ (alpha : ℝ)) ^ 2 := by
      rw [inv_mul_cancel₀ (pow_ne_zero 2 hrho.ne'), one_mul]


end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower
