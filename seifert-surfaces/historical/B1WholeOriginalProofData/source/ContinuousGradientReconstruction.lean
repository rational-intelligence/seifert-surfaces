import IsothermalPDEData

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower
open SeifertSurfaces.AppendixACoordinates

/-- Reconstruction of the same native H1 scalar on the full ball from its
supplied continuous almost-everywhere weak-gradient representative. -/
theorem native_continuous_weak_gradient_reconstruction
    (r : ℝ) (radius_positive : 0 < r)
    (v : E2 → ℝ) (dv G : E2 → E2)
    (native_h1 : H1On (Metric.ball (0 : E2) r) v dv)
    (gradient_continuous : ContinuousOn G (Metric.ball (0 : E2) r))
    (gradient_ae : G =ᵐ[volume.restrict (Metric.ball (0 : E2) r)] dv) :
    ∃ u : E2 → ℝ,
      u =ᵐ[volume.restrict (Metric.ball (0 : E2) r)] v ∧
      ContDiffOn ℝ 1 u (Metric.ball (0 : E2) r) ∧
      ∀ z ∈ Metric.ball (0 : E2) r,
        HasFDerivAt u (innerSL ℝ (G z)) z ∧ planarGradient u z = G z := by
  open Filter Function Metric in
  open scoped Topology Convolution in
    classical
    let Ω := Metric.ball (0 : E2) r
    have hΩ : IsOpen Ω := Metric.isOpen_ball
    have hmoll (φ : ContDiffBump (0 : E2)) (x : E2)
        (hball : Metric.closedBall x φ.rOut ⊆ Ω) :
        HasFDerivAt (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Ω.indicator v)
          (innerSL ℝ ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            Ω.indicator G) x)) x := by
      classical
      let f := Ω.indicator v
      let g := Ω.indicator G
      let ρ := φ.normed volume
      have hfLp : MemLp f 2 volume :=
        (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).mpr native_h1.2.1
      have hgLp : MemLp g 2 volume :=
        (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).mpr
        (native_h1.2.2.ae_eq gradient_ae.symm)
      have hf : LocallyIntegrable f volume := hfLp.locallyIntegrable (by norm_num)
      have hg : LocallyIntegrable g volume := hgLp.locallyIntegrable (by norm_num)
      have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := φ.contDiff_normed
      have hρc : HasCompactSupport ρ := φ.hasCompactSupport_normed
      have hd := hρc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
        (hρ.of_le (by simp)) hf x
      suffices heq : innerSL ℝ ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) =
          (fderiv ℝ ρ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL E2, volume] f) x by
        rw [← heq] at hd
        exact hd
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ext
      intro i
      change innerSL ℝ ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
        (EuclideanSpace.basisFun (Fin 2) ℝ i) =
        ((fderiv ℝ ρ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL E2, volume] f) x)
          (EuclideanSpace.basisFun (Fin 2) ℝ i)
      rw [EuclideanSpace.basisFun_apply]
      let ei := EuclideanSpace.single i (1 : ℝ)
      let ψ := fun y => ρ (x - y)
      have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hρ.comp (contDiff_const.sub contDiff_id)
      have hψc : HasCompactSupport ψ := hρc.comp_homeomorph (Homeomorph.subLeft x)
      have hψsub : tsupport ψ ⊆ Ω := by
        apply Set.Subset.trans _ hball
        have hpre := tsupport_comp_subset_preimage (f := fun y => x - y) ρ
          (continuous_const.sub continuous_id)
        intro y hy
        have hy' := hpre hy
        change x - y ∈ tsupport ρ at hy'
        rw [φ.tsupport_normed_eq] at hy'
        simpa [mem_closedBall, dist_eq_norm_sub, norm_sub_rev] using hy'
      have hψder (y : E2) : (fderiv ℝ ψ y) ei = -(fderiv ℝ ρ (x - y)) ei := by
        have hdψ := (hρ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
          ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
        have hfun : ρ ∘ ((fun _ : E2 => x) - id) = ψ := rfl
        rw [hfun] at hdψ
        rw [hdψ.fderiv]
        simp [ei]
      have hw := native_h1.1.2.2 ψ hψ hψc hψsub i
      have hweak : (∫ y in Ω, v y * (fderiv ℝ ρ (x - y)) ei) =
          ∫ y in Ω, G y i * ρ (x - y) := by
        change (∫ y in Ω, v y * (fderiv ℝ ψ y) ei) = -∫ y in Ω, dv y i * ψ y at hw
        simp_rw [hψder, mul_neg, integral_neg] at hw
        have hw' := neg_injective hw
        rw [hw']
        apply integral_congr_ae
        filter_upwards [gradient_ae] with y hy
        simp only [ψ, hy]
      have hdc : HasCompactSupport (fderiv ℝ ρ) := hρc.fderiv ℝ
      have hdcont : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv (by simp)
      have hdint : Integrable (fun y =>
          ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E2) (fderiv ℝ ρ (x - y)) (f y)) volume := by
        have hi := hdc.convolutionExists_left ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E2)
          hdcont hf x
        have his := convolutionExistsAt_flip.mpr hi
        simpa [ConvolutionExistsAt, ContinuousLinearMap.flip_apply] using his
      have hgint : Integrable (fun y => ρ (x - y) • g y) volume := by
        have hi := hρc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ.continuous hg x
        have his := convolutionExistsAt_flip.mpr hi
        simpa [ConvolutionExistsAt, ContinuousLinearMap.flip_apply] using his
      change innerSL ℝ ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) ei =
        ((fderiv ℝ ρ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL E2, volume] f) x) ei
      rw [convolution_eq_swap, convolution_eq_swap,
        ContinuousLinearMap.integral_apply hdint]
      simp only [ContinuousLinearMap.lsmul_apply]
      change innerSL ℝ (∫ y, ρ (x - y) • g y) ei = _
      rw [show (innerSL ℝ (∫ y, ρ (x - y) • g y)) ei =
          (∫ y, ρ (x - y) • g y) i by
            simp [ei, innerSL_apply_apply, PiLp.inner_apply, EuclideanSpace.single]]
      rw [eval_integral_piLp hgint.eval_piLp]
      simp only [ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.precompL_apply,
        PiLp.smul_apply, smul_eq_mul]
      have hleft : (fun y => ρ (x - y) * g y i) = Ω.indicator
          (fun y => G y i * ρ (x - y)) := by
        ext y
        by_cases hy : y ∈ Ω <;> simp [g, hy, mul_comm]
      have hright : (fun y => (fderiv ℝ ρ (x - y)) ei * f y) = Ω.indicator
          (fun y => v y * (fderiv ℝ ρ (x - y)) ei) := by
        ext y
        by_cases hy : y ∈ Ω <;> simp [f, hy, mul_comm]
      rw [hleft, hright, integral_indicator hΩ.measurableSet,
        integral_indicator hΩ.measurableSet]
      exact hweak.symm
    let f := Ω.indicator v
    let g := Ω.indicator G
    have hfLp : MemLp f 2 volume :=
      (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).mpr native_h1.2.1
    have hgLp : MemLp g 2 volume :=
      (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).mpr
        (native_h1.2.2.ae_eq gradient_ae.symm)
    let φ : ℕ → ContDiffBump (0 : E2) := fun n =>
      { rIn := (1 / ((n : ℝ) + 1)) / 2
        rOut := 1 / ((n : ℝ) + 1)
        rIn_pos := by positivity
        rIn_lt_rOut := by apply half_lt_self; positivity }
    have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    let F : ℕ → E2 → ℝ := fun n =>
      (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
    let D : ℕ → E2 → E2 →L[ℝ] ℝ := fun n y => innerSL ℝ
      (((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y)
    have hae : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
      apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ
        (K := 2) _ (hfLp.locallyIntegrable (by norm_num))
      exact Eventually.of_forall (fun n => by dsimp [φ]; linarith)
    have hgc (x : E2) (hx : x ∈ Ω) : ContinuousAt g x := by
      exact (gradient_continuous.continuousAt (hΩ.mem_nhds hx)).congr
        ((show ∀ᶠ y in 𝓝 x, y ∈ Ω from hΩ.mem_nhds hx).mono fun y hy =>
          (Set.indicator_of_mem hy G).symm)
    have hdlim (x : E2) (hx : x ∈ Ω) :
        Tendsto (fun p : ℕ × E2 => D p.1 p.2)
          (atTop ×ˢ 𝓝 x) (𝓝 (innerSL ℝ (g x))) := by
      have hc : Tendsto (fun p : ℕ × E2 =>
          ((φ p.1).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) p.2)
          (atTop ×ˢ 𝓝 x) (𝓝 (g x)) :=
        ContDiffBump.convolution_tendsto_right (hφ.comp tendsto_fst)
          (Eventually.of_forall fun _ => hgLp.aestronglyMeasurable)
          ((hgc x hx).tendsto.comp tendsto_snd) tendsto_snd
      exact (innerSL ℝ).continuous.continuousAt.tendsto.comp hc
    have hder (x : E2) (hx : x ∈ Ω) :
        ∀ᶠ p : ℕ × E2 in atTop ×ˢ 𝓝 x, HasFDerivAt (F p.1) (D p.1 p.2) p.2 := by
      obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hΩ x hx
      have hsmall : ∀ᶠ n in atTop, (φ n).rOut < δ / 2 :=
        hφ.eventually (Iio_mem_nhds (half_pos hδ))
      have hnear : ∀ᶠ y in 𝓝 x, dist y x < δ / 2 :=
        Metric.ball_mem_nhds x (half_pos hδ)
      filter_upwards [hsmall.prod_mk hnear] with p hp
      apply hmoll
      intro y hy
      apply hδsub
      have hdist := dist_triangle y p.2 x
      have hy' := mem_closedBall.mp hy
      change dist y x < δ
      linarith [hp.1, hp.2]
    have hcauchy (x : E2) (hx : x ∈ Ω) : CauchySeq (fun n => F n x) := by
      let M : ℝ := ‖innerSL ℝ (g x)‖ + 1
      have hM : 0 < M := by dsimp [M]; positivity
      have hb : ∀ᶠ p : ℕ × E2 in atTop ×ˢ 𝓝 x, ‖D p.1 p.2‖ < M :=
        (hdlim x hx).norm.eventually (Iio_mem_nhds (by dsimp [M]; linarith))
      obtain ⟨a, ha, b, hb, hab⟩ := eventually_prod_iff.mp ((hder x hx).and hb)
      obtain ⟨N, hN⟩ := eventually_atTop.mp ha
      obtain ⟨δ, hδ, hδb⟩ := Metric.nhds_basis_ball.eventually_iff.mp hb
      have hcontrol (n : ℕ) (hn : N ≤ n) (y : E2) (hy : y ∈ ball x δ) :
          HasFDerivAt (F n) (D n y) y ∧ ‖D n y‖ ≤ M :=
        ⟨(hab (hN n hn) (hδb hy)).1, (hab (hN n hn) (hδb hy)).2.le⟩
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have he : 0 < min δ (ε / (4 * M)) := lt_min hδ (by positivity)
      obtain ⟨y, hy, hyl⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
        (ne_of_gt (measure_ball_pos volume x he)) (ae_restrict_of_ae hae)
      have hyd : y ∈ ball x δ := Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _))
      have hye : dist y x < ε / (4 * M) :=
        lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _)
      have hMdist : M * dist y x < ε / 4 := by
        have := (lt_div_iff₀ (by positivity : 0 < 4 * M)).mp hye
        nlinarith
      have hdist (n : ℕ) (hn : N ≤ n) : dist (F n y) (F n x) < ε / 4 := by
        have hi := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
          (fun z hz => (hcontrol n hn z hz).1.hasFDerivWithinAt)
          (fun z hz => (hcontrol n hn z hz).2) (convex_ball x δ)
          (Metric.mem_ball_self hδ) hyd
        rw [dist_eq_norm] at hMdist ⊢
        exact hi.trans_lt hMdist
      obtain ⟨N', hN'⟩ := Metric.cauchySeq_iff.mp hyl.cauchySeq (ε / 2) (half_pos hε)
      refine ⟨max N N', fun m hm n hn => ?_⟩
      have hmN := (le_max_left N N').trans hm
      have hnN := (le_max_left N N').trans hn
      have hmn := hN' m ((le_max_right N N').trans hm) n
        ((le_max_right N N').trans hn)
      have ht1 := dist_triangle (F m x) (F m y) (F n x)
      have ht2 := dist_triangle (F m y) (F n y) (F n x)
      have hm' := hdist m hmN
      have hn' := hdist n hnN
      rw [dist_comm (F m y)] at hm'
      linarith
    let u : E2 → ℝ := fun x => limUnder atTop (fun n => F n x)
    have hu (x : E2) (hx : x ∈ Ω) : Tendsto (fun n => F n x) atTop (𝓝 (u x)) := by
      exact (hcauchy x hx).tendsto_limUnder
    have hu_der (x : E2) (hx : x ∈ Ω) : HasFDerivAt u (innerSL ℝ (G x)) x := by
      have hderg : Tendsto (fun p : ℕ × E2 => innerSL ℝ (g p.2))
          (atTop ×ˢ 𝓝 x) (𝓝 (innerSL ℝ (g x))) :=
        ((innerSL ℝ).continuous.continuousAt.tendsto.comp (hgc x hx).tendsto).comp tendsto_snd
      have huniform : TendstoUniformlyOnFilter D (fun y => innerSL ℝ (g y)) atTop (𝓝 x) := by
        rw [tendstoUniformlyOnFilter_iff_tendsto]
        exact (hderg.prodMk_nhds (hdlim x hx)).mono_right (nhds_le_uniformity _)
      have hpoint : ∀ᶠ y in 𝓝 x, Tendsto (fun n => F n y) atTop (𝓝 (u y)) :=
        (show ∀ᶠ y in 𝓝 x, y ∈ Ω from hΩ.mem_nhds hx).mono (fun y hy => hu y hy)
      simpa [g, hx] using hasFDerivAt_of_tendstoUniformlyOnFilter huniform (hder x hx) hpoint
    refine ⟨u, ?_, ?_, ?_⟩
    · filter_upwards [ae_restrict_of_ae hae, self_mem_ae_restrict hΩ.measurableSet] with x hx hxΩ
      have h := tendsto_nhds_unique (hu x hxΩ) hx
      exact h.trans (Set.indicator_of_mem hxΩ v)
    · rw [show (1 : ℕ∞ω) = 0 + 1 by rfl,
        contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hΩ.uniqueDiffOn]
      refine ⟨by simp, (fun x => innerSL ℝ (G x)), ?_, fun x hx => (hu_der x hx).hasFDerivWithinAt⟩
      exact contDiffOn_zero.mpr ((innerSL ℝ).continuous.comp_continuousOn gradient_continuous)
    · intro z hz
      refine ⟨hu_der z hz, ?_⟩
      ext i
      fin_cases i <;> simp [planarGradient, (hu_der z hz).fderiv,
        Fin.sum_univ_two, coordinateVector, innerSL_apply_apply, PiLp.inner_apply]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower
