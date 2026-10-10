import WeakDivergenceData
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

noncomputable section
open Set MeasureTheory Filter Function Metric
open scoped Topology Convolution ContDiff
namespace SeifertSurfaces.WeakSchauder

set_option maxHeartbeats 3000000

private lemma mollified_weak_derivative
    (Ω : Set V) (hΩ : IsOpen Ω) (v : V → ℝ) (hv : H1Witness v Ω)
    (G : V → V) (hGae : G =ᵐ[volume.restrict Ω] hv.weakGrad)
    (φ : ContDiffBump (0 : V)) (x : V)
    (hball : closedBall x φ.rOut ⊆ Ω) :
    HasFDerivAt (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Ω.indicator v)
      (innerSL ℝ ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Ω.indicator G) x)) x := by
  classical
  let f := Ω.indicator v
  let g := Ω.indicator G
  let ρ := φ.normed volume
  have hfLp : MemLp f 2 volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).mpr hv.memLp
  have hgLp : MemLp g 2 volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).mpr
    ((MemLp.of_eval_piLp hv.weakGrad_component_memLp).ae_eq hGae.symm)
  have hf : LocallyIntegrable f volume := hfLp.locallyIntegrable (by norm_num)
  have hg : LocallyIntegrable g volume := hgLp.locallyIntegrable (by norm_num)
  have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := φ.contDiff_normed
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport_normed
  have hd := hρc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hρ.of_le (by simp)) hf x
  suffices heq : innerSL ℝ ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) =
      (fderiv ℝ ρ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL V, volume] f) x by
    rw [← heq] at hd
    exact hd
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
  intro i
  change innerSL ℝ ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
    (EuclideanSpace.basisFun (Fin 3) ℝ i) =
    ((fderiv ℝ ρ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL V, volume] f) x)
      (EuclideanSpace.basisFun (Fin 3) ℝ i)
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
  have hψder (y : V) : (fderiv ℝ ψ y) ei = -(fderiv ℝ ρ (x - y)) ei := by
    have hdψ := (hρ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    have hfun : ρ ∘ ((fun _ : V => x) - id) = ψ := rfl
    rw [hfun] at hdψ
    rw [hdψ.fderiv]
    simp [ei]
  have hw := hv.isWeakGrad i ψ hψ hψc hψsub
  have hweak : (∫ y in Ω, v y * (fderiv ℝ ρ (x - y)) ei) =
      ∫ y in Ω, G y i * ρ (x - y) := by
    change (∫ y in Ω, v y * (fderiv ℝ ψ y) ei) = -∫ y in Ω, hv.weakGrad y i * ψ y at hw
    simp_rw [hψder, mul_neg, integral_neg] at hw
    have hw' := neg_injective hw
    rw [hw']
    apply integral_congr_ae
    filter_upwards [hGae] with y hy
    simp only [ψ, hy]
  have hdc : HasCompactSupport (fderiv ℝ ρ) := hρc.fderiv ℝ
  have hdcont : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv (by simp)
  have hdint : Integrable (fun y =>
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL V) (fderiv ℝ ρ (x - y)) (f y)) volume := by
    have hi := hdc.convolutionExists_left ((ContinuousLinearMap.lsmul ℝ ℝ).precompL V)
      hdcont hf x
    have his := convolutionExistsAt_flip.mpr hi
    simpa [ConvolutionExistsAt, ContinuousLinearMap.flip_apply] using his
  have hgint : Integrable (fun y => ρ (x - y) • g y) volume := by
    have hi := hρc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ.continuous hg x
    have his := convolutionExistsAt_flip.mpr hi
    simpa [ConvolutionExistsAt, ContinuousLinearMap.flip_apply] using his
  change innerSL ℝ ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) ei =
    ((fderiv ℝ ρ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL V, volume] f) x) ei
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

private lemma continuous_indicator_at {F : Type*} [Zero F] [TopologicalSpace F]
    (Ω : Set V) (hΩ : IsOpen Ω) (f : V → F) (hf : ContinuousOn f Ω)
    {x : V} (hx : x ∈ Ω) : ContinuousAt (Ω.indicator f) x := by
  exact (hf.continuousAt (hΩ.mem_nhds hx)).congr
    ((show ∀ᶠ y in 𝓝 x, y ∈ Ω from hΩ.mem_nhds hx).mono fun y hy =>
      (Set.indicator_of_mem hy f).symm)

theorem continuous_weak_gradient_hasFDerivAt
    (Ω : Set V) (hΩ : IsOpen Ω) (v : V → ℝ) (hv : H1Witness v Ω)
    (hcont : ContinuousOn v Ω) (G : V → V) (hGcont : ContinuousOn G Ω)
    (hGae : G =ᵐ[volume.restrict Ω] hv.weakGrad) (x : V) (hx : x ∈ Ω) :
    HasFDerivAt v (innerSL ℝ (G x)) x := by
  classical
  let f := Ω.indicator v
  let g := Ω.indicator G
  have hfLp : MemLp f 2 volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).mpr hv.memLp
  have hgLp : MemLp g 2 volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).mpr
      ((MemLp.of_eval_piLp hv.weakGrad_component_memLp).ae_eq hGae.symm)
  let φ : ℕ → ContDiffBump (0 : V) := fun n =>
    { rIn := (1 / ((n : ℝ) + 1)) / 2
      rOut := 1 / ((n : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by apply half_lt_self; positivity }
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hfc : ∀ y ∈ Ω, ContinuousAt f y := fun y hy =>
    continuous_indicator_at Ω hΩ v hcont hy
  have hgc : ContinuousAt g x := continuous_indicator_at Ω hΩ G hGcont hx
  have hgconv : Tendsto (fun p : ℕ × V =>
      ((φ p.1).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (g x)) := by
    exact ContDiffBump.convolution_tendsto_right (hφ.comp tendsto_fst)
      (Filter.Eventually.of_forall fun _ => hgLp.aestronglyMeasurable)
      (hgc.tendsto.comp tendsto_snd) tendsto_snd
  have hderconv : Tendsto (fun p : ℕ × V => innerSL ℝ
      (((φ p.1).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) p.2))
      (atTop ×ˢ 𝓝 x) (𝓝 (innerSL ℝ (g x))) :=
    (innerSL ℝ).continuous.continuousAt.tendsto.comp hgconv
  have hderg : Tendsto (fun p : ℕ × V => innerSL ℝ (g p.2))
      (atTop ×ˢ 𝓝 x) (𝓝 (innerSL ℝ (g x))) :=
    ((innerSL ℝ).continuous.continuousAt.tendsto.comp hgc.tendsto).comp tendsto_snd
  have huniform : TendstoUniformlyOnFilter (fun n y => innerSL ℝ
      (((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y))
      (fun y => innerSL ℝ (g y)) atTop (𝓝 x) := by
    rw [tendstoUniformlyOnFilter_iff_tendsto]
    exact (hderg.prodMk_nhds hderconv).mono_right (nhds_le_uniformity _)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hsmall : ∀ᶠ n in atTop, (φ n).rOut < δ / 2 :=
    hφ.eventually (Iio_mem_nhds (half_pos hδ))
  have hnear : ∀ᶠ y in 𝓝 x, dist y x < δ / 2 :=
    Metric.ball_mem_nhds x (half_pos hδ)
  have hder : ∀ᶠ p : ℕ × V in atTop ×ˢ 𝓝 x,
      HasFDerivAt ((φ p.1).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f)
        (innerSL ℝ (((φ p.1).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) p.2)) p.2 := by
    filter_upwards [hsmall.prod_mk hnear] with p hp
    apply mollified_weak_derivative Ω hΩ v hv G hGae (φ p.1) p.2
    intro y hy
    apply hδsub
    have hdist := dist_triangle y p.2 x
    have hy' := mem_closedBall.mp hy
    change dist y x < δ
    linarith [hp.1, hp.2]
  have hpoint : ∀ᶠ y in 𝓝 x, Tendsto (fun n =>
      ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y)
      atTop (𝓝 (f y)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact ContDiffBump.convolution_tendsto_right hφ
      (Filter.Eventually.of_forall fun _ => hfLp.aestronglyMeasurable)
      ((hfc y hy).tendsto.comp tendsto_snd) tendsto_const_nhds
  have hresult := hasFDerivAt_of_tendstoUniformlyOnFilter huniform hder hpoint
  have hfv : f =ᶠ[𝓝 x] v :=
    (show ∀ᶠ y in 𝓝 x, y ∈ Ω from hΩ.mem_nhds hx).mono fun y hy => Set.indicator_of_mem hy v
  simpa [g, hx] using hresult.congr_of_eventuallyEq hfv.symm

end SeifertSurfaces.WeakSchauder
