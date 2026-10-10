import WeakDivergenceData
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import BridgeHelpers

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.WeakSchauder

/-- Witness-independent weak equation, energy and excess on actual balls. -/
theorem weak_data_independent (center : V) (R : ℝ) (hR : 0 < R)
    (a : V → Mat) (v : V → ℝ)
    (h₁ h₂ : H1Witness v (Metric.ball center R)) :
    (WeakEquation a h₁ ↔ WeakEquation a h₂) ∧
    (∀ x r, Metric.ball x r ⊆ Metric.ball center R →
      energy h₁.weakGrad x r = energy h₂.weakGrad x r ∧
      ballMean h₁.weakGrad x r = ballMean h₂.weakGrad x r ∧
      excess h₁.weakGrad x r = excess h₂.weakGrad x r) := by
  have hgrad := DeGiorgi.MemW1pWitness.ae_eq Metric.isOpen_ball h₁ h₂
  constructor
  · have transfer (h : WeakEquation a h₁) : WeakEquation a h₂ := by
      intro φ hφ htest
      have heq : (fun x => inner ℝ (DeGiorgi.matMulE (a x) (h₁.weakGrad x))
          (htest.weakGrad x)) =ᵐ[volume.restrict (Metric.ball center R)]
          (fun x => inner ℝ (DeGiorgi.matMulE (a x) (h₂.weakGrad x)) (htest.weakGrad x)) := by
        filter_upwards [hgrad] with x hx
        rw [hx]
      exact ⟨((h φ hφ htest).1.congr heq),
        (integral_congr_ae heq.symm).trans (h φ hφ htest).2⟩
    constructor
    · exact transfer
    · intro h
      intro φ hφ htest
      have heq : (fun x => inner ℝ (DeGiorgi.matMulE (a x) (h₂.weakGrad x))
          (htest.weakGrad x)) =ᵐ[volume.restrict (Metric.ball center R)]
          (fun x => inner ℝ (DeGiorgi.matMulE (a x) (h₁.weakGrad x)) (htest.weakGrad x)) := by
        filter_upwards [hgrad] with x hx
        rw [hx]
      exact ⟨((h φ hφ htest).1.congr heq),
        (integral_congr_ae heq.symm).trans (h φ hφ htest).2⟩
  · intro x r hball
    have hg := hgrad.filter_mono (ae_mono (Measure.restrict_mono_set volume hball))
    have hm : ballMean h₁.weakGrad x r = ballMean h₂.weakGrad x r := by
      unfold ballMean
      rw [integral_congr_ae hg]
    refine ⟨?_, hm, ?_⟩
    · apply integral_congr_ae
      filter_upwards [hg] with y hy
      rw [hy]
    · unfold excess
      rw [hm]
      apply integral_congr_ae
      filter_upwards [hg] with y hy
      rw [hy]

/-- No circular all-test hypothesis is needed when only the smooth weak
identity is supplied: H₀¹ approximation upgrades it under genuine L² bounds. -/
theorem smooth_tests_iff_H01_tests (center : V) (R κ Λ : ℝ) (hR : 0 < R)
    (a : V → Mat) (ha : CoefficientBounds a (Metric.ball center R) κ Λ)
    (v : V → ℝ) (hv : H1Witness v (Metric.ball center R)) :
    SmoothWeakEquation a hv.weakGrad (Metric.ball center R) ↔ WeakEquation a hv := by
  classical
  constructor
  · intro hs φ hφ htest
    obtain ⟨hw, seq, hseqsmooth, hseqcompact, hseqsub, hseqfun, hseqgrad⟩ := hφ.2
    let flux : Fin 3 → V → ℝ := fun i x => DeGiorgi.matMulE (a x) (hv.weakGrad x) i
    have hflux : ∀ i, MemLp (flux i) 2 (volume.restrict (Metric.ball center R)) :=
      fun i => flux_component_memLp _ Metric.isOpen_ball.measurableSet a κ Λ ha
        hv.weakGrad hv.weakGrad_memLp i
    let deriv : ℕ → Fin 3 → V → ℝ :=
      fun n i x => (fderiv ℝ (seq n) x) (EuclideanSpace.single i 1)
    have hd : ∀ n i, MemLp (deriv n i) 2 (volume.restrict (Metric.ball center R)) := by
      intro n i
      exact ((hseqsmooth n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)
        |>.clm_apply contDiff_const |>.continuous.memLp_of_hasCompactSupport
          ((hseqcompact n).fderiv_apply (𝕜 := ℝ) _)).restrict _
    have hint : ∀ i, Integrable (fun x => flux i x * hw.weakGrad x i)
        (volume.restrict (Metric.ball center R)) :=
      fun i => (hflux i).integrable_mul (hw.weakGrad_component_memLp i)
    have hintseq : ∀ n i, Integrable (fun x => flux i x * deriv n i x)
        (volume.restrict (Metric.ball center R)) :=
      fun n i => (hflux i).integrable_mul (hd n i)
    have ht := tendsto_finsetSum Finset.univ (fun i hi =>
      integral_mul_tendsto_of_eLpNorm (volume.restrict (Metric.ball center R))
        (flux i) (fun x => hw.weakGrad x i) (fun n => deriv n i)
        (hflux i) (hw.weakGrad_component_memLp i) (fun n => hd n i) (hseqgrad i))
    have hzero : (fun n => ∑ i : Fin 3, ∫ x in Metric.ball center R,
        flux i x * deriv n i x) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      rw [← integral_finsetSum Finset.univ (fun i hi => hintseq n i)]
      exact (hs (seq n) (hseqsmooth n) (hseqcompact n) (hseqsub n)).2
    rw [hzero] at ht
    have heqzero : (∑ i : Fin 3, ∫ x in Metric.ball center R,
        flux i x * hw.weakGrad x i) = 0 :=
      tendsto_nhds_unique ht tendsto_const_nhds
    have hgrad := DeGiorgi.MemW1pWitness.ae_eq Metric.isOpen_ball hw htest
    have heq : (fun x => ∑ i : Fin 3, flux i x * hw.weakGrad x i)
        =ᵐ[volume.restrict (Metric.ball center R)]
        (fun x => inner ℝ (DeGiorgi.matMulE (a x) (hv.weakGrad x)) (htest.weakGrad x)) := by
      filter_upwards [hgrad] with x hx
      rw [hx]
      simp [flux, PiLp.inner_apply, mul_comm]
    refine ⟨(integrable_finsetSum Finset.univ (fun i hi => hint i)).congr heq, ?_⟩
    rw [← integral_congr_ae heq, integral_finsetSum Finset.univ (fun i hi => hint i)]
    exact heqzero
  · intro hw φ hφ hφcompact hφsub
    let hcanonical : H1Witness φ (Metric.ball center R) :=
      (DeGiorgi.MemW1pWitness.ofContDiffHasCompactSupport (p := 2) hφ hφcompact).restrict
        Metric.isOpen_ball (Set.subset_univ _)
    have h01 : DeGiorgi.MemH01 φ (Metric.ball center R) :=
      DeGiorgi.memW01p_of_contDiff_hasCompactSupport_subset Metric.isOpen_ball
        hφ hφcompact hφsub
    have heq : (fun x => inner ℝ (DeGiorgi.matMulE (a x) (hv.weakGrad x))
        (hcanonical.weakGrad x)) = (fun x => ∑ i : Fin 3,
        DeGiorgi.matMulE (a x) (hv.weakGrad x) i *
        (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
      funext x
      simp [hcanonical, DeGiorgi.MemW1pWitness.restrict,
        DeGiorgi.MemW1pWitness.ofContDiffHasCompactSupport, PiLp.inner_apply, mul_comm]
    simpa only [heq] using hw φ h01 hcanonical

/-- Restrict actual Sobolev witnesses and the homogeneous equation to a ball. -/
theorem weak_equation_restrict (a : V → Mat) (Ω : Set V) (hΩ : IsOpen Ω)
    (v : V → ℝ) (hv : H1Witness v Ω) (hweak : WeakEquation a hv)
    (center : V) (R : ℝ) (hR : 0 < R) (hball : Metric.ball center R ⊆ Ω) :
    ∃ hsmall : H1Witness v (Metric.ball center R),
      (∀ x, hsmall.weakGrad x = hv.weakGrad x) ∧ WeakEquation a hsmall := by
  classical
  refine ⟨hv.restrict Metric.isOpen_ball hball, fun _ => rfl, ?_⟩
  intro φ hφ htest
  obtain ⟨hext, h01, hextgrad⟩ := h01_zero_extension_to_superset
    (Metric.ball center R) Ω Metric.isOpen_ball hΩ hball φ hφ htest
  have htesteq := hweak ((Metric.ball center R).indicator φ) h01 hext
  let integrand : V → ℝ := fun x => inner ℝ
    (DeGiorgi.matMulE (a x) (hv.weakGrad x)) (htest.weakGrad x)
  have heq : (fun x => inner ℝ (DeGiorgi.matMulE (a x) (hv.weakGrad x))
      (hext.weakGrad x)) = (Metric.ball center R).indicator integrand := by
    funext x
    rw [hextgrad]
    by_cases hx : x ∈ Metric.ball center R <;> simp [hx, integrand]
  rw [heq] at htesteq
  have hmeasure : (volume.restrict Ω).restrict (Metric.ball center R) =
      volume.restrict (Metric.ball center R) := by
    rw [Measure.restrict_restrict Metric.isOpen_ball.measurableSet,
      Set.inter_eq_left.mpr hball]
  have hi := (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mp htesteq.1
  change Integrable integrand ((volume.restrict Ω).restrict (Metric.ball center R)) at hi
  rw [hmeasure] at hi
  have he : (∫ x in Ω, (Metric.ball center R).indicator integrand x) =
      ∫ x in Metric.ball center R, integrand x := by
    rw [integral_indicator Metric.isOpen_ball.measurableSet, hmeasure]
  exact ⟨hi, he.symm.trans htesteq.2⟩

end SeifertSurfaces.WeakSchauder
