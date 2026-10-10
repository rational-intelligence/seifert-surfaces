import WeakDivergenceData
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.WeakSchauder

/-- Actual coefficient flux components are square integrable on the declared domain. -/
theorem flux_component_memLp (Ω : Set V) (hΩ : MeasurableSet Ω) (a : V → Mat) (κ Λ : ℝ)
    (ha : CoefficientBounds a Ω κ Λ) (G : V → V)
    (hG : MemLp G 2 (volume.restrict Ω)) (i : Fin 3) :
    MemLp (fun x => DeGiorgi.matMulE (a x) (G x) i) 2 (volume.restrict Ω) := by
  apply MemLp.of_le_mul (g := G) (c := Λ) hG
  · have hcomp : ∀ j : Fin 3, AEStronglyMeasurable (fun x => G x j) (volume.restrict Ω) :=
      fun j => (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).comp_aestronglyMeasurable hG.aestronglyMeasurable
    simpa [DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct] using
      Finset.aestronglyMeasurable_fun_sum Finset.univ (fun j hj =>
        (ha.measurable i j).aestronglyMeasurable.mul (hcomp j))
  · filter_upwards [ae_restrict_mem₀ hΩ.nullMeasurableSet] with x hx
    have h := ha.mixed x hx (G x) (EuclideanSpace.single i 1)
    simpa [PiLp.inner_apply, EuclideanSpace.single, PiLp.single_apply,
      PiLp.norm_single, Real.norm_eq_abs] using h

/-- Pairing with a fixed actual L2 scalar is continuous for L2 approximation. -/
theorem integral_mul_tendsto_of_eLpNorm
    (μ : Measure V) (f g : V → ℝ) (seq : ℕ → V → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hseq : ∀ n, MemLp (seq n) 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => seq n x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f x * seq n x ∂μ) atTop (𝓝 (∫ x, f x * g x ∂μ)) := by
  have ht : Tendsto (fun n => (hseq n).toLp (seq n)) atTop (𝓝 (hg.toLp g)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' seq hseq g hg).mpr hlim
  have heq (z : V → ℝ) (hz : MemLp z 2 μ) :
      inner ℝ (hf.toLp f) (hz.toLp z) = ∫ x, f x * z x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hz.coeFn_toLp] with x hxf hxz
    simp [hxf, hxz, mul_comm]
  have hi := (tendsto_const_nhds (x := hf.toLp f)).inner (𝕜 := ℝ) ht
  simp only [heq] at hi
  exact hi

/-- A genuine zero extension remains an H₀¹ test on an open containing set,
with the displayed weak gradient equal everywhere to the zero extension. -/
theorem h01_zero_extension_to_superset (B Ω : Set V) (hB : IsOpen B) (hΩ : IsOpen Ω)
    (hsub : B ⊆ Ω) (φ : V → ℝ) (hφ : DeGiorgi.MemH01 φ B)
    (htest : H1Witness φ B) :
    ∃ hext : H1Witness (B.indicator φ) Ω,
      DeGiorgi.MemH01 (B.indicator φ) Ω ∧
      ∀ x, hext.weakGrad x = B.indicator htest.weakGrad x := by
  classical
  obtain ⟨hw, seq, hseqsmooth, hseqcompact, hseqsub, hseqfun, hseqgrad⟩ := hφ.2
  let hrawtest : DeGiorgi.MemW1pWitness (ENNReal.ofReal (2 : ℝ)) φ B :=
    { memLp := by simpa using htest.memLp
      weakGrad := htest.weakGrad
      weakGrad_component_memLp := fun i => by simpa using htest.weakGrad_component_memLp i
      isWeakGrad := htest.isWeakGrad }
  let hraw := DeGiorgi.zeroExtendMemW1pWitnessP (p := 2) (v := φ) hB (by norm_num)
    (by simpa using hφ) hrawtest
  let hwhole : H1Witness (B.indicator φ) Set.univ :=
    { memLp := by simpa using hraw.memLp
      weakGrad := hraw.weakGrad
      weakGrad_component_memLp := fun i => by simpa using hraw.weakGrad_component_memLp i
      isWeakGrad := hraw.isWeakGrad }
  let hext : H1Witness (B.indicator φ) Ω := hwhole.restrict hΩ (Set.subset_univ _)
  have hextgrad (x : V) : hext.weakGrad x = B.indicator htest.weakGrad x := by
    change (WithLp.toLp 2 (fun i => B.indicator (fun y => htest.weakGrad y i) x)) = _
    by_cases hx : x ∈ B
    · simp [hx]
    · simp [hx]
      rfl
  have hgrad := DeGiorgi.MemW1pWitness.ae_eq hB hw htest
  have hseqgrad' (i : Fin 3) :
      Tendsto (fun n => eLpNorm
        (fun x => (fderiv ℝ (seq n) x) (EuclideanSpace.single i 1) - htest.weakGrad x i)
        2 (volume.restrict B)) atTop (𝓝 0) := by
    have heq : (fun n => eLpNorm
        (fun x => (fderiv ℝ (seq n) x) (EuclideanSpace.single i 1) - htest.weakGrad x i)
        2 (volume.restrict B)) = (fun n => eLpNorm
        (fun x => (fderiv ℝ (seq n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
        2 (volume.restrict B)) := by
      funext n
      apply eLpNorm_congr_ae
      filter_upwards [hgrad] with x hx
      rw [hx]
    rw [heq]
    exact hseqgrad i
  have hfun_eq (n : ℕ) : (fun x => seq n x - B.indicator φ x) =
      B.indicator (fun x => seq n x - φ x) := by
    funext x
    by_cases hx : x ∈ B
    · simp [hx]
    · simp [hx, DeGiorgi.zero_outside_of_tsupport_subset (hseqsub n) hx]
  have hderiv_eq (n : ℕ) (i : Fin 3) :
      (fun x => (fderiv ℝ (seq n) x) (EuclideanSpace.single i 1) - hext.weakGrad x i) =
      B.indicator (fun x => (fderiv ℝ (seq n) x) (EuclideanSpace.single i 1) -
        htest.weakGrad x i) := by
    funext x
    rw [hextgrad]
    by_cases hx : x ∈ B
    · simp [hx]
    · simp [hx, DeGiorgi.fderiv_apply_zero_outside_of_tsupport_subset
        (hseqsmooth n) (hseqsub n) hx i]
  refine ⟨hext, ⟨hext.memW1p, hext, seq, hseqsmooth, hseqcompact,
    fun n => (hseqsub n).trans hsub, ?_, ?_⟩, hextgrad⟩
  · have hglobal : Tendsto (fun n => eLpNorm (fun x => seq n x - B.indicator φ x)
        2 volume) atTop (𝓝 0) := by
      simpa only [hfun_eq, eLpNorm_indicator_eq_eLpNorm_restrict hB.measurableSet.nullMeasurableSet]
        using hseqfun
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglobal
      (fun _ => bot_le) (fun n => eLpNorm_mono_measure _ Measure.restrict_le_self)
  · intro i
    have hglobal : Tendsto (fun n => eLpNorm
        (fun x => (fderiv ℝ (seq n) x) (EuclideanSpace.single i 1) - hext.weakGrad x i)
        2 volume) atTop (𝓝 0) := by
      simpa only [hderiv_eq, eLpNorm_indicator_eq_eLpNorm_restrict hB.measurableSet.nullMeasurableSet]
        using hseqgrad' i
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglobal
      (fun _ => bot_le) (fun n => eLpNorm_mono_measure _ Measure.restrict_le_self)

end SeifertSurfaces.WeakSchauder
