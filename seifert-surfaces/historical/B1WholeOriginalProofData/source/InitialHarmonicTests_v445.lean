import InitialFourierConstancy_v445

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

private theorem centered_complex_circle_power_tests_v445 (x : E2) (n : ℕ) :
    let w : E2 → ℂ := fun z => ((z 0 - x 0 : ℝ) : ℂ) +
      ((z 1 - x 1 : ℝ) : ℂ) * Complex.I
    let phi : Fin 2 → E2 → ℝ := fun i z => ![(w z ^ n).re, (w z ^ n).im] i
    (∀ i, ContDiff ℝ ∞ (phi i)) ∧
      ∀ q t : ℝ,
        phi 0 (x + q • unitCircleParameter t) = q ^ n * Real.cos ((n : ℝ) * t) ∧
        phi 1 (x + q • unitCircleParameter t) = q ^ n * Real.sin ((n : ℝ) * t) := by
  dsimp only
  let w : E2 → ℂ := fun z => ((z 0 - x 0 : ℝ) : ℂ) +
    ((z 1 - x 1 : ℝ) : ℂ) * Complex.I
  have hw : ContDiff ℝ ∞ w := by
    have h0 : ContDiff ℝ ∞ (fun z : E2 => z 0 - x 0) := by fun_prop
    have h1 : ContDiff ℝ ∞ (fun z : E2 => z 1 - x 1) := by fun_prop
    exact (Complex.ofRealCLM.contDiff.comp h0).add
      ((Complex.ofRealCLM.contDiff.comp h1).mul contDiff_const)
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · exact Complex.reCLM.contDiff.comp (hw.pow n)
    · exact Complex.imCLM.contDiff.comp (hw.pow n)
  · intro q t
    have he : w (x + q • unitCircleParameter t) =
        (q : ℂ) * (Complex.cos (t : ℂ) + Complex.sin (t : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp [w, unitCircleParameter, Complex.mul_re, Complex.mul_im]
    have hn : w (x + q • unitCircleParameter t) ^ n =
        (q : ℂ) ^ n *
          (Complex.cos ((n : ℂ) * (t : ℂ)) +
            Complex.sin ((n : ℂ) * (t : ℂ)) * Complex.I) := by
      rw [he, mul_pow, Complex.cos_add_sin_mul_I_pow]
    constructor
    · simpa [w, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin] using congrArg Complex.re hn
    · simpa [w, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin] using congrArg Complex.im hn

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
