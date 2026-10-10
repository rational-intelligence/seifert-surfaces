import InitialActualArcPath_v411
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent

set_option maxRecDepth 10000
set_option maxHeartbeats 0

 theorem ae_deriv_coordinate (c : ℝ → E2) (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) a b) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      DifferentiableAt ℝ c t ∧ ∀ i : Fin 2, deriv (fun u => c u i) t = deriv c t i := by
  have hall : ∀ᵐ t ∂volume, ∀ i : Fin 2,
      t ∈ Icc a b → DifferentiableAt ℝ (fun u => c u i) t := by
    exact (ae_all_iff.mpr fun i => by simpa [uIcc_of_le hab] using (hc i).ae_differentiableAt)
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Icc] with t ht hmem
  have hdpi : DifferentiableAt ℝ (fun u => fun i : Fin 2 => c u i) t :=
    differentiableAt_pi.mpr (fun i => ht i hmem)
  have hd : DifferentiableAt ℝ c t :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.differentiableAt.comp t hdpi
  refine ⟨hd, fun i => ?_⟩
  exact (((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt).comp_hasDerivAt t hd.hasDerivAt).deriv

 theorem circle_contDiff : ContDiff ℝ ∞ unitCircleParameter := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp <;> fun_prop

 theorem circle_norm (t : ℝ) : ‖unitCircleParameter t‖ = 1 := by
  have hs : ‖unitCircleParameter t‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    exact Real.cos_sq_add_sin_sq t
  nlinarith [norm_nonneg (unitCircleParameter t)]

 theorem periodic_deriv {c : ℝ → E2} {p : ℝ} (hc : Periodic c p) :
    Periodic (deriv c) p := by
  have hh : (fun t => c (t + p)) = c := funext hc
  intro t
  rw [← deriv_comp_add_const, hh]

 theorem polar_pullback (c : ℝ → E2) (hc : Periodic c (2 * Real.pi))
    (r t : ℝ) (hr : 0 < r) :
    let angle : E2 → ℝ := fun z => Complex.arg ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I)
    let cone : E2 → E2 := fun z => ‖z‖ • c (angle z)
    let jets : Fin 2 → E2 → E2 := fun i z =>
      if z = 0 then 0 else
        (c (angle z) i / ‖z‖) • z +
        (deriv c (angle z) i / ‖z‖) •
          (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-z 1, z 0]
    cone (r • unitCircleParameter t) = r • c t ∧
      ∀ i : Fin 2, jets i (r • unitCircleParameter t) =
        (c t i) • unitCircleParameter t +
          (deriv c t i) • (EuclideanSpace.equiv (Fin 2) ℝ).symm
            ![-unitCircleParameter t 1, unitCircleParameter t 0] := by
  have radial_norm : ‖r • unitCircleParameter t‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, circle_norm, mul_one]
  have radial_ne : r • unitCircleParameter t ≠ 0 := by
    intro h
    have hn : ‖r • unitCircleParameter t‖ = 0 := by rw [h, norm_zero]
    rw [radial_norm] at hn
    exact hr.ne' hn
  have complex_radial :
      (((r • unitCircleParameter t) 0 : ℂ) +
        ((r • unitCircleParameter t) 1 : ℂ) * Complex.I) =
        (r : ℂ) * (Circle.exp t : ℂ) := by
    change ((r * Real.cos t : ℝ) : ℂ) + ((r * Real.sin t : ℝ) : ℂ) * Complex.I =
      (r : ℂ) * (Circle.exp t : ℂ)
    simp only [Complex.ofReal_mul, Circle.coe_exp, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have angle_eq : Complex.arg (((r • unitCircleParameter t) 0 : ℂ) +
      ((r • unitCircleParameter t) 1 : ℂ) * Complex.I) = Complex.arg (Circle.exp t : ℂ) := by
    rw [complex_radial, Complex.arg_real_mul _ hr]
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp (Circle.exp_arg (Circle.exp t))
  have value_eq : c (Complex.arg (Circle.exp t : ℂ)) = c t := by
    rw [hn]
    exact hc.int_mul n t
  have derivative_eq : deriv c (Complex.arg (Circle.exp t : ℂ)) = deriv c t := by
    rw [hn]
    exact (periodic_deriv hc).int_mul n t
  dsimp only
  rw [radial_norm, angle_eq, value_eq]
  refine ⟨rfl, fun i => ?_⟩
  rw [if_neg radial_ne, derivative_eq]
  ext k
  fin_cases k <;> simp [EuclideanSpace.equiv] <;> field_simp [hr.ne'] <;> ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
