import NativeACCircleGreen
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def polarAngle (z : E2) : ℝ := Complex.arg ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I)
def rotateQuarter (z : E2) : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-z 1, z 0]
def scalarCone (x : E2) (q k : ℝ) (g : ℝ → ℝ) (z : E2) : ℝ :=
  k + (‖z - x‖ / q) * g (polarAngle (z - x))
def scalarConeGrad (x : E2) (q : ℝ) (g : ℝ → ℝ) (z : E2) : E2 :=
  q⁻¹ • ((g (polarAngle (z - x)) / ‖z - x‖) • (z - x) +
    (deriv g (polarAngle (z - x)) / ‖z - x‖) • rotateQuarter (z - x))

 theorem measurable_polarAngle : Measurable polarAngle := by
  change Measurable (fun z : E2 => Complex.arg ((z 0 : ℂ) + (z 1 : ℂ) * Complex.I))
  exact Complex.measurable_arg.comp (by fun_prop)

 theorem continuous_rotateQuarter : Continuous rotateQuarter := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop

 theorem measurable_scalarCone (x : E2) (q k : ℝ) (g : ℝ → ℝ) (hg : Continuous g) :
    Measurable (scalarCone x q k g) := by
  unfold scalarCone
  exact measurable_const.add (((continuous_id.sub continuous_const).norm.measurable.div_const q).mul
    (hg.measurable.comp (measurable_polarAngle.comp (measurable_id.sub measurable_const))))

 theorem measurable_scalarConeGrad (x : E2) (q : ℝ) (g : ℝ → ℝ) (hg : Continuous g) :
    Measurable (scalarConeGrad x q g) := by
  unfold scalarConeGrad
  have ha := measurable_polarAngle.comp ((continuous_id.sub (continuous_const : Continuous (fun _ : E2 => x))).measurable)
  have hn := (continuous_id.sub (continuous_const : Continuous (fun _ : E2 => x))).norm.measurable
  exact (measurable_const : Measurable (fun _ : E2 => q⁻¹)).smul (((hg.measurable.comp ha).div hn).smul (measurable_id.sub measurable_const) |>.add
    (((measurable_deriv g).comp ha).div hn |>.smul
      (continuous_rotateQuarter.measurable.comp (measurable_id.sub measurable_const))))

 theorem periodic_angle (g : ℝ → ℝ) (hg : Periodic g (2 * Real.pi))
    (r t : ℝ) (hr : 0 < r) : g (polarAngle (r • unitCircleParameter t)) = g t := by
  have hz : (((r • unitCircleParameter t) 0 : ℂ) +
      ((r • unitCircleParameter t) 1 : ℂ) * Complex.I) = (r : ℂ) * (Circle.exp t : ℂ) := by
    change ((r * Real.cos t : ℝ) : ℂ) + ((r * Real.sin t : ℝ) : ℂ) * Complex.I =
      (r : ℂ) * (Circle.exp t : ℂ)
    simp only [Complex.ofReal_mul, Circle.coe_exp, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  unfold polarAngle
  rw [hz, Complex.arg_real_mul _ hr]
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp (Circle.exp_arg (Circle.exp t))
  rw [hn]
  exact hg.int_mul n t

 theorem scalarCone_polar (x : E2) (q k : ℝ) (g : ℝ → ℝ)
    (hg : Periodic g (2 * Real.pi)) (r t : ℝ) (hr : 0 < r) :
    scalarCone x q k g (x + r • unitCircleParameter t) = k + r / q * g t ∧
    scalarConeGrad x q g (x + r • unitCircleParameter t) =
      q⁻¹ • (g t • unitCircleParameter t + deriv g t • rotateQuarter (unitCircleParameter t)) := by
  have hn : ‖r • unitCircleParameter t‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, circle_norm, mul_one]
  have hgp : Periodic (deriv g) (2 * Real.pi) := by
    have hh : (fun t => g (t + 2 * Real.pi)) = g := funext hg
    intro t
    rw [← deriv_comp_add_const, hh]
  simp only [scalarCone, scalarConeGrad, add_sub_cancel_left, hn,
    periodic_angle g hg r t hr, periodic_angle (deriv g) hgp r t hr]
  constructor
  · trivial
  congr 1
  ext i
  fin_cases i <;> simp [rotateQuarter, EuclideanSpace.equiv] <;> field_simp [hr.ne']

 theorem frame_norm_sq (a b t : ℝ) :
    ‖a • unitCircleParameter t + b • rotateQuarter (unitCircleParameter t)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  change (a * Real.cos t + b * -Real.sin t) ^ 2 + (a * Real.sin t + b * Real.cos t) ^ 2 = _
  nlinarith [Real.cos_sq_add_sin_sq t, sq_nonneg (a * Real.cos t), sq_nonneg (b * Real.sin t),
    sq_nonneg (a * Real.sin t), sq_nonneg (b * Real.cos t)]

 theorem scalarConeGrad_norm_polar (x : E2) (q k : ℝ) (g : ℝ → ℝ)
    (hg : Periodic g (2 * Real.pi)) (r t : ℝ) (hr : 0 < r) :
    ‖scalarConeGrad x q g (x + r • unitCircleParameter t)‖ ^ 2 =
      q⁻¹ ^ 2 * (g t ^ 2 + deriv g t ^ 2) := by
  rw [(scalarCone_polar x q k g hg r t hr).2, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, frame_norm_sq]

 theorem scalarCone_memLp (x : E2) (q k : ℝ) (hq : 0 < q) (g : ℝ → ℝ)
    (hg : Periodic g (2 * Real.pi)) (hgc : Continuous g) :
    MemLp (scalarCone x q k g) 2 (volume.restrict (Metric.ball x q)) := by
  apply (memLp_two_iff_integrable_sq (measurable_scalarCone x q k g hgc).aestronglyMeasurable).mpr
  have hcont : Continuous (fun rt : ℝ × ℝ => rt.1 * (k + rt.1 / q * g rt.2) ^ 2) := by fun_prop
  exact (polar_integral_ball x q hq (fun z => scalarCone x q k g z ^ 2)
    (fun t r => r * (k + r / q * g t) ^ 2)
    (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (fun r hr t _ => by rw [(scalarCone_polar x q k g hg r t hr.1).1]; rfl)).1

 theorem scalarConeGrad_energy (x : E2) (q : ℝ) (hq : 0 < q) (g : ℝ → ℝ)
    (hg : Periodic g (2 * Real.pi)) (hgc : Continuous g)
    (hgp : MemLp (deriv g) 2 (volume.restrict (Icc (-Real.pi) Real.pi))) :
    MemLp (scalarConeGrad x q g) 2 (volume.restrict (Metric.ball x q)) ∧
    (∫ z in Metric.ball x q, ‖scalarConeGrad x q g z‖ ^ 2) =
      (1 / 2 : ℝ) * ∫ t in Icc (-Real.pi) Real.pi, g t ^ 2 + deriv g t ^ 2 := by
  have hi : IntegrableOn (fun t => g t ^ 2 + deriv g t ^ 2) (Icc (-Real.pi) Real.pi) :=
    (hgc.pow 2).integrableOn_Icc.add hgp.integrable_sq
  have hri : IntegrableOn (fun r : ℝ => r * q⁻¹ ^ 2) (Icc (0 : ℝ) q) :=
    (continuous_id.mul continuous_const).integrableOn_Icc
  have hrect := hri.mul_prod hi
  change Integrable (fun rt : ℝ × ℝ => (rt.1 * q⁻¹ ^ 2) * (g rt.2 ^ 2 + deriv g rt.2 ^ 2))
    ((volume.restrict (Icc (0 : ℝ) q)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) at hrect
  rw [Measure.prod_restrict] at hrect
  have hh := polar_integral_ball x q hq (fun z => ‖scalarConeGrad x q g z‖ ^ 2)
    (fun t r => r * q⁻¹ ^ 2 * (g t ^ 2 + deriv g t ^ 2)) hrect
    (fun r hr t _ => by rw [scalarConeGrad_norm_polar x q 0 g hg r t hr.1]; simp [smul_eq_mul, mul_assoc])
  refine ⟨(memLp_two_iff_integrable_sq_norm
    (measurable_scalarConeGrad x q g hgc).aestronglyMeasurable).mpr hh.1, ?_⟩
  rw [hh.2]
  have hint (t : ℝ) : (∫ r in Icc (0 : ℝ) q, r * q⁻¹ ^ 2 * (g t ^ 2 + deriv g t ^ 2)) =
      (1 / 2 : ℝ) * (g t ^ 2 + deriv g t ^ 2) := by
    rw [integral_mul_const, integral_mul_const, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hq.le]
    rw [integral_id]
    field_simp
    ring
  simp_rw [hint]
  exact integral_const_mul _ _

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
