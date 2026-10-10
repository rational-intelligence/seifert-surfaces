import CapTangentGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def capArtificialAngle (s q t : ℝ) : ℝ := s + Real.arcsin (q * Real.sin (t-s))
def capArtificialAnglePrime (s q t : ℝ) : ℝ :=
  q * Real.cos (t-s) / Real.sqrt (1-(q*Real.sin (t-s))^2)

theorem cap_artificial_tangent_abs (s q t : ℝ) (hq : 0 ≤ q) :
    |q * Real.sin (t-s)| ≤ q := by
  rw [abs_mul, abs_of_nonneg hq]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hq).trans_eq (mul_one _)

theorem cap_artificial_angle_deriv (s q t : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2) :
    HasDerivAt (capArtificialAngle s q) (capArtificialAnglePrime s q t) t := by
  have hb := cap_artificial_tangent_abs s q t hq.le
  have hp : -1 < q*Real.sin (t-s) ∧ q*Real.sin (t-s) < 1 := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp hb
    constructor <;> linarith
  have hd := ((Real.hasDerivAt_arcsin (ne_of_gt hp.1) (ne_of_lt hp.2)).comp t
    (((Real.hasDerivAt_sin (t-s)).comp t ((hasDerivAt_id t).sub_const s)).const_mul q)).const_add s
  convert hd using 1
  · rfl
  · dsimp [capArtificialAnglePrime]
    ring

theorem cap_artificial_angle_smooth (s q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2) :
    ContDiff ℝ ∞ (capArtificialAngle s q) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have hb := cap_artificial_tangent_abs s q t hq.le
  have hp : q*Real.sin (t-s) ≠ -1 ∧ q*Real.sin (t-s) ≠ 1 := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp hb
    constructor
    · exact ne_of_gt (by linarith)
    · exact ne_of_lt (by linarith)
  change ContDiffAt ℝ ∞ (fun x => s+Real.arcsin (q*Real.sin (x-s))) t
  have ha : ContDiffAt ℝ ∞ Real.arcsin (q*Real.sin (t-s)) := Real.contDiffAt_arcsin hp.1 hp.2
  have hqf : ContDiffAt ℝ ∞ (fun x : ℝ => q*Real.sin (x-s)) t := by fun_prop
  have hh : ContDiffAt ℝ ∞ (fun x : ℝ => Real.arcsin (q*Real.sin (x-s))) t := ContDiffAt.comp (g:=Real.arcsin) (f:=fun x : ℝ => q*Real.sin (x-s)) t ha hqf
  exact contDiffAt_const.add hh

theorem cap_artificial_angle_prime_abs (s q t : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2) :
    |capArtificialAnglePrime s q t| ≤ 2*q := by
  have hb := cap_artificial_tangent_abs s q t hq.le
  have hs : 1/2 ≤ Real.sqrt (1-(q*Real.sin (t-s))^2) := by
    apply Real.le_sqrt_of_sq_le
    obtain ⟨hlo,hhi⟩ := abs_le.mp hb
    nlinarith [sq_nonneg (q*Real.sin (t-s)),sq_abs (q*Real.sin (t-s))]
  have hs0 : 0 < Real.sqrt (1-(q*Real.sin (t-s))^2) := by linarith
  unfold capArtificialAnglePrime
  rw [abs_div,abs_of_pos hs0,abs_mul,abs_of_pos hq]
  apply (div_le_iff₀ hs0).mpr
  have hc := Real.abs_cos_le_one (t-s)
  nlinarith

theorem cap_artificial_angle_prime_nonpos (s q t : ℝ) (hq : 0 < q)
    (ht : t ∈ Icc (s+Real.pi/2+Real.arcsin (q/2))
      (s+3*Real.pi/2-Real.arcsin (q/2))) : capArtificialAnglePrime s q t ≤ 0 := by
  have he : 0 ≤ Real.arcsin (q/2) := Real.arcsin_nonneg.mpr (by linarith)
  have hc : Real.cos (t-s) ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le
    (by linarith [ht.1]) (by linarith [ht.2])
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hq.le hc) (Real.sqrt_nonneg _)

theorem cap_artificial_trace_energy (s q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2)
    (b : ℝ → E2) (hb : ContDiff ℝ ∞ b) :
    (∫ t in Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2)),
      ‖deriv (fun t => b (capArtificialAngle s q t)) t‖^2) ≤
    2*q*(∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)),‖deriv b t‖^2) := by
  let a := s+Real.pi/2+Real.arcsin (q/2)
  let d := s+3*Real.pi/2-Real.arcsin (q/2)
  have he := cap_arcsin_bounds q hq hq1
  have had : a ≤ d := by dsimp [a,d]; linarith [Real.pi_pos,he.2.1]
  have hθ := cap_artificial_angle_smooth s q hq hq1
  have hder (t : ℝ) : deriv (fun t => b (capArtificialAngle s q t)) t =
      capArtificialAnglePrime s q t • deriv b (capArtificialAngle s q t) := by
    exact ((hb.differentiable (by simp) (capArtificialAngle s q t)).hasDerivAt.scomp t
      (cap_artificial_angle_deriv s q t hq hq1)).deriv
  have hc : Continuous (fun t => ‖deriv b t‖^2) := (hb.continuous_deriv (by simp)).norm.pow 2
  have hp : Continuous (capArtificialAnglePrime s q) := by
    convert hθ.continuous_deriv (by simp) using 1
    ext t
    exact (cap_artificial_angle_deriv s q t hq hq1).deriv.symm
  have hleft : IntegrableOn (fun t => ‖deriv (fun t => b (capArtificialAngle s q t)) t‖^2) (Icc a d) :=
    (((hb.comp hθ).continuous_deriv (by simp)).norm.pow 2).integrableOn_Icc
  have hright : IntegrableOn (fun t => -2*q*((‖deriv b (capArtificialAngle s q t)‖^2)*capArtificialAnglePrime s q t)) (Icc a d) := by
    apply Continuous.integrableOn_Icc
    exact continuous_const.mul ((hc.comp hθ.continuous).mul hp)
  have hi := setIntegral_mono_on hleft hright measurableSet_Icc (fun t ht => by
    rw [hder t,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    have hn := cap_artificial_angle_prime_nonpos s q t hq ht
    have hm := cap_artificial_angle_prime_abs s q t hq hq1
    rw [abs_of_nonpos hn] at hm
    have hs := sq_nonneg (capArtificialAnglePrime s q t)
    have hk : capArtificialAnglePrime s q t^2 ≤ -2*q*capArtificialAnglePrime s q t := by nlinarith
    nlinarith [sq_nonneg (‖deriv b (capArtificialAngle s q t)‖),mul_le_mul_of_nonneg_right hk (sq_nonneg (‖deriv b (capArtificialAngle s q t)‖))])
  have hsub := intervalIntegral.integral_comp_mul_deriv (a:=a) (b:=d)
    (fun t _ => cap_artificial_angle_deriv s q t hq hq1) hp.continuousOn hc
  have hend := cap_base_endpoints s q hq hq1 (fun t => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![t,0])
  have ha : capArtificialAngle s q a = s+2*Real.arcsin (q/2) := by
    simpa [capArtificialAngle,a,EuclideanSpace.equiv] using congrArg (fun z : E2 => z 0) hend.1
  have hd : capArtificialAngle s q d = s-2*Real.arcsin (q/2) := by
    simpa [capArtificialAngle,d,EuclideanSpace.equiv] using congrArg (fun z : E2 => z 0) hend.2
  have hsub1 : (∫ t in Icc a d, ‖deriv b (capArtificialAngle s q t)‖^2*capArtificialAnglePrime s q t) =
      -(∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)),‖deriv b t‖^2) := by
    rw [intervalIntegral.integral_of_le had,← integral_Icc_eq_integral_Ioc,ha,hd,
      intervalIntegral.integral_symm,intervalIntegral.integral_of_le (by linarith [he.1]),
      ← integral_Icc_eq_integral_Ioc] at hsub
    exact hsub
  calc
    _ ≤ ∫ t in Icc a d, -2*q*((‖deriv b (capArtificialAngle s q t)‖^2)*capArtificialAnglePrime s q t) := hi
    _ = 2*q*(∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)),‖deriv b t‖^2) := by
      rw [integral_const_mul,hsub1]
      ring

theorem cap_artificial_trace_native_properties (s q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1/2)
    (B b : ℝ → E2) (hb : ContDiff ℝ ∞ b)
    (hagree : ∀ t ∈ Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), B t=b t) :
    let c := fun t => b (capArtificialAngle s q t)
    let a := s+Real.pi/2+Real.arcsin (q/2)
    let d := s+3*Real.pi/2-Real.arcsin (q/2)
    ContinuousOn c (Icc a d) ∧
    (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) a d) ∧
    MemLp (deriv c) 2 (volume.restrict (Icc a d)) ∧
    c a=B (s+2*Real.arcsin (q/2)) ∧ c d=B (s-2*Real.arcsin (q/2)) ∧
    (∫ t in Icc a d, ‖deriv c t‖^2) ≤
      2*q*(∫ t in Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)),‖deriv b t‖^2) := by
  dsimp only
  have hc := hb.comp (cap_artificial_angle_smooth s q hq hq1)
  have he : 0 < Real.arcsin (q/2) := (cap_arcsin_bounds q hq hq1).1
  have hm : MemLp (deriv (fun t => b (capArtificialAngle s q t))) 2
      (volume.restrict (Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2)))) := by
    apply (memLp_two_iff_integrable_sq_norm (hc.continuous_deriv (by simp)).aestronglyMeasurable).mpr
    exact ((hc.continuous_deriv (by simp)).norm.pow 2).integrableOn_Icc
  refine ⟨hc.continuous.continuousOn, ?_,hm,?_,?_, cap_artificial_trace_energy s q hq hq1 b hb⟩
  · intro i
    exact (((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp hc).of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  · unfold capArtificialAngle
    rw [cap_base_endpoints s q hq hq1 b |>.1]
    exact (hagree _ ⟨by linarith,le_rfl⟩).symm
  · unfold capArtificialAngle
    rw [cap_base_endpoints s q hq hq1 b |>.2]
    exact (hagree _ ⟨le_rfl,by linarith⟩).symm

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
