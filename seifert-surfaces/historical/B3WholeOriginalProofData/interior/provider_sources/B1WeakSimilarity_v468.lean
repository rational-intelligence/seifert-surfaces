import VM03ExactCaller_v464
import B1CauchyGauge
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
theorem weak_vekua_similarity (R : ℝ) (hR : 0 < R) (w A B : ℂ → ℂ)
    (hw : ContinuousOn w (Metric.ball 0 R)) (heq : WeakVekuaOn (Metric.ball 0 R) w A B)
    (p : ℝ) (hp : 2 < p)
    (hA : MemLp A (ENNReal.ofReal p) (volume.restrict (Metric.ball 0 R)))
    (hB : MemLp B (ENNReal.ofReal p) (volume.restrict (Metric.ball 0 R))) :
    Nonempty (SimilarityFactorization R w) := by
  let a := fun z => A z + B z * (star (w z) / w z)
  have hratio (z : ℂ) : ‖star (w z) / w z‖ ≤ 1 := by
    rw [norm_div, norm_star]
    exact div_self_le_one _
  have hameas : AEStronglyMeasurable a (volume.restrict (Metric.ball 0 R)) := by
    have hwmeas := hw.aestronglyMeasurable (μ := volume) Metric.isOpen_ball.measurableSet
    exact hA.aestronglyMeasurable.add
      (hB.aestronglyMeasurable.mul (hwmeas.star.div₀ hwmeas))
  have habound (z : ℂ) : ‖a z‖ ≤ ‖A z‖ + ‖B z‖ := by
    calc
      ‖a z‖ ≤ ‖A z‖ + ‖B z * (star (w z) / w z)‖ := norm_add_le _ _
      _ = ‖A z‖ + ‖B z‖ * ‖star (w z) / w z‖ := by rw [norm_mul]
      _ ≤ ‖A z‖ + ‖B z‖ := by nlinarith [hratio z, norm_nonneg (B z)]
  have ha : MemLp a (ENNReal.ofReal p) (volume.restrict (Metric.ball 0 R)) :=
    (hA.norm.add hB.norm).mono' hameas (Filter.Eventually.of_forall habound)
  have haeq (z : ℂ) : a z * w z = A z * w z + B z * star (w z) := by
    dsimp [a]
    by_cases hz : w z = 0
    · simp [hz]
    · field_simp
  have heqa : WeakVekuaOn (Metric.ball 0 R) w a (fun _ => 0) := by
    refine ⟨heq.1, ?_⟩
    intro φ hφ hcompact hsupport
    obtain ⟨hint, hrhs, hid⟩ := heq.2 φ hφ hcompact hsupport
    have hfun : (fun z => (a z * w z + (0 : ℂ) * star (w z)) * φ z) =
        (fun z => (A z * w z + B z * star (w z)) * φ z) := by
      funext z
      simp only [haeq, zero_mul, add_zero]
    exact ⟨hint, hfun.symm ▸ hrhs, hfun.symm ▸ hid⟩
  let omega := CauchyGauge.literalCauchyPotential R a
  obtain ⟨hbounded, halpha, hholder, hdbar⟩ :=
    CauchyGauge.literal_Cauchy_potential_bounded_holder_weak_dbar R hR p hp a ha
  obtain ⟨C, hC⟩ := hholder
  have homega : ContinuousOn omega (Metric.ball (0 : ℂ) R) :=
    hC.continuousOn halpha.1
  have hhol := CauchyGauge.weak_gauge_product_holomorphic (Metric.ball (0 : ℂ) R)
    Metric.isOpen_ball p hp a w omega ha hw homega heqa hdbar
  refine ⟨{
    Phi := fun z => w z * Complex.exp (-omega z)
    holomorphic := hhol
    omega := omega
    omega_bounded := hbounded
    alpha := CauchyGauge.cauchyExponent p
    alpha_pos := halpha.1
    alpha_lt_one := halpha.2.1
    omega_holder := ⟨C, hC⟩
    same_w := ?_ }⟩
  intro z _hz
  rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

end SeifertSurfaces.OriginalEndpoints.B1Tangency
