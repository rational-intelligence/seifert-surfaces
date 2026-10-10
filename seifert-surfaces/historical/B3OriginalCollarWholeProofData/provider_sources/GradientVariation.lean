import HarmonicHessianBound
import ConstantEnergyDecay

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

theorem harmonic_gradient_difference_sq (Ω U : Set V) (hΩ : IsOpen Ω)
    (hU : Convex ℝ U) (hsub : U ⊆ Ω) (f : V → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (Q : ℝ) (hQ : 0 ≤ Q)
    (hbound : ∀ x ∈ U, ∀ i : Fin 3,
      ‖fderiv ℝ (fun y => classicalGradient f y i) x‖ ^ 2 ≤ Q)
    (x y : V) (hx : x ∈ U) (hy : y ∈ U) :
    ‖classicalGradient f y - classicalGradient f x‖ ^ 2 ≤ 3 * Q * ‖y - x‖ ^ 2 := by
  have hc (i : Fin 3) :
      ‖classicalGradient f y i - classicalGradient f x i‖ ^ 2 ≤ Q * ‖y - x‖ ^ 2 := by
    have hgi : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => classicalGradient f z i) Ω :=
      (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
    have hd : ∀ z ∈ U, DifferentiableAt ℝ (fun w => classicalGradient f w i) z := by
      intro z hz
      exact (hgi.contDiffAt (hΩ.mem_nhds (hsub hz))).differentiableAt (by simp)
    have hb : ∀ z ∈ U, ‖fderiv ℝ (fun w => classicalGradient f w i) z‖ ≤ Real.sqrt Q := by
      intro z hz
      exact (Real.le_sqrt (norm_nonneg _) hQ).mpr (hbound z hz i)
    have hm := (hU.norm_image_sub_le_of_norm_fderiv_le hd hb hx hy)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hm 2
    simpa only [mul_pow, Real.sq_sqrt hQ] using hs
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ i : Fin 3, Q * ‖y - x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs] using hc i
    _ = _ := by simp; ring

theorem pulledBack_field_energy_le (P : V ≃L[ℝ] V) (Ω : Set V)
    (G : V → V) (hG : MemLp G 2 (volume.restrict Ω)) (L : ℝ)
    (hP : ‖P.toContinuousLinearMap‖ ≤ L) :
    (∫ y in P ⁻¹' Ω, ‖P.toContinuousLinearMap.adjoint (G (P y))‖ ^ 2) ≤
      L ^ 2 * |(LinearMap.det P.toLinearMap)⁻¹| * ∫ x in Ω, ‖G x‖ ^ 2 := by
  have hm := hG.continuousLinearMap_comp P.toContinuousLinearMap.adjoint
  rw [linear_pullback_integral P Ω (fun x => ‖P.toContinuousLinearMap.adjoint (G x)‖ ^ 2)]
  have hi := integral_mono hm.norm.integrable_sq (hG.norm.integrable_sq.const_mul (L ^ 2))
    (fun x => by
      have hn := P.toContinuousLinearMap.adjoint.le_opNorm (G x)
      have he : ‖P.toContinuousLinearMap.adjoint‖ = ‖P.toContinuousLinearMap‖ := by simp
      rw [he] at hn
      have hn' := hn.trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn' 2)
  rw [integral_const_mul] at hi
  calc
    _ ≤ |(LinearMap.det P.toLinearMap)⁻¹| * (L ^ 2 * ∫ x in Ω, ‖G x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hi (abs_nonneg _)
    _ = _ := by ring

end SeifertSurfaces.WeakSchauder
