import SymmetricWeakEquation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

theorem linear_map_restrict_volume (P : V ≃L[ℝ] V) (Ω : Set V) :
    Measure.map P (volume.restrict (P ⁻¹' Ω)) =
      ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume.restrict Ω := by
  have he : MeasurableEmbedding (P : V → V) := P.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hm : Measure.map P volume = ENNReal.ofReal |(LinearMap.det P.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume P.toLinearEquiv.isUnit_det'.ne_zero
  rw [← he.restrict_map, hm, Measure.restrict_smul]

theorem linear_pullback_memLp (P : V ≃L[ℝ] V) (Ω : Set V) (f : V → ℝ)
    (hf : MemLp f 2 (volume.restrict Ω)) :
    MemLp (fun y => f (P y)) 2 (volume.restrict (P ⁻¹' Ω)) := by
  have hm : MemLp f 2 (Measure.map P (volume.restrict (P ⁻¹' Ω))) := by
    rw [linear_map_restrict_volume]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map P.continuous.measurable.aemeasurable

theorem linear_pullback_integral (P : V ≃L[ℝ] V) (Ω : Set V) (f : V → ℝ) :
    (∫ y in P ⁻¹' Ω, f (P y)) =
      |(LinearMap.det P.toLinearMap)⁻¹| * ∫ x in Ω, f x := by
  have he : MeasurableEmbedding (P : V → V) := P.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [← he.integral_map,
    linear_map_restrict_volume, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

theorem clm_coordinate_sum (L : V →L[ℝ] ℝ) (v : V) :
    L v = ∑ i : Fin 3, v i * L (EuclideanSpace.single i 1) := by
  have hv : (∑ i : Fin 3, v i • EuclideanSpace.single i 1) = v := by
    ext j
    simp [Pi.single_apply, mul_ite]
  calc
    L v = L (∑ i : Fin 3, v i • EuclideanSpace.single i 1) := congrArg L hv.symm
    _ = _ := by simp

theorem weak_directional_integral (Ω : Set V) (h : V → ℝ) (hh : H1Witness h Ω)
    (φ : V → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) (v : V) :
    (∫ x in Ω, h x * (fderiv ℝ φ x) v) =
      -∫ x in Ω, inner ℝ (hh.weakGrad x) v * φ x := by
  have hD (i : Fin 3) : MemLp (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1))
      2 (volume.restrict Ω) := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (by simp)
    exact ((hd.clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport
      (hφc.fderiv_apply (𝕜 := ℝ) _)).restrict Ω
  have hp : MemLp φ 2 (volume.restrict Ω) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict Ω
  have hL (i : Fin 3) : Integrable (fun x => v i * (h x *
      (fderiv ℝ φ x) (EuclideanSpace.single i 1))) (volume.restrict Ω) :=
    (hh.memLp.integrable_mul (hD i)).const_mul (v i)
  have hG (i : Fin 3) : Integrable (fun x => v i * (hh.weakGrad x i * φ x))
      (volume.restrict Ω) := (hh.weakGrad_component_memLp i |>.integrable_mul hp).const_mul (v i)
  have hinner (x : V) : inner ℝ (hh.weakGrad x) v = ∑ i : Fin 3, v i * hh.weakGrad x i := by
    simp [PiLp.inner_apply]
  have he : (fun x => h x * (fderiv ℝ φ x) v) =
      fun x => ∑ i : Fin 3, v i * (h x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
    funext x
    rw [clm_coordinate_sum]
    simp [Finset.mul_sum, mul_left_comm]
  rw [he]
  simp_rw [hinner, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => hL i), integral_finsetSum _ (fun i _ => hG i)]
  simp_rw [integral_const_mul, hh.isWeakGrad _ φ hφ hφc hφΩ, mul_neg, Finset.sum_neg_distrib]

theorem adjoint_coordinate (P : V ≃L[ℝ] V) (v : V) (i : Fin 3) :
    P.toContinuousLinearMap.adjoint v i = inner ℝ v (P (EuclideanSpace.single i 1)) := by
  calc
    _ = inner ℝ (P.toContinuousLinearMap.adjoint v) (EuclideanSpace.single i 1) := by
      simp [EuclideanSpace.inner_single_right]
    _ = _ := by rw [ContinuousLinearMap.adjoint_inner_left]; rfl

def linear_pullback_witness (P : V ≃L[ℝ] V) (Ω : Set V)
    (h : V → ℝ) (hh : H1Witness h Ω) :
    H1Witness (fun y => h (P y)) (P ⁻¹' Ω) where
  memLp := linear_pullback_memLp P Ω h hh.memLp
  weakGrad := fun y => P.toContinuousLinearMap.adjoint (hh.weakGrad (P y))
  weakGrad_component_memLp := by
    intro i
    have hi : MemLp (fun x => inner ℝ (hh.weakGrad x) (P (EuclideanSpace.single i 1)))
        2 (volume.restrict Ω) := by
      simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm] using
        (innerSL ℝ (P (EuclideanSpace.single i 1))).comp_memLp' hh.weakGrad_memLp
    simpa only [adjoint_coordinate] using linear_pullback_memLp P Ω _ hi
  isWeakGrad := by
    intro i φ hφ hφc hφΩ
    let ψ : V → ℝ := fun x => φ (P.symm x)
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp P.symm.contDiff
    have hψc : HasCompactSupport ψ := hφc.comp_homeomorph P.symm.toHomeomorph
    have hψΩ : tsupport ψ ⊆ Ω := by
      rw [show ψ = φ ∘ P.symm.toHomeomorph from rfl, tsupport_comp_eq_preimage]
      intro x hx
      have ht := hφΩ hx
      simpa using ht
    have hdψ (x : V) : fderiv ℝ ψ x =
        (fderiv ℝ φ (P.symm x)).comp P.symm.toContinuousLinearMap :=
      ((hφ.differentiable (by simp) (P.symm x)).hasFDerivAt.comp x P.symm.hasFDerivAt).fderiv
    have hid (y : V) : (fderiv ℝ φ y) (EuclideanSpace.single i 1) =
        (fderiv ℝ ψ (P y)) (P (EuclideanSpace.single i 1)) := by
      rw [hdψ]
      simp
    have hp (y : V) : ψ (P y) = φ y := by simp [ψ]
    change (∫ y in P ⁻¹' Ω, h (P y) * (fderiv ℝ φ y) (EuclideanSpace.single i 1)) =
      -∫ y in P ⁻¹' Ω, P.toContinuousLinearMap.adjoint (hh.weakGrad (P y)) i * φ y
    simp_rw [hid, adjoint_coordinate, ← hp]
    rw [linear_pullback_integral P Ω (fun x => h x * (fderiv ℝ ψ x) (P (EuclideanSpace.single i 1))),
      linear_pullback_integral P Ω (fun x => inner ℝ (hh.weakGrad x) (P (EuclideanSpace.single i 1)) * ψ x),
      weak_directional_integral Ω h hh ψ hψ hψc hψΩ (P (EuclideanSpace.single i 1)), mul_neg]

end SeifertSurfaces.WeakSchauder
