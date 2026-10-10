import Foundations
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open scoped Manifold ContDiff RealInnerProductSpace
open Set Topology Metric
noncomputable section
namespace SeifertSurfaces.Foundations.EquatorProof

/-- Extend an injective linear map between the actual model spaces by a two-dimensional complement. -/
theorem exists_extension (A : Euc 1 →L[ℝ] Euc 3) (hA : Function.Injective A) :
    ∃ e : (Euc 1 × Euc 2) ≃L[ℝ] Euc 3, ∀ x, e (x, 0) = A x := by
  let R := A.range
  let eA : Euc 1 ≃L[ℝ] R := (LinearEquiv.ofInjective A.toLinearMap hA).toContinuousLinearEquiv
  have hd : Module.finrank ℝ Rᗮ = 2 := by
    have h := R.finrank_add_finrank_orthogonal
    have hr : Module.finrank ℝ R = 1 := by
      rw [← eA.finrank_eq]
      exact finrank_euclideanSpace_fin
    rw [hr, finrank_euclideanSpace_fin] at h
    omega
  let eB : Euc 2 ≃L[ℝ] Rᗮ := ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_euclideanSpace_fin, hd])
  let eR : (R × Rᗮ) ≃L[ℝ] Euc 3 :=
    (R.prodEquivOfIsCompl Rᗮ R.isCompl_orthogonal).toContinuousLinearEquiv
  refine ⟨(eA.prodCongr eB).trans eR, ?_⟩
  intro x
  simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply, map_zero]
  change (A x : Euc 3) + 0 = A x
  exact add_zero _

variable (L : ℂ →ₗᵢ[ℝ] Euc 4)

def sphereMap (z : Circle) : ThreeSphere :=
  ⟨L z, by simp only [mem_sphere_zero_iff_norm, L.norm_map, Circle.norm_coe]⟩

@[simp] theorem sphereMap_coe (z : Circle) : (sphereMap L z : Euc 4) = L z := rfl

@[simp] theorem sphereMap_neg (z : Circle) : sphereMap L (-z) = -sphereMap L z := by
  apply Subtype.ext
  exact L.map_neg _

def orthogonalMap (v : ℂ) : (ℝ ∙ v)ᗮ →ₗᵢ[ℝ] (ℝ ∙ L v)ᗮ where
  toLinearMap := (L.toLinearMap.comp (ℝ ∙ v)ᗮ.subtype).codRestrict (ℝ ∙ L v)ᗮ (by
    intro w
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, LinearIsometry.coe_toLinearMap,
      L.inner_map_map] using Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property)
  norm_map' w := L.norm_map w

@[simp] theorem orthogonalMap_coe (v : ℂ) (w : (ℝ ∙ v)ᗮ) :
    (orthogonalMap L v w : Euc 4) = L w := rfl

/-- Stereographic inversion commutes with the ambient linear isometry. -/
theorem stereoInv_natural (v : Circle) (w : (ℝ ∙ (v : ℂ))ᗮ) :
    stereoInvFun (norm_eq_of_mem_sphere (sphereMap L v)) (orthogonalMap L v w) =
      sphereMap L (stereoInvFun (norm_eq_of_mem_sphere v) w) := by
  apply Subtype.ext
  change stereoInvFunAux (L v) (L w) = L (stereoInvFunAux (v : ℂ) w)
  simp only [stereoInvFunAux, L.norm_map, L.map_smul, L.map_add]

local instance : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
local instance : Fact (Module.finrank ℝ (Euc 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩

/-- The linear coordinate expression of the sphere map in matching stereographic charts. -/
def chartLinear (v : Circle) : Euc 1 →ₗᵢ[ℝ] Euc 3 :=
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1
    (ne_zero_of_mem_unit_sphere v)).repr
  let V := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
    (ne_zero_of_mem_unit_sphere (sphereMap L v))).repr
  V.toLinearIsometry.comp ((orthogonalMap L v).comp U.symm.toLinearIsometry)

theorem stereo'_inv_natural (v : Circle) (y : Euc 1) :
    (stereographic' 3 (sphereMap L v)).symm (chartLinear L v y) =
      sphereMap L ((stereographic' 1 v).symm y) := by
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1
    (ne_zero_of_mem_unit_sphere v)).repr
  let V := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
    (ne_zero_of_mem_unit_sphere (sphereMap L v))).repr
  change stereoInvFun (norm_eq_of_mem_sphere (sphereMap L v))
    (V.symm (V (orthogonalMap L v (U.symm y)))) =
      sphereMap L (stereoInvFun (norm_eq_of_mem_sphere v) (U.symm y))
  erw [V.symm_apply_apply]
  exact stereoInv_natural L v (U.symm y)

theorem stereo'_natural (v : Circle) (y : Euc 1) :
    stereographic' 3 (sphereMap L v) (sphereMap L ((stereographic' 1 v).symm y)) =
      chartLinear L v y := by
  rw [← stereo'_inv_natural]
  exact (stereographic' 3 (sphereMap L v)).right_inv (by simp)

theorem sphereMap_continuous : Continuous (sphereMap L) :=
  (L.continuous.comp continuous_subtype_val).subtype_mk _

theorem sphereMap_isImmersion : Manifold.IsImmersion (𝓡 1) (𝓡 3) ∞ (sphereMap L) := by
  apply Manifold.IsImmersionOfComplement.isImmersion (F := Euc 2)
  intro x
  obtain ⟨e, he⟩ := exists_extension (chartLinear L (-x)).toContinuousLinearMap
    (chartLinear L (-x)).injective
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt
    (sphereMap_continuous L).continuousAt e
  intro y hy
  change stereographic' 3 (-(sphereMap L x))
    (sphereMap L ((stereographic' 1 (-x)).symm y)) = e (y, 0)
  rw [← sphereMap_neg, stereo'_natural, he]
  rfl

theorem sphereMap_isometry : Isometry (sphereMap L) := by
  intro x y
  change edist (L (x : ℂ)) (L (y : ℂ)) = edist (x : ℂ) (y : ℂ)
  exact L.isometry.edist_eq _ _

theorem sphereMap_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 3) ∞ (sphereMap L) :=
  ⟨sphereMap_isImmersion L, (sphereMap_isometry L).isEmbedding⟩

def equatorLinear : ℂ →ₗᵢ[ℝ] Euc 4 where
  toFun z := EuclideanSpace.single 0 z.re + EuclideanSpace.single 1 z.im
  map_add' z w := by
    ext i
    simp [PiLp.single_apply]
    split_ifs <;> simp_all
  map_smul' c z := by
    ext i
    simp [PiLp.single_apply]
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, Complex.normSq_apply,
      ← Complex.normSq_eq_norm_sq, PiLp.single_apply, Real.norm_eq_abs,
      sq_abs]
    ring

end SeifertSurfaces.Foundations.EquatorProof
