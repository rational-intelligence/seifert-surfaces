import Section5GeometricDefinitions
import Mathlib.LinearAlgebra.Alternating.Curry

set_option autoImplicit false
noncomputable section
open Set Function
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations

/-- A nonzero radial vector and an injective tangent-plus-collar derivative
give a nonvanishing ambient determinant on the surface tangent plane. -/
theorem contracted_sphere_determinant_ne_zero
    (z n : Euc 4) (L : Euc 2 →ₗ[ℝ] Euc 4)
    (hz : z ≠ 0) (hzn : inner ℝ z n = 0)
    (hzL : ∀ v, inner ℝ z (L v) = 0)
    (hinj : Injective (fun v : Euc 2 × ℝ => L v.1 + v.2 • n)) :
    ((((EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det.curryLeft z).curryLeft n).compLinearMap L) ≠ 0 := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hL : Injective L := by
    intro v w h
    have e := @hinj (v, 0) (w, 0) (show L v + (0 : ℝ) • n = L w + (0 : ℝ) • n by simpa using h)
    exact congrArg Prod.fst e
  have hLI : LinearIndependent ℝ (fun i => L (b i)) :=
    b.linearIndependent.map' L (LinearMap.ker_eq_bot.mpr hL)
  have hnspan : n ∉ Submodule.span ℝ (range (fun i => L (b i))) := by
    intro h
    have hs : Submodule.span ℝ (range (fun i => L (b i))) ≤ L.range :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨b i, rfl⟩)
    obtain ⟨v, hv⟩ := hs h
    have he := @hinj (0, 1) (v, 0) (show L (0 : Euc 2) + (1 : ℝ) • n = L v + (0 : ℝ) • n by simp [hv])
    have : (1 : ℝ) = 0 := congrArg Prod.snd he
    norm_num at this
  let v : Fin 3 → Euc 4 := Fin.cons n (fun i => L (b i))
  have hv : LinearIndependent ℝ v := linearIndependent_finCons.mpr ⟨hLI, hnspan⟩
  have horth : Submodule.span ℝ (range v) ≤ (innerSL ℝ z).toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change inner ℝ z (v i) = 0
    exact Fin.cases hzn (fun i => hzL (b i)) i
  have hzspan : z ∉ Submodule.span ℝ (range v) := by
    intro h
    have hzz : inner ℝ z z = 0 := horth h
    exact hz ((inner_self_eq_zero).mp hzz)
  have hall : LinearIndependent ℝ (Fin.cons z v) :=
    linearIndependent_finCons.mpr ⟨hv, hzspan⟩
  have hdet := (Module.Basis.is_basis_iff_det
    (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis).mp
    ⟨hall, hall.span_eq_top_of_card_eq_finrank (by simp [Euc])⟩
  intro hzero
  have heval := congrArg (fun A : (Euc 2) [⋀^Fin 2]→ₗ[ℝ] ℝ => A b) hzero
  apply hdet.ne_zero
  simpa only [AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply,
    AlternatingMap.zero_apply, Matrix.vecCons, v] using heval

#print axioms contracted_sphere_determinant_ne_zero
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
