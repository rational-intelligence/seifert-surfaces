import EndpointGeometry
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates

theorem exists_orthogonal_normal (L : E2 →L[ℝ] E3)
    (B : E3 →L[ℝ] E3 →L[ℝ] ℝ) :
    ∃ n : E3, n ≠ 0 ∧ ∀ z : E2, B (L z) n = 0 := by
  let A : E3 →ₗ[ℝ] (E2 →ₗ[ℝ] ℝ) := {
    toFun := fun n => (B.flip n).toLinearMap.comp L.toLinearMap
    map_add' := by intro v w; ext z; simp
    map_smul' := by intro a v; ext z; simp }
  have hnot : ¬ Function.Injective A := by
    intro h
    have hd := LinearMap.finrank_le_finrank_of_injective h
    have h3 : Module.finrank ℝ E3 = 3 := by simp [E3]
    have h2 : Module.finrank ℝ (E2 →ₗ[ℝ] ℝ) = 2 := by simp [E2]
    rw [h3,h2] at hd
    omega
  have hker : LinearMap.ker A ≠ ⊥ := fun h => hnot (LinearMap.ker_eq_bot.mp h)
  obtain ⟨n,hn,hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨n,hne,?_⟩
  intro z
  exact congrArg (fun f : E2 →ₗ[ℝ] ℝ => f z) hn

/-- The actual metric-normal direction completes an injective tangent frame. -/
theorem normal_completion (L : E2 →L[ℝ] E3) (hL : Function.Injective L)
    (B : E3 →L[ℝ] E3 →L[ℝ] ℝ)
    (hpos : ∀ n : E3, n ≠ 0 → 0 < B n n) :
    ∃ n : E3, n ≠ 0 ∧ (∀ z : E2, B (L z) n = 0) ∧
      ∃ A : (E2 × ℝ) ≃L[ℝ] E3, ∀ q, A q = L q.1 + q.2 • n := by
  obtain ⟨n,hn,horth⟩ := exists_orthogonal_normal L B
  let A0 : E2 × ℝ →L[ℝ] E3 :=
    L.comp (ContinuousLinearMap.fst ℝ E2 ℝ) +
      (ContinuousLinearMap.snd ℝ E2 ℝ).smulRight n
  have hA0 : Function.Injective A0 := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨z,t⟩ heq
    have hB : t * B n n = 0 := by
      have h := congrArg (fun v : E3 => B v n) heq
      simpa [A0,horth] using h
    have ht : t = 0 := (mul_eq_zero.mp hB).resolve_right (ne_of_gt (hpos n hn))
    have hz : z = 0 := hL (by simpa [A0,ht] using heq)
    exact Prod.ext hz ht
  let A : (E2 × ℝ) ≃L[ℝ] E3 :=
    (A0.toLinearMap.linearEquivOfInjective hA0 (by simp [E2,E3])).toContinuousLinearEquiv
  exact ⟨n,hn,horth,A,fun _ => rfl⟩

end SeifertSurfaces.OriginalEndpoints.A7Support
