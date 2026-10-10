import A7PlaneAlgebraV464
import A7HalfSpaceSignV464
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates

/-- Complete a transverse boundary differential by a direction tangent to the
ambient boundary. This controls the first coordinate of the whole IFT map. -/
theorem boundary_completion (L : E2 →L[ℝ] E3) (hL : Injective L)
    {c : ℝ} (hc : 0 < c) (hfirst : ∀ z : E2, L z 0 = c * z 0) :
    ∃ n : E3, n 0 = 0 ∧ ∃ A : (E2 × ℝ) ≃L[ℝ] E3,
      (∀ q, A q = L q.1 + q.2 • n) ∧ (∀ q, A q 0 = c * q.1 0) := by
  obtain ⟨n,hn,horth,B,hB⟩ := normal_completion L hL (innerSL ℝ)
    (fun v hv => real_inner_self_pos.mpr hv)
  let r : E2 := (n 0 / c) • EuclideanSpace.single 0 (1 : ℝ)
  let m : E3 := n - L r
  have hr : c * r 0 = n 0 := by
    simp only [r,PiLp.smul_apply,EuclideanSpace.single,PiLp.single_apply,
      ite_eq_left_iff,smul_eq_mul]
    field_simp
    simp
  have hm : m 0 = 0 := by
    simp only [m,PiLp.sub_apply,hfirst,hr,sub_self]
  let A0 : E2 × ℝ →L[ℝ] E3 :=
    L.comp (ContinuousLinearMap.fst ℝ E2 ℝ) +
      (ContinuousLinearMap.snd ℝ E2 ℝ).smulRight m
  have hA0 : Injective A0 := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨z,t⟩ hzt
    have hb : B (z - t • r,t) = B (0,0) := by
      rw [hB,hB]
      simp only [Prod.fst,Prod.snd,map_zero,zero_smul,add_zero]
      have hzero : L z + t • (n - L r) = 0 := hzt
      simpa only [map_sub,map_smul,smul_sub,sub_add_eq_add_sub,add_sub_assoc] using hzero
    have he := B.injective hb
    have ht : t = 0 := congrArg Prod.snd he
    have hz : z = 0 := by simpa only [ht,zero_smul,sub_zero] using congrArg Prod.fst he
    exact Prod.ext hz ht
  let A : (E2 × ℝ) ≃L[ℝ] E3 :=
    (A0.toLinearMap.linearEquivOfInjective hA0 (by simp [E2,E3])).toContinuousLinearEquiv
  refine ⟨m,hm,A,fun _ => rfl,?_⟩
  intro q
  change (L q.1 + q.2 • m) 0 = c * q.1 0
  simp only [PiLp.add_apply,PiLp.smul_apply,hfirst,hm,smul_zero,add_zero]

end SeifertSurfaces.OriginalEndpoints.A7Support
