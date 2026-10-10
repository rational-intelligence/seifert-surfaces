import Section5StrictBoundaryTransportV481
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology BigOperators
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.PrivateHelpers.C6Native

/-- The second derivative of a smooth function vanishing on the boundary
hyperplane is zero along every tangent direction. -/
theorem boundary_plane_second_derivative_zero
    (R : E3 → ℝ) (a v : E3) (ha : a 0 = 0) (hv : v 0 = 0)
    (hs : ContDiffAt ℝ 2 R a)
    (hz : ∀ᶠ z in 𝓝 a, z 0 = 0 → R z = 0) :
    fderiv ℝ (fderiv ℝ R) a v v = 0 := by
  let line : ℝ → E3 := fun t => a + t • v
  have hline (t : ℝ) : HasDerivAt line v t := by
    convert ((hasDerivAt_id t).smul_const v).const_add a using 1 <;>
      simp only [line, id_eq, one_smul]
  have hl0 : line 0 = a := by simp [line]
  have hlt : Tendsto line (𝓝 0) (𝓝 a) := by
    simpa only [hl0] using (hline 0).continuousAt.tendsto
  have hzero : (R ∘ line) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hlt.eventually hz] with t ht
    exact ht (by simp [line, ha, hv])
  have hderiv : (fun t => fderiv ℝ R (line t) v) =ᶠ[𝓝 (0 : ℝ)]
      (fun _ => (0 : ℝ)) := by
    have hnear := hlt.eventually (hs.eventually (by norm_num))
    have hd0 := hzero.deriv
    filter_upwards [hnear, hd0] with t ht hd
    have he := ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
    exact he.symm.trans (by simpa using hd)
  have hdiff := (hs.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd : HasDerivAt (fun t => fderiv ℝ R (line t) v)
      (fderiv ℝ (fderiv ℝ R) a v v) 0 := by
    have hD := hdiff.hasFDerivAt
    rw [← hl0] at hD
    have hc := (hD.comp_hasDerivAt 0 (hline 0)).clm_apply (hasDerivAt_const 0 v)
    convert hc using 1 <;> simp only [Function.comp_apply, hl0, map_zero, add_zero]
  exact hd.deriv.symm.trans (hderiv.deriv_eq.trans (deriv_const 0 0))

/-- A nonsingular nonnegative defining function has a strictly positive inward
normal derivative, and its derivative annihilates the boundary tangent plane. -/
theorem boundary_defining_covector_positive
    (R : E3 → ℝ) (a : E3) (ha : a 0 = 0) (hRa : R a = 0)
    (hs : DifferentiableAt ℝ R a) (hne : fderiv ℝ R a ≠ 0)
    (hpos : ∀ᶠ z in 𝓝 a, 0 ≤ z 0 → 0 ≤ R z) :
    ∃ k : ℝ, 0 < k ∧ ∀ v : E3, fderiv ℝ R a v = k * v 0 := by
  have haR : a ∈ range (𝓡∂ 3) := by
    simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq, ha] using (le_refl (0 : ℝ))
  have hmin : IsLocalMinOn R (range (𝓡∂ 3)) a := by
    filter_upwards [hpos.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzr
    rw [hRa]
    apply hz
    simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hzr
  have hnn (w : E3) (hw : 0 ≤ w 0) : 0 ≤ fderiv ℝ R a w := by
    apply hmin.hasFDerivWithinAt_nonneg hs.hasFDerivAt.hasFDerivWithinAt
    apply mem_posTangentConeAt_of_segment_subset
    apply (𝓡∂ 3).convex_range.segment_subset haR
    simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq,
      PiLp.add_apply, ha, zero_add] using hw
  have ht (w : E3) (hw : w 0 = 0) : fderiv ℝ R a w = 0 := by
    have h1 := hnn w (by rw [hw])
    have h2 := hnn (-w) (by simp only [PiLp.neg_apply, hw, neg_zero, le_refl])
    rw [map_neg] at h2
    exact le_antisymm (neg_nonneg.mp h2) h1
  let k := fderiv ℝ R a (coordinateVector 3 0)
  have hk0 : 0 ≤ k := hnn _ (by simp [coordinateVector, EuclideanSpace.single, PiLp.single_apply])
  have heq (v : E3) : fderiv ℝ R a v = k * v 0 := by
    let w := v - v 0 • coordinateVector 3 0
    have hw : w 0 = 0 := by simp [w, coordinateVector, EuclideanSpace.single, PiLp.single_apply]
    have htw := ht w hw
    change fderiv ℝ R a (v - v 0 • coordinateVector 3 0) = 0 at htw
    rw [map_sub, map_smul] at htw
    change fderiv ℝ R a v - v 0 * k = 0 at htw
    nlinarith
  have hkne : k ≠ 0 := by
    intro hk
    apply hne
    ext v
    simp only [heq v, hk, zero_mul, zero_apply]
  exact ⟨k, lt_of_le_of_ne hk0 hkne.symm, heq⟩

/-- Boundary defining functions differ by a positive scalar at the level of
the metric Hessian restricted to the boundary tangent plane. -/
theorem boundary_defining_hessian_scale
    (G : MetricTensor) (hG : ∀ z i j, G z i j = G z j i)
    (R : E3 → ℝ) (a v : E3) (ha : a 0 = 0) (hv : v 0 = 0)
    (hs : ContDiffAt ℝ 2 R a)
    (hz : ∀ᶠ z in 𝓝 a, z 0 = 0 → R z = 0)
    (k : ℝ) (hd : ∀ w : E3, fderiv ℝ R a w = k * w 0) :
    hessianQuadratic G R a v = k * hessianQuadratic G (fun z : E3 => z 0) a v := by
  have hs0 : ContDiffAt ℝ 2 (fun z : E3 => z 0) a :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0).contDiff.contDiffAt
  rw [hessian_quadratic_frechet G R a v hG hs,
    boundary_plane_second_derivative_zero R a v ha hv hs hz,
    hessian_quadratic_frechet G (fun z : E3 => z 0) a v hG hs0]
  have hdf : fderiv ℝ (fun z : E3 => z 0) = fun _ =>
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0) := by
    funext z
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0).fderiv
  rw [hdf]
  have hzder : fderiv ℝ (fun _ : E3 => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0)) a = 0 :=
    (hasFDerivAt_const (𝕜 := ℝ) (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0) a).fderiv
  rw [hzder]
  simp only [zero_apply, zero_sub]
  simp_rw [hd]
  simp only [PiLp.proj_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  ring

#print axioms boundary_defining_covector_positive
#print axioms boundary_defining_hessian_scale
#print axioms boundary_plane_second_derivative_zero
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
