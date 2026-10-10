import B1InteriorLocalZeroContinuation_v475
noncomputable section
open Set Topology Function Filter
open scoped ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A C1 scalar function and its first derivative vanish at an accumulation
point of actual open zero germs.  Applied to the normal coordinate of the
opposite sheet, this supplies the limiting tangent-plane equality. -/
theorem native_zero_germ_value_derivative_closure_v475
    (O : Set E2) (hO : IsOpen O) (u : E2 → ℝ)
    (hu : ContDiffOn ℝ 1 u O) (p : E2) (hp : p ∈ O)
    (hacc : p ∈ closure {q | q ∈ O ∧ native_planar_zero_germ_v475 O u q}) :
    u p=0 ∧ fderiv ℝ u p=0 := by
  let Z := {q | q ∈ O ∧ native_planar_zero_germ_v475 O u q}
  have huc := hu.continuousOn
  have hdc := hu.continuousOn_fderiv_of_isOpen hO (by simp)
  have hclosed : IsClosed {q : O | u q=0 ∧ fderiv ℝ u q=0} :=
    (isClosed_eq (huc.comp_continuous continuous_subtype_val (fun q => q.property)) continuous_const).inter
      (isClosed_eq (hdc.comp_continuous continuous_subtype_val (fun q => q.property)) continuous_const)
  have hzero (q : E2) (hq : q ∈ Z) : u q=0 ∧ fderiv ℝ u q=0 := by
    obtain ⟨V,hV,hqV,hVO,hVz⟩ := hq.2
    have he : u =ᶠ[𝓝 q] (fun _ => (0:ℝ)) :=
      Filter.eventuallyEq_of_mem (hV.mem_nhds hqV) hVz
    exact ⟨hVz hqV,by rw [he.fderiv_eq]; simp⟩
  have hsub : Subtype.val ⁻¹' Z ⊆ {q : O | u q=0 ∧ fderiv ℝ u q=0} :=
    fun q hq => hzero q hq
  have hcl : (⟨p,hp⟩:O) ∈ closure (Subtype.val ⁻¹' Z) := by
    rw [← hO.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val]
    exact hacc
  exact closure_minimal hsub hclosed hcl

/-- A rank-two parametrization with zero normal derivative has invertible
projection onto the two-dimensional graph base. -/
theorem native_projected_derivative_invertible_v475
    (L : E2 →L[ℝ] (E2 × ℝ)) (hL : Function.Injective L)
    (hnormal : (ContinuousLinearMap.snd ℝ E2 ℝ).comp L=0) :
    ((ContinuousLinearMap.fst ℝ E2 ℝ).comp L).IsInvertible := by
  have hi : Function.Injective ((ContinuousLinearMap.fst ℝ E2 ℝ).comp L) := by
    intro x y hxy
    apply hL
    apply Prod.ext hxy
    have hn (z : E2) : (L z).2=0 := congrArg (fun A : E2 →L[ℝ] ℝ => A z) hnormal
    change (L x).2 = (L y).2
    rw [hn x,hn y]
  have hs := LinearMap.injective_iff_surjective.mp hi
  exact ⟨(LinearEquiv.ofBijective _ ⟨hi,hs⟩).toContinuousLinearEquiv,rfl⟩

#print axioms native_zero_germ_value_derivative_closure_v475
#print axioms native_projected_derivative_invertible_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
