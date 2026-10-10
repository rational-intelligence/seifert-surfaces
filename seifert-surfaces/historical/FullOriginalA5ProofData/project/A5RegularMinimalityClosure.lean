import A5MinimalityClosure

set_option autoImplicit false
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- Actual coordinate minimality extends from a dense subset of any smooth
regular patch. A continuous left inverse is constructed locally from rank;
no fixed projection or graph presentation is assumed. -/
theorem coordinate_minimality_of_dense_regular_patch
    (V : Set E3) (hV : IsOpen V) (g : CoordinateMetric V)
    (U W : Set E2) (hU : IsOpen U) (hdense : U ⊆ closure W)
    (Φ : E2 → E3) (hΦ : ContDiffOn ℝ ∞ Φ U) (himage : MapsTo Φ U V)
    (hrank : ∀ x ∈ U, Function.Injective (fderiv ℝ Φ x))
    (hminimal : IsMinimalParametrizationOn g.tensor Φ W) :
    IsMinimalParametrizationOn g.tensor Φ U := by
  have hD := hΦ.continuousOn_fderiv_of_isOpen hU (by simp)
  have hT := traced_acceleration_continuous_on V hV g U hU Φ hΦ himage hrank
  refine ⟨hΦ, ?_⟩
  intro x hx
  obtain ⟨P, hP⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (hrank x hx)
  let A : E2 → E2 →L[ℝ] E2 := fun y => P.comp (fderiv ℝ Φ y)
  have hAx : A x = ContinuousLinearMap.id ℝ E2 := by
    apply ContinuousLinearMap.ext
    intro v
    exact hP v
  have hAc : ContinuousAt A x := continuousAt_const.clm_comp
    (hD.continuousAt (hU.mem_nhds hx))
  have hAxinv : (A x).IsInvertible := by rw [hAx]; exact ⟨ContinuousLinearEquiv.refl ℝ E2, rfl⟩
  have hAi : ContinuousAt (fun y => (A y).inverse) x :=
    (hAxinv.contDiffAt_map_inverse (n := ∞)).continuousAt.comp hAc
  let B : Set E2 := {y | (A y).IsInvertible}
  have hB : B ∈ 𝓝 x := hAc hAxinv.eventually_nhds
  let R : E2 → E3 := fun y => (fderiv ℝ Φ y)
    ((A y).inverse (P (tracedAcceleration g.tensor Φ y))) -
      tracedAcceleration g.tensor Φ y
  have hR : ContinuousAt R x :=
    ((hD.continuousAt (hU.mem_nhds hx)).clm_apply
      (hAi.clm_apply (P.continuous.continuousAt.comp
        (hT.continuousAt (hU.mem_nhds hx))))).sub
      (hT.continuousAt (hU.mem_nhds hx))
  have hz (y : E2) (hy : y ∈ W ∩ B) : R y = 0 := by
    obtain ⟨v, hv⟩ := hminimal.2 y hy.1
    change (fderiv ℝ Φ y) v = tracedAcceleration g.tensor Φ y at hv
    have hi : (A y).inverse ((A y) v) = v := hy.2.inverse_apply_self v
    dsimp only [R]
    rw [← hv]
    change (fderiv ℝ Φ y) ((A y).inverse ((A y) v)) - (fderiv ℝ Φ y) v = 0
    rw [hi, sub_self]
  have hxc : x ∈ closure (W ∩ B) := by
    apply mem_closure_iff_nhds.mpr
    intro O hO
    obtain ⟨y, hy, hyW⟩ := mem_closure_iff_nhds.mp (hdense hx) (O ∩ B) (inter_mem hO hB)
    exact ⟨y, hy.1, hyW, hy.2⟩
  have he : R x = 0 := hR.continuousWithinAt.eq_const_of_mem_closure hxc hz
  exact ⟨(A x).inverse (P (tracedAcceleration g.tensor Φ x)), sub_eq_zero.mp he⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
