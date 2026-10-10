import A2MetricFluxV468

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter MeasureTheory
open scoped ContDiff
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen

/-- Exact Jacobian transport for the actual affine bulk frame. The boundary
clock is absent; the determinant belongs to that same frame. -/
theorem native_affine_bulk_volume_transport
    (p : E2) (A : E2 ≃L[ℝ] E2) (Z : Set (ℝ × ℝ)) (hZ : MeasurableSet Z)
    (d : E2 → ℝ) :
    let T := fun z : ℝ × ℝ => p + A (coordinates.symm z)
    MeasurableSet (T '' Z) ∧
      (IntegrableOn d (T '' Z) ↔
        IntegrableOn (fun z => |(A : E2 →L[ℝ] E2).det| * d (T z)) Z) ∧
      (∫ x in T '' Z, d x) =
        ∫ z in Z, |(A : E2 →L[ℝ] E2).det| * d (T z) := by
  dsimp only
  let B := coordinates ⁻¹' Z
  let T := fun x : E2 => p + A x
  let e := fun x : E2 => |(A : E2 →L[ℝ] E2).det| * d (T x)
  have hB : MeasurableSet B := hZ.preimage coordinates.continuous.measurable
  have hdf : ∀ x ∈ B, HasFDerivWithinAt T (A : E2 →L[ℝ] E2) B x := by
    intro x hx
    have hd : HasFDerivAt T (A : E2 →L[ℝ] E2) x := A.hasFDerivAt.const_add p
    exact hd.hasFDerivWithinAt
  have hinj : InjOn T B := by
    intro x hx y hy h
    exact A.injective (add_left_cancel h)
  have himage : T '' B = (fun z : ℝ × ℝ => p + A (coordinates.symm z)) '' Z := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨coordinates y,hy,by simp only [ContinuousLinearEquiv.symm_apply_apply]; rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨coordinates.symm z,by simpa only [B,mem_preimage,
        ContinuousLinearEquiv.apply_symm_apply] using hz,rfl⟩
  have hBi : coordinates.symm '' Z = B := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      simpa only [B,mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hz
    · intro hx
      exact ⟨coordinates x,hx,coordinates.symm_apply_apply x⟩
  have hMP : MeasurePreserving coordinates (volume : Measure E2) (volume : Measure (ℝ × ℝ)) :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  have hMPs : MeasurePreserving coordinates.symm (volume : Measure (ℝ × ℝ)) (volume : Measure E2) :=
    hMP.symm coordinates.toHomeomorph.toMeasurableEquiv
  have hcoords : IntegrableOn (fun z => e (coordinates.symm z)) Z ↔ IntegrableOn e B := by
    have hr := hMPs.restrict_image_emb coordinates.symm.toHomeomorph.measurableEmbedding Z
    rw [hBi] at hr
    simpa only [IntegrableOn,Function.comp_def] using
      hr.integrable_comp_emb coordinates.symm.toHomeomorph.measurableEmbedding (g := e)
  have hi := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (volume : Measure E2) hB hdf hinj d
  have hint := integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure E2) hB hdf hinj d
  have hchange := hMPs.setIntegral_image_emb coordinates.symm.toHomeomorph.measurableEmbedding e Z
  rw [hBi] at hchange
  refine ⟨?_,?_,?_⟩
  · rw [← himage]
    exact measurable_image_of_fderivWithin hB hdf hinj
  · rw [← himage]
    have hi' : IntegrableOn d (T '' B) ↔ IntegrableOn e B := by
      simpa only [smul_eq_mul] using hi
    exact hi'.trans hcoords.symm
  · rw [← himage]
    have hint' : (∫ x in T '' B,d x) = ∫ x in B,e x := by
      simpa only [smul_eq_mul] using hint
    exact hint'.trans hchange

#print axioms native_affine_bulk_volume_transport
end SeifertSurfaces.OriginalEndpoints.A2NativeTests
