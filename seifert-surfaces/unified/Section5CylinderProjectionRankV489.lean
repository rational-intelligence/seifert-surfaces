import Section5CylinderLocalInverseV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates
noncomputable section

/-- Both actual coordinate directions lie in the image of the differential. -/
theorem product_coordinate_rank (L : E2 →L[ℝ]
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
    (hnormal : ∃ u, (L u).2 ≠ 0)
    (htangent : ∀ v : EuclideanSpace ℝ (Fin 1), ∃ w, L w = (v,0)) : Injective L := by
  have hdim : Module.finrank ℝ E2 =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) := by simp
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=L.toLinearMap) hdim).mpr
  obtain ⟨u,hu⟩ := hnormal
  have hu0 : (L u).2 0 ≠ 0 := by
    intro he
    apply hu
    ext i
    fin_cases i
    exact he
  intro z
  let c := z.2 0 / (L u).2 0
  obtain ⟨w,hw⟩ := htangent (z.1 - c • (L u).1)
  refine ⟨c • u + w,?_⟩
  change L (c • u + w) = z
  rw [map_add,map_smul,hw]
  apply Prod.ext
  · change c • (L u).1 + (z.1-c • (L u).1) = z.1
    abel
  · ext i
    fin_cases i
    change c * (L u).2 0 + 0 = z.2 0
    rw [add_zero]
    exact div_mul_cancel₀ _ hu0

/-- Exact lower-boundary parametrization and a noncritical actual radial
coordinate force the cylinder projection to have full rank. -/
theorem cylinder_projection_rank {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] [IsManifold (𝓡∂ 2) ∞ S]
    {f : S → Circle × Time} {beta : Circle → S} {z : Circle}
    (hf : MDifferentiableAt (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) f (beta z))
    (hbeta : MDifferentiableAt (𝓡 1) (𝓡∂ 2) beta z)
    (heq : ∀ w, f (beta w) = (w,0))
    (hr : mfderiv (𝓡∂ 2) 𝓘(ℝ) (fun y => ((f y).2 : ℝ)) (beta z) ≠ 0) :
    Injective (mfderiv (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) f (beta z)) := by
  let df := mfderiv (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) f (beta z)
  let db := mfderiv (𝓡 1) (𝓡∂ 2) beta z
  have ht : ∀ v : EuclideanSpace ℝ (Fin 1), ∃ w, df w = (v,0) := by
    intro v
    refine ⟨db v,?_⟩
    have hfun : f ∘ beta = fun w => (w,(0:Time)) := funext heq
    have hh := congrArg (fun d => d v) (mfderiv_comp z hf hbeta)
    rw [hfun,mfderiv_prod_left] at hh
    exact hh.symm
  have hn : ∃ u, (df u).2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hr
    have hds : MDifferentiableAt ((𝓡 1).prod (𝓡∂ 1)) (𝓡∂ 1) Prod.snd (f (beta z)) :=
      mdifferentiableAt_snd
    have hdt : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Time → ℝ) (f (beta z)).2 :=
      contMDiff_subtypeVal_Icc.mdifferentiableAt (n:=∞) (by simp)
    have he : (fun y => ((f y).2 : ℝ)) = Subtype.val ∘ (Prod.snd ∘ f) := rfl
    rw [he]
    rw [mfderiv_comp (beta z) (f:=Prod.snd ∘ f) (g:=Subtype.val) hdt (hds.comp _ hf)]
    rw [mfderiv_comp (beta z) hds hf,mfderiv_snd]
    ext u
    change mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Time → ℝ) (f (beta z)).2 (df u).2 = 0
    rw [h u,map_zero]
  have hh := product_coordinate_rank df hn ht
  exact hh

#print axioms product_coordinate_rank
#print axioms cylinder_projection_rank
end
end SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
