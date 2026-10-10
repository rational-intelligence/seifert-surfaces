import Section5SurfaceBoundaryInverseV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.OriginalEndpoints.A7Support
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- Lift the actual common boundary parametrization into the actual embedded
surface, preserving its full differential rank. -/
theorem actual_surface_boundary_parameter {S : CompactOrientedSurface.{0}}
    (F : NeatEmbedding S E.Carrier) (gamma : Circle → E.Carrier)
    (hgamma : IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞ gamma)
    (himage : range gamma = F.toFun '' S.boundary) :
    ∃ beta : Circle → S,
      ContMDiff (𝓡 1) (𝓡∂ 2) ∞ beta ∧ IsEmbedding beta ∧
      (∀ z, F.toFun (beta z) = gamma z) ∧ range beta = S.boundary ∧
      ∀ z, Injective (mfderiv (𝓡 1) (𝓡∂ 2) beta z) := by
  classical
  have hex (z : Circle) : ∃ x ∈ S.boundary, F.toFun x = gamma z := by
    have hm : gamma z ∈ F.toFun '' S.boundary := by
      rw [← himage]
      exact mem_range_self z
    exact hm
  choose beta hbetaBoundary hbeta using hex
  have heq : F.toFun ∘ beta = gamma := funext hbeta
  have hc : Continuous beta :=
    F.smoothEmbedding.isEmbedding.continuous_iff.mpr (heq ▸ hgamma.contMDiff.continuous)
  have hs : ContMDiff (𝓡 1) (𝓡∂ 2) ∞ beta :=
    (ContMDiff.iff_comp_isImmersion F.smoothEmbedding.isImmersion).mpr
      ⟨hc,heq ▸ hgamma.contMDiff⟩
  have hb : IsEmbedding beta := F.smoothEmbedding.isEmbedding.of_comp_iff.mp
    (heq ▸ hgamma.isEmbedding)
  refine ⟨beta,hs,hb,hbeta,?_,?_⟩
  · apply subset_antisymm
    · rintro _ ⟨z,rfl⟩
      exact hbetaBoundary z
    · intro x hx
      have hxg : F.toFun x ∈ range gamma := by
        rw [himage]
        exact mem_image_of_mem F.toFun hx
      obtain ⟨z,hz⟩ := hxg
      exact ⟨z,F.smoothEmbedding.isEmbedding.injective ((hbeta z).trans hz)⟩
  · intro z
    have hinj : Injective (mfderiv (𝓡 1) (𝓡∂ 3) (F.toFun ∘ beta) z) :=
      heq ▸ hgamma.isImmersion.mfderiv_injective (by simp) z
    rw [mfderiv_comp z (F.smoothEmbedding.contMDiff.mdifferentiableAt (by simp))
      (hs.mdifferentiableAt (by simp))] at hinj
    intro u v huv
    apply hinj
    change mfderiv (𝓡∂ 2) (𝓡∂ 3) F.toFun (beta z)
      (mfderiv (𝓡 1) (𝓡∂ 2) beta z u) =
      mfderiv (𝓡∂ 2) (𝓡∂ 3) F.toFun (beta z)
      (mfderiv (𝓡 1) (𝓡∂ 2) beta z v)
    rw [huv]

/-- The actual inward distance restricts to a noncritical defining function
on every actual neat surface at its boundary. -/
theorem actual_surface_distance_noncritical {S : CompactOrientedSurface.{0}}
    (F : NeatEmbedding S E.Carrier) (g : SmoothMetric E.Carrier)
    {U : Set E.Carrier} (hU : IsOpen U) {r : E.Carrier → ℝ}
    (hr : IsInwardDistanceCoordinate g U r) {x : S} (hx : x ∈ S.boundary)
    (hxU : F.toFun x ∈ U) :
    MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ) (r ∘ F.toFun) x ∧
      mfderiv (𝓡∂ 2) 𝓘(ℝ) (r ∘ F.toFun) x ≠ 0 := by
  have hFx : F.toFun x ∈ (𝓡∂ 3).boundary E.Carrier := by
    change x ∈ F.toFun ⁻¹' ((𝓡∂ 3).boundary E.Carrier)
    rwa [F.boundary_preimage]
  have hdr : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ) r (F.toFun x) :=
    ((hr.1 _ hxU).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
  have hdF := F.smoothEmbedding.contMDiff.mdifferentiableAt (by simp) (x := x)
  refine ⟨hdr.comp x hdF,?_⟩
  obtain ⟨w,hw⟩ := F.boundary_transverse x hx
  have hpositive : ∃ v : TangentSpace (𝓡∂ 2) x,
      0 < inwardCoordinate (F.toFun x) (mfderiv (𝓡∂ 2) (𝓡∂ 3) F.toFun x v) := by
    rcases lt_or_gt_of_ne hw with hn | hp
    · refine ⟨-w,?_⟩
      rw [map_neg,inwardCoordinate_eq_coordinate]
      rw [inwardCoordinate_eq_coordinate] at hn
      change 0 < -(show SeifertSurfaces.AppendixACoordinates.E3 from
        mfderiv (𝓡∂ 2) (𝓡∂ 3) F.toFun x w) 0
      exact neg_pos.mpr hn
    · exact ⟨w,hp⟩
  obtain ⟨v,hv⟩ := hpositive
  have hp := inward_distance_differential_positive g hU hr hxU hFx
    (mfderiv (𝓡∂ 2) (𝓡∂ 3) F.toFun x v) hv
  intro hzero
  rw [mfderiv_comp x hdr hdF] at hzero
  have hz := congrArg (fun d => d v) hzero
  change mfderiv (𝓡∂ 3) 𝓘(ℝ) r (F.toFun x)
    (mfderiv (𝓡∂ 2) (𝓡∂ 3) F.toFun x v) = 0 at hz
  exact hp.ne' hz

#print axioms actual_surface_boundary_parameter
#print axioms actual_surface_distance_noncritical
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
