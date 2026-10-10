import Section5RadialCylinderEmbeddingV489
import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

def straightenedRealCollar (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞) (FB : Circle × ℝ → ℝ)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (R : ℝ) : T2Coordinate → E.Carrier :=
  straightenedTimeCollar a rho FB d hd hd1 V C ∘ radialCylinderRescaling R

theorem straightened_real_collar_smooth (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FB : Circle × ℝ → ℝ) (hFB : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FB)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (R : ℝ) (hR : 0 < R) (eta : ℝ) :
    ContMDiffOn ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) (𝓡∂ 3) ∞
      (straightenedRealCollar a rho FB d hd hd1 V C R) (halfCylinder R eta) :=
  (straightened_time_collar_smooth a rho FB hFB d hd hd1 V C).comp_contMDiffOn
    (radial_cylinder_rescaling_smooth hR)

theorem straightened_real_collar_immersion (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FB : Circle × ℝ → ℝ) (hFB : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FB)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (R : ℝ) (hR : 0 < R) (eta : ℝ) (p : T2Coordinate) (hp : p ∈ halfCylinder R eta) :
    Injective (mfderivWithin ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) (𝓡∂ 3)
      (straightenedRealCollar a rho FB d hd hd1 V C R) (halfCylinder R eta) p) := by
  rw [straightenedRealCollar,mfderiv_comp_mfderivWithin p
    ((straightened_time_collar_smooth a rho FB hFB d hd hd1 V C).mdifferentiableAt (by simp))
    ((radial_cylinder_rescaling_smooth hR p hp).mdifferentiableWithinAt (by simp))
    (half_cylinder_unique hR p hp)]
  exact (straightened_time_collar_differential_injective a rho FB hFB d hd hd1 V C _).comp
    (radial_cylinder_rescaling_differential_injective hR p hp)

theorem straightened_real_collar_embedding (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FB : Circle × ℝ → ℝ) (hFB : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FB)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (R : ℝ) (hR : 0 < R) :
    IsEmbedding (fun p : halfCylinder R 1 => straightenedRealCollar a rho FB d hd hd1 V C R p) :=
  (straightened_time_collar_closed_embedding a rho FB hFB d hd hd1 V C).comp
    (radial_cylinder_closed_rescaling_embedding hR)

/-- The actual collar image has unique manifold derivatives, including its boundary. -/
theorem straightened_real_collar_image_unique (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FB : Circle × ℝ → ℝ) (hFB : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FB)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (R : ℝ) (hR : 0 < R) (eta : ℝ) :
    UniqueMDiffOn (𝓡∂ 3) (straightenedRealCollar a rho FB d hd hd1 V C R '' halfCylinder R eta) := by
  apply (half_cylinder_unique hR).image_denseRange
    ((straightened_real_collar_smooth a rho FB hFB d hd hd1 V C R hR eta).mdifferentiableOn (by simp))
  intro p hp
  apply Function.Surjective.denseRange
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=
    (mfderivWithin ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) (𝓡∂ 3)
      (straightenedRealCollar a rho FB d hd hd1 V C R) (halfCylinder R eta) p).toLinearMap) ?_).mp
    (straightened_real_collar_immersion a rho FB hFB d hd hd1 V C R hR eta p hp)
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × (ℝ × ℝ)) =
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
  simp

/-- Restricting an actual distance function to a full-dimensional collar image
preserves its metric gradient and all other distance clauses. -/
theorem inward_distance_restrict_unique (g : SmoothMetric E.Carrier)
    {U W : Set E.Carrier} {r : E.Carrier → ℝ}
    (hr : IsInwardDistanceCoordinate g U r) (hWU : W ⊆ U)
    (hW : UniqueMDiffOn (𝓡∂ 3) W) : IsInwardDistanceCoordinate g W r := by
  refine ⟨hr.1.mono hWU,fun p hp => hr.2.1 p (hWU hp),fun p hp => hr.2.2.1 p (hWU hp),?_⟩
  intro p hp
  obtain ⟨n,hn,hnr⟩ := hr.2.2.2 p (hWU hp)
  refine ⟨n,hn,?_⟩
  intro w
  rw [((hr.1 p (hWU hp)).mdifferentiableWithinAt (by simp)).mfderivWithin_mono (hW p hp) hWU]
  exact hnr w

#print axioms straightened_real_collar_smooth
#print axioms straightened_real_collar_immersion
#print axioms straightened_real_collar_embedding
#print axioms straightened_real_collar_image_unique
#print axioms inward_distance_restrict_unique
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
