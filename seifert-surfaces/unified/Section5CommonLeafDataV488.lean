import Section5CommonLeafSmoothEmbeddingV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem common_leaf_parameter_data (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (A B : IncompressibleSpanningSurface.{0} E)
    (hA : IsRelativeAreaMinimizer g J A) (hB : IsRelativeAreaMinimizer g J B)
    (hcommon : SurfaceBoundary E A = SurfaceBoundary E B) :
    ∃ (a : Circle) (γ : Circle → E.Carrier) (L : ℝ),
      A.1.embedding.toFun '' A.1.surface.boundary = J.leaf a ∧
      B.1.embedding.toFun '' B.1.surface.boundary = J.leaf a ∧
      Manifold.IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞ γ ∧
      range γ = J.leaf a ∧ 0 < L ∧
      ∀ t : ℝ,
        let c := fun s : ℝ => γ (Circle.exp (2 * Real.pi * s / L))
        let v := mfderiv 𝓘(ℝ) (𝓡∂ 3) c t
          ((NormedSpace.fromTangentSpace t).symm 1)
        g.inner (c t) v v = 1 := by
  obtain ⟨a,hAa,hBa⟩ := common_boundary_label J A B hA.1 hB.1 hcommon
  exact ⟨a,longitudeUnitParameter g J a,longitudeLength g J a,hAa,hBa,
    longitude_unit_parameter_smoothEmbedding g J a,longitude_unit_parameter_image g J a,
    longitude_length_positive g J a,longitude_unit_parameter_arclength g J a⟩

#print axioms common_leaf_parameter_data
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
