import Section5WarpedNormalV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem actual_exterior_smooth_embedding :
    Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion

theorem exterior_differential_surjective (p : E.Carrier) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 3) E.toSphere p) := by
  have hi : Injective (mfderiv (𝓡∂ 3) (𝓡 3) E.toSphere p) :=
    actual_exterior_smooth_embedding.isImmersion.mfderiv_injective (by simp) p
  exact LinearMap.surjective_of_injective
    (f := (mfderiv (𝓡∂ 3) (𝓡 3) E.toSphere p).toLinearMap) hi

theorem warped_exterior_inward_distance (G : A7.SourceGeometry E)
    (C : WarpedBoundaryCollar G.extension (Set.range E.toSphere)) :
    IsInwardDistanceCoordinate G.metric
      (E.toSphere ⁻¹' C.coordinates.chart.source) (C.radial ∘ E.toSphere) := by
  have hi : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := actual_exterior_smooth_embedding.contMDiff
  have hopen : IsOpen (E.toSphere ⁻¹' C.coordinates.chart.source) :=
    C.coordinates.chart.open_source.preimage hi.continuous
  have hs : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ) ∞ (C.radial ∘ E.toSphere)
      (E.toSphere ⁻¹' C.coordinates.chart.source) :=
    C.radial_smooth.comp hi.contMDiffOn (fun _ h => h)
  refine ⟨hs, ?_, ?_, ?_⟩
  · intro p hp
    exact (C.region_identification (E.toSphere p) hp).mp ⟨p,rfl⟩
  · intro p hp
    exact (G.boundary_exact p).symm.trans (C.boundary_identification (E.toSphere p) hp)
  · intro p hp
    obtain ⟨n,hn⟩ := exterior_differential_surjective p (warpedMetricNormal C (E.toSphere p))
    refine ⟨n, ?_, ?_⟩
    · rw [G.metric_restriction, hn]
      exact warped_metric_normal_unit C (E.toSphere p) hp
    · intro w
      rw [G.metric_restriction, hn, warped_metric_normal_pairing C (E.toSphere p) hp]
      rw [mfderivWithin_eq_mfderiv (hopen.uniqueMDiffWithinAt hp)
        (((hs p hp).contMDiffAt (hopen.mem_nhds hp)).mdifferentiableAt (by simp))]
      rw [mfderiv_comp p
        (((C.radial_smooth (E.toSphere p) hp).contMDiffAt
          (C.coordinates.chart.open_source.mem_nhds hp)).mdifferentiableAt (by simp))
        (hi.mdifferentiable (by simp) p)]
      rfl

theorem actual_local_inward_distance (G : A7.SourceGeometry E)
    (p : E.Carrier) (hp : p ∈ (𝓡∂ 3).boundary E.Carrier) :
    ∃ U : Set E.Carrier, IsOpen U ∧ p ∈ U ∧
      ∃ r : E.Carrier → ℝ, IsInwardDistanceCoordinate G.metric U r := by
  obtain ⟨C,hC⟩ := G.collars p hp
  refine ⟨E.toSphere ⁻¹' C.coordinates.chart.source,
    C.coordinates.chart.open_source.preimage actual_exterior_smooth_embedding.contMDiff.continuous,hC,
    C.radial ∘ E.toSphere,warped_exterior_inward_distance G C⟩

#print axioms actual_local_inward_distance
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
