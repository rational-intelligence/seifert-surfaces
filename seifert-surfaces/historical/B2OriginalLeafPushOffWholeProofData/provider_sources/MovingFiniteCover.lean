import MovingChartVelocity

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] {f g : NeatEmbedding S M}

/-- Compactness converts the pointwise moving retractions into one finite chart
cover of the entire compact trace. The local retractions and their boundary
properties are retained at each selected chart. -/
theorem normalTrace_exists_finite_retraction_cover
    (F : SmoothNormalIsotopy S M f g) :
    ∃ K : Set (Time × S), K.Finite ∧
      (∀ p ∈ K, ∃ U : Set (Time × M), IsOpen U ∧ normalTrace F p ∈ U ∧
        ∃ r : Time × M → S,
          ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 2) ∞ r U ∧
          (∀ q, normalTrace F q ∈ U → r (normalTrace F q) = q.2) ∧
          ∀ q ∈ U, q.2 ∈ (𝓡∂ 3).boundary M → r q ∈ S.boundary) ∧
      range (normalTrace F) ⊆ ⋃ p ∈ K,
        Classical.choose (normal_exists_moving_retraction F p) := by
  classical
  let U : Time × S → Set (Time × M) :=
    fun p => Classical.choose (normal_exists_moving_retraction F p)
  have hUo : ∀ p, IsOpen (U p) := fun p =>
    (Classical.choose_spec (normal_exists_moving_retraction F p)).1
  have hUc : range (normalTrace F) ⊆ ⋃ p, U p := by
    rintro z ⟨p,rfl⟩
    exact mem_iUnion_of_mem p
      (Classical.choose_spec (normal_exists_moving_retraction F p)).2.1
  obtain ⟨K,hKuniv,hK,hcover⟩ := normalTrace_isCompact F |>.elim_finite_subcover_image
    (b := univ) (c := U) (fun p _ => hUo p) (by simpa using hUc)
  refine ⟨K,hK,?_,?_⟩
  · intro p hp
    exact normal_exists_moving_retraction F p
  · intro z hz
    obtain ⟨p,hp,hpz⟩ := mem_iUnion₂.mp (hcover hz)
    exact mem_iUnion₂.mpr ⟨p,hp,hpz⟩

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
