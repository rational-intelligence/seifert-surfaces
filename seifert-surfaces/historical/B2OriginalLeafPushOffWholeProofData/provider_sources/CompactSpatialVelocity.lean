import MovingCompactVelocity

open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SecondCountableTopology M]
  {f g : NeatEmbedding S M}

/-- The global field in precisely the time-dependent spatial form needed for
integration on the ambient manifold. All data are produced from the original
normal isotopy. -/
theorem normal_exists_compact_spatial_velocity
    (F : SmoothNormalIsotopy S M f g) :
    ∃ K : Set M, IsCompact K ∧
      ∃ Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2,
        ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
          (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)) ∧
        (∀ p, Y (normalTrace F p) = traceVelocity F p) ∧
        (∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0) ∧
        ∀ q, q.2 ∉ K → Y q = 0 := by
  obtain ⟨K,hK,X,hX,hXt,hXtrace,hXb,hXs⟩ := normal_exists_compact_tangent_velocity F
  let Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2 := fun q => (X q).2
  have hprod := contMDiff_equivTangentBundleProd.comp hX
  have hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)) :=
    contMDiff_snd.comp hprod
  refine ⟨K,hK,Y,hY,hXtrace,hXb,?_⟩
  intro q hq
  change (X q).2 = 0
  rw [hXs q hq]
  rfl

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
