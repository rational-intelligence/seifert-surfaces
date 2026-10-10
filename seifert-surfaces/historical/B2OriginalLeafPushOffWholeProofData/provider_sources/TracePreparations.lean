import NeatTransport

open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
universe u v
noncomputable section
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  {f g : NeatEmbedding S M}

/-- The time coordinate makes the entire compact isotopy track injective. -/
def normalTrace (F : SmoothNormalIsotopy S M f g) (p : Time × S) : Time × M :=
  (p.1, (F.stage p.1).toFun p.2)

theorem normalTrace_injective (F : SmoothNormalIsotopy S M f g) :
    Function.Injective (normalTrace F) := by
  rintro ⟨t,x⟩ ⟨s,y⟩ h
  have ht : t = s := congrArg Prod.fst h
  subst s
  have hx : x = y := (F.stage t).smoothEmbedding.isEmbedding.injective (congrArg Prod.snd h)
  subst y
  rfl

theorem normalTrace_continuous (F : SmoothNormalIsotopy S M f g) :
    Continuous (normalTrace F) :=
  continuous_fst.prodMk F.smooth_family.continuous

theorem normalTrace_contMDiff (F : SmoothNormalIsotopy S M f g) :
    ContMDiff ((𝓡∂ 1).prod (𝓡∂ 2)) ((𝓡∂ 1).prod (𝓡∂ 3)) ∞ (normalTrace F) :=
  contMDiff_fst.prodMk F.smooth_family

theorem normalTrace_isCompact (F : SmoothNormalIsotopy S M f g) :
    IsCompact (Set.range (normalTrace F)) :=
  isCompact_range (normalTrace_continuous F)

theorem normalTrace_isClosedEmbedding [T2Space M]
    (F : SmoothNormalIsotopy S M f g) : IsClosedEmbedding (normalTrace F) :=
  (normalTrace_continuous F).isClosedEmbedding (normalTrace_injective F)

theorem normalTrace_image_boundary (F : SmoothNormalIsotopy S M f g) :
    normalTrace F ⁻¹' ((univ : Set Time) ×ˢ (𝓡∂ 3).boundary M) =
      (univ : Set Time) ×ˢ S.boundary := by
  ext p
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, normalTrace]
  change p.2 ∈ (F.stage p.1).toFun ⁻¹' (𝓡∂ 3).boundary M ↔ p.2 ∈ S.boundary
  rw [(F.stage p.1).boundary_preimage]

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
