import SpatialFlowAmbientSegment
import NormalTraceIntegralCurve

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] {f g : NeatEmbedding S M}

/-- Every short flow segment transports the original moving embeddings at its
endpoints, by uniqueness for the same already constructed field. -/
theorem spatial_flow_segment_tracks_normal
    (F : SmoothNormalIsotopy S M f g)
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    (htrace : ∀ p, Y (normalTrace F p) = traceVelocity F p)
    {a b : Time} (hab : a ≤ b) {Φ : ℝ → ℝ → M → M}
    (hΦ : SpatialFlowOn Y (a : ℝ) (b : ℝ) Φ) :
    ∃ H : SmoothAmbientIsotopy M, ∀ x,
      H.stage 1 ((F.stage a).toFun x) = (F.stage b).toFun x := by
  obtain ⟨H,hH⟩ := spatial_flow_ambient_segment hΦ ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩
  refine ⟨H,?_⟩
  intro x
  let γ : ℝ → M := fun t => Φ (a : ℝ) t ((F.stage a).toFun x)
  have hγ : ContinuousOn γ (Icc (a : ℝ) (b : ℝ)) := by
    intro t ht
    exact (hΦ.2.2.2.2 a ⟨le_rfl,hab⟩ t ht ((F.stage a).toFun x)).continuousAt.continuousWithinAt
  have hη : ContinuousOn (normalStageCurve F x) (Icc (a : ℝ) (b : ℝ)) :=
    (normalStageCurve_contMDiffOn F x).continuousOn.mono (Icc_subset_Icc a.property.1 b.property.2)
  have hηd (t : ℝ) (ht : t ∈ Icc (a : ℝ) (b : ℝ)) :
      HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) (normalStageCurve F x) (Icc (a : ℝ) (b : ℝ)) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight
          (Y (projIcc 0 1 (by norm_num) t,normalStageCurve F x t))) := by
    have hh := (normalStageCurve_hasMFDerivWithinAt F x
      ((Icc_subset_Icc a.property.1 b.property.2) ht)).mono
      (Icc_subset_Icc a.property.1 b.property.2)
    have hv := htrace (projIcc 0 1 (by norm_num) t,x)
    change Y (projIcc 0 1 (by norm_num) t,normalStageCurve F x t) = _ at hv
    rw [hv]
    exact hh
  have hinit : γ (a : ℝ) = normalStageCurve F x a := by
    dsimp only [γ,normalStageCurve]
    rw [hΦ.2.1 a ⟨le_rfl,hab⟩,projIcc_of_mem (by norm_num) a.property]
  have hh := spatial_solution_unique_Icc Y hY hYb
    (Icc_subset_Icc a.property.1 b.property.2) hγ hη
    (fun t ht => (hΦ.2.2.2.2 a ⟨le_rfl,hab⟩ t ht ((F.stage a).toFun x)).hasMFDerivWithinAt)
    hηd (t₀ := (a : ℝ)) ⟨le_rfl,hab⟩ hinit
  rw [hH]
  have hb := hh ⟨hab,le_rfl⟩
  simpa only [γ,normalStageCurve,projIcc_of_mem (by norm_num) b.property] using hb

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
