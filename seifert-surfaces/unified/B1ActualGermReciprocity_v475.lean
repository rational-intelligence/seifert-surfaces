import B1ActualGermContact_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v w
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Agreement-germ accumulation transfers to the actual opposite interior
preimage through the two original embeddings. -/
theorem native_actual_germ_accumulation_reciprocity_v475
    {S : CompactOrientedSurface.{u}} {T : CompactOrientedSurface.{w}}
    (f : ProperSmoothEmbedding S M) (g : ProperSmoothEmbedding T M)
    (x : (𝓡∂ 2).interior S) (y : (𝓡∂ 2).interior T)
    (hy : g.toFun y=f.toFun x)
    (hacc : x ∈ closure {z : (𝓡∂ 2).interior S |
      native_surface_germ_eq_v475 f.image g.image (f.toFun z)}) :
    y ∈ closure {z : (𝓡∂ 2).interior T |
      native_surface_germ_eq_v475 g.image f.image (g.toFun z)} := by
  let A : (𝓡∂ 2).interior S → M := fun z => f.toFun z
  let B : (𝓡∂ 2).interior T → M := fun z => g.toFun z
  let ZA := {z : (𝓡∂ 2).interior S | native_surface_germ_eq_v475 f.image g.image (f.toFun z)}
  let ZB := {z : (𝓡∂ 2).interior T | native_surface_germ_eq_v475 g.image f.image (g.toFun z)}
  have hB : IsEmbedding B := g.embedding.comp IsEmbedding.subtypeVal
  have hsub : A '' ZA ⊆ B '' ZB := by
    rintro p ⟨z,hz,rfl⟩
    obtain ⟨O,hO,hzO,heq⟩ := hz
    have hg : f.toFun z ∈ g.image :=
      (heq ▸ (show f.toFun z ∈ f.image ∩ O from ⟨⟨z,rfl⟩,hzO⟩)).1
    obtain ⟨t,ht⟩ := hg
    have htI : t ∈ (𝓡∂ 2).interior T := by
      rw [← (𝓡∂ 2).compl_boundary]
      intro htbd
      change t ∈ T.boundary at htbd
      have hpbd : g.toFun t ∈ (𝓡∂ 3).boundary M := by
        rwa [← g.boundary_preimage] at htbd
      rw [ht] at hpbd
      have hzbd : (z : S) ∈ S.boundary := by
        rw [← f.boundary_preimage]
        exact hpbd
      have hnot (a : S) (ha : a ∈ (𝓡∂ 2).interior S) : a ∉ S.boundary := by
        rw [← (𝓡∂ 2).compl_boundary] at ha
        exact ha
      exact hnot z z.property hzbd
    refine ⟨⟨t,htI⟩,?_,ht⟩
    exact ⟨O,hO,by change g.toFun t ∈ O; rwa [ht],heq.symm⟩
  have hp : A x ∈ closure (A '' ZA) :=
    image_closure_subset_closure_image (f.smooth.continuous.comp continuous_subtype_val)
      ⟨x,hacc,rfl⟩
  have hb : B y ∈ closure (B '' ZB) := by
    change g.toFun y ∈ _
    rw [hy]
    exact closure_mono hsub hp
  rwa [hB.closure_eq_preimage_closure_image ZB]

#print axioms native_actual_germ_accumulation_reciprocity_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
