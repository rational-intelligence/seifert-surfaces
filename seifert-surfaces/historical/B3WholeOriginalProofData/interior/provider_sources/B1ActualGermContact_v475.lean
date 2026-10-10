import B1ActualSurfaceGermTopology_v475
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

/-- An accumulation point of actual image agreement germs belongs to the
opposite compact surface. Neatness places its unique opposite preimage in the
surface interior. This is actual image contact, before analytic continuation. -/
theorem native_actual_germ_contact_v475
    {S : CompactOrientedSurface.{u}} {T : CompactOrientedSurface.{w}}
    (f : ProperSmoothEmbedding S M) (g : ProperSmoothEmbedding T M)
    (x : (𝓡∂ 2).interior S)
    (hacc : x ∈ closure {z : (𝓡∂ 2).interior S |
      native_surface_germ_eq_v475 f.image g.image (f.toFun z)}) :
    ∃ y : (𝓡∂ 2).interior T, g.toFun y = f.toFun x := by
  have hG : IsClosed g.image := (isCompact_range g.smooth.continuous).isClosed
  have hpre : IsClosed {z : (𝓡∂ 2).interior S | f.toFun z ∈ g.image} :=
    hG.preimage (f.smooth.continuous.comp continuous_subtype_val)
  have hsub : {z : (𝓡∂ 2).interior S |
      native_surface_germ_eq_v475 f.image g.image (f.toFun z)} ⊆
      {z : (𝓡∂ 2).interior S | f.toFun z ∈ g.image} := by
    rintro z ⟨O,hO,hzO,heq⟩
    exact (heq ▸ (show f.toFun z ∈ f.image ∩ O from ⟨⟨z,rfl⟩,hzO⟩)).1
  obtain ⟨y,hy⟩ := closure_minimal hsub hpre hacc
  have hxI : (x : S) ∉ S.boundary := by
    have hinside (z : S) (hz : z ∈ (𝓡∂ 2).interior S) : z ∉ S.boundary := by
      rw [← (𝓡∂ 2).compl_boundary] at hz
      exact hz
    exact hinside x x.property
  have hpI : f.toFun x ∉ (𝓡∂ 3).boundary M := by
    intro hp
    apply hxI
    rwa [← f.boundary_preimage]
  have hyI : y ∈ (𝓡∂ 2).interior T := by
    rw [← (𝓡∂ 2).compl_boundary]
    intro hyb
    change y ∈ T.boundary at hyb
    have hpy : g.toFun y ∈ (𝓡∂ 3).boundary M := by
      rwa [← g.boundary_preimage] at hyb
    exact hpI (hy ▸ hpy)
  exact ⟨⟨y,hyI⟩,hy⟩

#print axioms native_actual_germ_contact_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
