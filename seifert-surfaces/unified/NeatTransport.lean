import NeatTransportHelpers

open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
universe u v
noncomputable section

variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- Postcomposition keeps the original surface and all three neatness conditions. -/
def postcompose (f : NeatEmbedding S M)
    (e : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞) : NeatEmbedding S M where
  toFun := e ∘ f.toFun
  smoothEmbedding := ⟨f.smoothEmbedding.isImmersion.comp_diffeomorph e,
    e.toHomeomorph.isEmbedding.comp f.smoothEmbedding.isEmbedding⟩
  boundary_preimage := by
    rw [Set.preimage_comp, e.preimage_boundary (by simp), f.boundary_preimage]
  boundary_transverse := by
    intro x hx
    obtain ⟨w, hw⟩ := f.boundary_transverse x hx
    have hfx : f.toFun x ∈ (𝓡∂ 3).boundary M := by
      rwa [← f.boundary_preimage] at hx
    obtain ⟨a, ha, he⟩ := inward_diffeomorph_positive e (f.toFun x) hfx
    refine ⟨w, ?_⟩
    rw [mfderiv_comp x (e.contMDiff.mdifferentiableAt (by simp))
      (f.smoothEmbedding.contMDiff.mdifferentiableAt (by simp))]
    exact (he _).trans_ne (mul_ne_zero ha.ne' hw)

theorem postcompose_image (f : NeatEmbedding S M)
    (e : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞) :
    (postcompose f e).image = e '' f.image := by
  exact Set.range_comp e f.toFun

theorem postcompose_incompressible (f : NeatEmbedding S M)
    (e : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞) :
    (postcompose f e).Incompressible ↔ f.Incompressible := by
  exact incompressible_postcompose_diffeomorph f e

/-- The equal-image proof is replayed for neat embeddings; the exterior-specific
paid theorem is not applied outside its contract. -/
theorem equal_image_reparam (f g : NeatEmbedding S M) (h : f.image = g.image) :
    ∃ e : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) S S ∞,
      ∀ x, g.toFun (e x) = f.toFun x := by
  let ef := f.smoothEmbedding.isEmbedding.toHomeomorph
  let eg := g.smoothEmbedding.isEmbedding.toHomeomorph
  have hr : Set.range f.toFun = Set.range g.toFun := h
  let e : S ≃ₜ S := ef.trans ((Homeomorph.setCongr hr).trans eg.symm)
  have he : ∀ x, g.toFun (e x) = f.toFun x := by
    intro x
    exact congrArg Subtype.val (eg.apply_symm_apply ((Homeomorph.setCongr hr) (ef x)))
  have hei : ∀ y, f.toFun (e.symm y) = g.toFun y := by
    intro y
    simpa only [e.apply_symm_apply] using (he (e.symm y)).symm
  have hs : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ e := by
    apply (ContMDiff.iff_comp_isImmersion g.smoothEmbedding.isImmersion).mpr
    refine ⟨e.continuous, ?_⟩
    have hf : g.toFun ∘ e = f.toFun := funext he
    rw [hf]
    exact f.smoothEmbedding.contMDiff
  have hsi : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ e.symm := by
    apply (ContMDiff.iff_comp_isImmersion f.smoothEmbedding.isImmersion).mpr
    refine ⟨e.symm.continuous, ?_⟩
    have hf : f.toFun ∘ e.symm = g.toFun := funext hei
    rw [hf]
    exact g.smoothEmbedding.contMDiff
  exact ⟨{ e.toEquiv with contMDiff_toFun := hs, contMDiff_invFun := hsi }, he⟩

theorem ambient_image_to_normal_reparam (f g : NeatEmbedding S M)
    (h : SmoothAmbientIsotopy.Rel f.image g.image) :
    Nonempty (ReparametrizedNormalIsotopy S M f g) := by
  obtain ⟨H, hH⟩ := h
  obtain ⟨r, hr⟩ := equal_image_reparam (postcompose f (H.stage 1)) g
    ((postcompose_image f (H.stage 1)).trans hH)
  refine ⟨{
    stage := fun t => postcompose f (H.stage t)
    smooth_family := H.smooth_family.comp
      (contMDiff_fst.prodMk (f.smoothEmbedding.contMDiff.comp contMDiff_snd))
    initial := funext (fun x => H.initial (f.toFun x))
    reparametrization := r
    final := funext (fun x => (hr x).symm) }⟩

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
