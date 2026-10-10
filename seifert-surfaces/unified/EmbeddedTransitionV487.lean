import NativeWithinV487

noncomputable section
open Set Topology Function MeasureTheory Metric Filter IsManifold
open scoped Manifold Topology ENNReal

namespace SeifertSurfaces.OriginalEndpoints.Section5.NativeAreaV487

variable {E M : Type*} [TopologicalSpace E] [Nonempty E] [TopologicalSpace M]
  {f g : E → M} {s t : Set E}

/-- The actual inverse transition of two embedded pieces of the same image. -/
theorem embedded_transition (hf : ContinuousOn f s)
    (hg : IsEmbedding (t.domRestrict g)) (hf_inj : InjOn f s)
    (himage : f '' s = g '' t) :
    let τ := (invFunOn g t) ∘ f
    MapsTo τ s t ∧ EqOn (g ∘ τ) f s ∧ ContinuousOn τ s ∧
      InjOn τ s ∧ τ '' s = t := by
  classical
  let τ := (invFunOn g t) ∘ f
  have hτt : MapsTo τ s t := by
    intro x hx
    exact (surjOn_image g t).mapsTo_invFunOn (himage ▸ mem_image_of_mem f hx)
  have hτeq : EqOn (g ∘ τ) f s := by
    intro x hx
    exact (surjOn_image g t).rightInvOn_invFunOn (himage ▸ mem_image_of_mem f hx)
  let q : s → t := fun x => ⟨τ x, hτt x.property⟩
  have hq : Continuous q := by
    apply hg.isInducing.continuous_iff.mpr
    have he : (t.domRestrict g) ∘ q = s.domRestrict f := by
      funext x
      exact hτeq x.property
    rw [he]
    exact continuousOn_iff_continuous_domRestrict.mp hf
  have hτcont : ContinuousOn τ s := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact continuous_subtype_val.comp hq
  have hτinj : InjOn τ s := by
    intro x hx y hy hxy
    apply hf_inj hx hy
    calc
      f x = g (τ x) := (hτeq hx).symm
      _ = g (τ y) := congrArg g hxy
      _ = f y := hτeq hy
  refine ⟨hτt, hτeq, hτcont, hτinj, ?_⟩
  apply Subset.antisymm (image_subset_iff.mpr hτt)
  intro y hy
  obtain ⟨x, hx, hxy⟩ := (himage.symm ▸ mem_image_of_mem g hy)
  refine ⟨x, hx, ?_⟩
  have hsub : (⟨τ x, hτt hx⟩ : t) = ⟨y, hy⟩ := hg.injective ((hτeq hx).trans hxy)
  exact congrArg Subtype.val hsub

end SeifertSurfaces.OriginalEndpoints.Section5.NativeAreaV487
