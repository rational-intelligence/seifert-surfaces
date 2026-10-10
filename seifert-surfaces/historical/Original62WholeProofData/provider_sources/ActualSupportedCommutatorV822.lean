import ActualPlanarWholeEmbeddingExtensionV759
import ActualDiskFixedPlanarIsotopyV757

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
noncomputable section
namespace CompressionActualSupportedCommutatorV822

variable {X : Type*} [TopologicalSpace X]

/-- Localize a homeomorphism by a supported conjugating contraction. -/
def localize (H g : X ≃ₜ X) : X ≃ₜ X :=
  g.trans (H.symm.trans (g.symm.trans H))

lemma localize_apply (H g : X ≃ₜ X) (x : X) :
    localize H g x = H (g.symm (H.symm (g x))) := rfl

lemma localize_eq (H g : X ≃ₜ X) {C B : Set X}
    (hfix : EqOn H id C) (hcontract : MapsTo g B C) :
    EqOn (localize H g) H B := by
  intro x hx
  have hf : H.symm (g x) = g x := H.injective (by simp [hfix (hcontract hx)])
  rw [localize_apply,hf,g.symm_apply_apply]

lemma localize_fixed_outside (H g : X ≃ₜ X) {S : Set X}
    (hgoff : EqOn g id Sᶜ) :
    EqOn (localize H g) id (S ∪ H '' S)ᶜ := by
  intro x hx
  have hxS : x ∉ S := fun hs => hx (Or.inl hs)
  have hxHS : H.symm x ∉ S := by
    intro hs
    exact hx (Or.inr ⟨H.symm x,hs,H.apply_symm_apply x⟩)
  have hginv : g.symm (H.symm x) = H.symm x :=
    g.injective (by simp [hgoff hxHS])
  rw [localize_apply,hgoff hxS]
  change H (g.symm (H.symm x)) = x
  rw [hginv,H.apply_symm_apply]

lemma localize_refl (H : X ≃ₜ X) (x : X) : localize H (Homeomorph.refl X) x = x := by
  simp [localize,Homeomorph.trans_apply]

/-- The whole time family has the same exact support bound. -/
theorem localize_family {Y : Type*} [TopologicalSpace Y]
    (H : X ≃ₜ X) (g : Y → X ≃ₜ X)
    (hg : Continuous (fun p : Y × X => g p.1 p.2))
    (hgi : Continuous (fun p : Y × X => (g p.1).symm p.2)) :
    Continuous (fun p : Y × X => localize H (g p.1) p.2) := by
  exact H.continuous.comp (hgi.comp (continuous_fst.prodMk
    (H.symm.continuous.comp hg)))

#print axioms localize_eq
#print axioms localize_fixed_outside
#print axioms localize_family
end CompressionActualSupportedCommutatorV822
