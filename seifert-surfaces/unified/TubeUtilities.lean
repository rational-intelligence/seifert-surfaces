import LinkExterior

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers
open Foundations
noncomputable section

def tubeImageOpen {K : OrientedKnot} (T : TubularNeighborhood K) :
    TopologicalSpace.Opens ThreeSphere := ⟨Set.range (T.tube 0), T.image_open 0⟩

theorem tube_image_diffeomorph_exists {K : OrientedKnot} (T : TubularNeighborhood K) :
    ∃ A : Diffeomorph ((𝓡 1).prod 𝓘(ℝ, Euc 2)) (𝓡 3) TubeDomain (tubeImageOpen T) ∞,
      ∀ p, (A p : ThreeSphere) = T.tube 0 p := by
  let e : TubeDomain ≃ tubeImageOpen T :=
    Equiv.ofInjective (T.tube 0) (T.smoothEmbedding 0).isEmbedding.injective
  have hforward : ContMDiff ((𝓡 1).prod 𝓘(ℝ, Euc 2)) (𝓡 3) ∞
      (e : TubeDomain → tubeImageOpen T) := by
    apply (ContMDiff.subtypeVal_comp_iff (tubeImageOpen T) _).mp
    exact (T.smoothEmbedding 0).contMDiff
  have hcontinuous : Continuous (e.symm : tubeImageOpen T → TubeDomain) := by
    apply (T.smoothEmbedding 0).isEmbedding.isInducing.continuous_iff.mpr
    have heq : T.tube 0 ∘ e.symm = (Subtype.val : tubeImageOpen T → ThreeSphere) := by
      funext x
      exact congrArg Subtype.val (e.apply_symm_apply x)
    rw [heq]
    exact continuous_subtype_val
  have hbackward : ContMDiff (𝓡 3) ((𝓡 1).prod 𝓘(ℝ, Euc 2)) ∞
      (e.symm : tubeImageOpen T → TubeDomain) := by
    apply (ContMDiff.iff_comp_isImmersion (T.smoothEmbedding 0).isImmersion).mpr
    refine ⟨hcontinuous, ?_⟩
    have heq : T.tube 0 ∘ e.symm = (Subtype.val : tubeImageOpen T → ThreeSphere) := by
      funext x
      exact congrArg Subtype.val (e.apply_symm_apply x)
    rw [heq]
    exact contMDiff_subtype_val
  exact ⟨{ toEquiv := e, contMDiff_toFun := hforward, contMDiff_invFun := hbackward },
    fun _ => rfl⟩

end
end SeifertSurfaces.LongitudeProducers
