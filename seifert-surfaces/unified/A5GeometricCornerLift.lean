import A5ProperEmbeddingLiftRegularity
import A5GlobalSmoothSourceV466

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- The actual geometric source morphism supplies regular corner maps into
the reconstructed source. Their regularity is recovered from the original
target image and the smooth embedding, including at corners and boundary. -/
theorem geometric_corner_lift_to_smooth_source
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime)
    (f : S → R) (hf : Continuous f) (D : GeometricSourceMap F Fprime f)
    (i : Fin D.count) :
    let q := Q.homeomorph.symm ∘ f ∘ D.parametrization i
    ContMDiff CornerModel (𝓡∂ 2) 1 q ∧
      (∀ x, Function.Injective (mfderiv CornerModel (𝓡∂ 2) q x)) ∧
      ContMDiffOn CornerModel (𝓡∂ 2) ∞ q (CornerModel.interior (D.domain i)) := by
  let q := Q.homeomorph.symm ∘ f ∘ D.parametrization i
  have hq : Continuous q := Q.homeomorph.symm.continuous.comp (hf.comp (D.parametrization i).continuous)
  have he : Q.embedding.toFun ∘ q = Fprime.map ∘ f ∘ D.parametrization i := by
    funext x
    change Q.embedding.toFun (Q.homeomorph.symm (f (D.parametrization i x))) =
      Fprime.map (f (D.parametrization i x))
    rw [Q.pointwise_same_map, Q.homeomorph.apply_symm_apply]
  have htarget : ContMDiff CornerModel (𝓡∂ 3) 1 (Q.embedding.toFun ∘ q) := by
    rw [he]; exact D.target_c1 i
  have hqs : ContMDiff CornerModel (𝓡∂ 2) 1 q := fun x =>
    proper_smooth_embedding_lift_contMDiffAt CornerModel Q.embedding q x hq.continuousAt
      1 (by simp) (htarget x)
  refine ⟨hqs, ?_, ?_⟩
  · intro x
    have hi : Function.Injective (mfderiv CornerModel (𝓡∂ 3) (Q.embedding.toFun ∘ q) x) := by
      rw [he]; exact D.target_injective i x
    rw [mfderiv_comp x (Q.embedding.smooth.mdifferentiable (by simp) _)
      (hqs.mdifferentiable (by simp) x)] at hi
    exact Function.Injective.of_comp hi
  · intro x hx
    have ho : IsOpen (CornerModel.interior (D.domain i)) :=
      CornerModel.isOpen_interior (n := ∞) (by simp)
    have ht : ContMDiffAt CornerModel (𝓡∂ 3) ∞ (Q.embedding.toFun ∘ q) x := by
      rw [he]
      exact (D.target_smooth_interior i).contMDiffAt (ho.mem_nhds hx)
    exact (proper_smooth_embedding_lift_contMDiffAt CornerModel Q.embedding q x hq.continuousAt
      ∞ le_rfl ht).contMDiffWithinAt

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
