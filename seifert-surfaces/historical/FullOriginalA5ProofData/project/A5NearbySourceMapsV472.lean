import A5GeometricCornerLift
import A5SameImageClassTransport

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- Recover regularity of the literal lift of an actual corner image map. -/
theorem lifted_corner_regular {R : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding R E.Carrier) (P : CompactCornerPiece.{u})
    (q : P → R) (hq : Continuous q)
    (hc : ContMDiff CornerModel (𝓡∂ 3) 1 (f.toFun ∘ q))
    (hr : ∀ x, Function.Injective (mfderiv CornerModel (𝓡∂ 3) (f.toFun ∘ q) x))
    (hs : ContMDiffOn CornerModel (𝓡∂ 3) ∞ (f.toFun ∘ q) (CornerModel.interior P)) :
    ContMDiff CornerModel (𝓡∂ 2) 1 q ∧
    (∀ x, Function.Injective (mfderiv CornerModel (𝓡∂ 2) q x)) ∧
    ContMDiffOn CornerModel (𝓡∂ 2) ∞ q (CornerModel.interior P) := by
  have hqs : ContMDiff CornerModel (𝓡∂ 2) 1 q := fun x =>
    proper_smooth_embedding_lift_contMDiffAt CornerModel f q x hq.continuousAt
      1 (by simp) (hc x)
  refine ⟨hqs, ?_, ?_⟩
  · intro x
    have hi := hr x
    rw [mfderiv_comp x (f.smooth.mdifferentiable (by simp) _)
      (hqs.mdifferentiable (by simp) x)] at hi
    exact Function.Injective.of_comp hi
  · intro x hx
    have ho : IsOpen (CornerModel.interior P) := CornerModel.isOpen_interior (n := ∞) (by simp)
    exact (proper_smooth_embedding_lift_contMDiffAt CornerModel f q x hq.continuousAt
      ∞ le_rfl (hs.contMDiffAt (ho.mem_nhds hx))).contMDiffWithinAt

/-- The original corner cover remains valid after changing only its smooth target embedding. -/
def forward_source_map {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime)
    (e : S ≃ₜ R) (D : GeometricSourceMap F Fprime e)
    (h : ProperSmoothEmbedding Q.source E.Carrier)
    (C : GeometricPiecewiseSurface Q.source E.Carrier)
    (hC : C.map = h.continuousMap) :
    GeometricSourceMap F C (e.trans Q.homeomorph.symm) where
  count := D.count
  domain := D.domain
  parametrization := D.parametrization
  embedding := D.embedding
  covers := D.covers
  source_c1 := D.source_c1
  source_injective := D.source_injective
  source_smooth_interior := D.source_smooth_interior
  target_c1 := by
    intro i
    rw [hC]
    exact (h.smooth.of_le (by simp)).comp
      (geometric_corner_lift_to_smooth_source E F Fprime Q e e.continuous D i).1
  target_injective := by
    intro i x
    rw [hC]
    change Function.Injective (mfderiv CornerModel (𝓡∂ 3)
      (h.toFun ∘ (Q.homeomorph.symm ∘ e ∘ D.parametrization i)) x)
    rw [mfderiv_comp x (h.smooth.mdifferentiable (by simp) _)
      ((geometric_corner_lift_to_smooth_source E F Fprime Q e e.continuous D i).1.mdifferentiable
        (by simp) x)]
    exact (h.differential_injective _).comp
      ((geometric_corner_lift_to_smooth_source E F Fprime Q e e.continuous D i).2.1 x)
  target_smooth_interior := by
    intro i
    rw [hC]
    exact h.smooth.comp_contMDiffOn
      (geometric_corner_lift_to_smooth_source E F Fprime Q e e.continuous D i).2.2

/-- The reverse cover is transported by the reconstruction homeomorphism. -/
def backward_source_map {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime)
    (e : S ≃ₜ R) (D : GeometricSourceMap Fprime F e.symm)
    (h : ProperSmoothEmbedding Q.source E.Carrier)
    (C : GeometricPiecewiseSurface Q.source E.Carrier)
    (hC : C.map = h.continuousMap) :
    GeometricSourceMap C F (e.trans Q.homeomorph.symm).symm := by
  have heq (i : Fin D.count) :
      Q.embedding.toFun ∘ (Q.homeomorph.symm ∘ D.parametrization i) =
        Fprime.map ∘ D.parametrization i := by
    funext x
    simp [Function.comp_def, Q.pointwise_same_map]
  have hreg (i : Fin D.count) := lifted_corner_regular E Q.embedding (D.domain i)
    (Q.homeomorph.symm ∘ D.parametrization i)
    (Q.homeomorph.symm.continuous.comp (D.parametrization i).continuous)
    (by rw [heq]; exact D.source_c1 i)
    (by rw [heq]; exact D.source_injective i)
    (by rw [heq]; exact D.source_smooth_interior i)
  refine {
    count := D.count
    domain := D.domain
    parametrization := fun i => ⟨Q.homeomorph.symm ∘ D.parametrization i,
      Q.homeomorph.symm.continuous.comp (D.parametrization i).continuous⟩
    embedding := fun i => Q.homeomorph.symm.isEmbedding.comp (D.embedding i)
    covers := ?_
    source_c1 := ?_
    source_injective := ?_
    source_smooth_interior := ?_
    target_c1 := ?_
    target_injective := ?_
    target_smooth_interior := ?_ }
  · ext x
    constructor
    · intro _; trivial
    · intro _
      have hx : Q.homeomorph x ∈ ⋃ i, Set.range (D.parametrization i) := by rw [D.covers]; trivial
      obtain ⟨i, z, hz⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨i, z, by simpa using congrArg Q.homeomorph.symm hz⟩
  · intro i
    rw [hC]
    exact (h.smooth.of_le (by simp)).comp (hreg i).1
  · intro i x
    rw [hC]
    change Function.Injective (mfderiv CornerModel (𝓡∂ 3)
      (h.toFun ∘ (Q.homeomorph.symm ∘ D.parametrization i)) x)
    rw [mfderiv_comp x (h.smooth.mdifferentiable (by simp) _)
      ((hreg i).1.mdifferentiable (by simp) x)]
    exact (h.differential_injective _).comp ((hreg i).2.1 x)
  · intro i
    rw [hC]
    exact h.smooth.comp_contMDiffOn (hreg i).2.2
  · intro i
    convert D.target_c1 i using 1
    funext x
    simp [Function.comp_def]
  · intro i x
    have heq2 : (fun z => F.map (e.symm (Q.homeomorph (Q.homeomorph.symm (D.parametrization i z))))) =
        (fun z => F.map (e.symm (D.parametrization i z))) := by
      funext z; simp
    change Function.Injective (mfderiv CornerModel (𝓡∂ 3)
      (fun z => F.map (e.symm (Q.homeomorph (Q.homeomorph.symm (D.parametrization i z))))) x)
    rw [heq2]
    exact D.target_injective i x
  · intro i
    convert D.target_smooth_interior i using 1
    funext x
    simp [Function.comp_def]

def endpoint_source_homeomorph {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime)
    (d : GeometricSourceHomeomorph F Fprime)
    (h : ProperSmoothEmbedding Q.source E.Carrier)
    (C : GeometricPiecewiseSurface Q.source E.Carrier)
    (hC : C.map = h.continuousMap) : GeometricSourceHomeomorph F C where
  homeomorph := d.homeomorph.trans Q.homeomorph.symm
  forward := forward_source_map E F Fprime Q d.homeomorph d.forward h C hC
  backward := backward_source_map E F Fprime Q d.homeomorph d.backward h C hC
  boundary_image := by
    change (Q.homeomorph.symm ∘ d.homeomorph) '' S.boundary = Q.source.boundary
    rw [Set.image_comp, d.boundary_image]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← Q.boundary_transport] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simpa only [Q.homeomorph.symm_apply_apply] using hz
    · intro hx
      refine ⟨Q.homeomorph x, ?_, Q.homeomorph.symm_apply_apply x⟩
      rw [← Q.boundary_transport]
      exact ⟨x, hx, rfl⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
