import A5CornerCylinderV472

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- Time in the graph prevents cancellation by the time derivative of a moving embedding. -/
theorem smooth_family_graph_rank {S : CompactOrientedSurface.{u}}
    (f : Time × S → M)
    (hf : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 2)) (𝓡∂ 3) 1 f)
    (hr : ∀ t x, Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) (fun x => f (t,x)) x))
    (p : Time × S) :
    Function.Injective (mfderiv ((𝓡∂ 1).prod (𝓡∂ 2)) ((𝓡∂ 1).prod (𝓡∂ 3))
      (fun q : Time × S => (q.1, f q)) p) := by
  rw [mfderiv_prodMk mdifferentiableAt_fst (hf.mdifferentiableAt (by simp)), mfderiv_fst]
  intro a b hab
  change (a.1, mfderiv ((𝓡∂ 1).prod (𝓡∂ 2)) (𝓡∂ 3) f p a) =
    (b.1, mfderiv ((𝓡∂ 1).prod (𝓡∂ 2)) (𝓡∂ 3) f p b) at hab
  obtain ⟨ht, hsp⟩ := Prod.mk.inj hab
  change mfderiv ((𝓡∂ 1).prod (𝓡∂ 2)) (𝓡∂ 3) f p a =
    mfderiv ((𝓡∂ 1).prod (𝓡∂ 2)) (𝓡∂ 3) f p b at hsp
  rw [mfderiv_prod_eq_add_apply (hf.mdifferentiableAt (by simp)),
    mfderiv_prod_eq_add_apply (hf.mdifferentiableAt (by simp)), ht] at hsp
  exact Prod.ext ht (hr p.1 p.2 (add_left_cancel hsp))

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
