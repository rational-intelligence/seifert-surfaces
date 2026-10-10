import A5NearbyGraphRankV472

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v

/-- C1 and interior smoothness of a product graph use precisely the paid corner regularity. -/
theorem cornerCylinder_product_regular
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {JH : Type*} [TopologicalSpace JH] (J : ModelWithCorners ℝ V JH)
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace JH Y] [IsManifold J ∞ Y]
    (P : CompactCornerPiece.{u}) (f : P → Y)
    (hc : ContMDiff CornerModel J 1 f)
    (hr : ∀ x, Function.Injective (mfderiv CornerModel J f x))
    (hs : ContMDiffOn CornerModel J ∞ f (CornerModel.interior P)) :
    let G := fun q : cornerCylinder P => ((q : Time × P).1, f (q : Time × P).2)
    ContMDiff PrismModel ((𝓡∂ 1).prod J) 1 G ∧
      (∀ q, Function.Injective (mfderiv PrismModel ((𝓡∂ 1).prod J) G q)) ∧
      ContMDiffOn PrismModel ((𝓡∂ 1).prod J) ∞ G
        (PrismModel.interior (cornerCylinder P)) := by
  let j : cornerCylinder P → Time × P := fun q => ((q : Time × P).1, (q : Time × P).2)
  have hj : ContMDiff PrismModel CylinderCornerModel ∞ j := cornerCylinder_projection_smooth P
  have ht : ContMDiff PrismModel (𝓡∂ 1) ∞ (fun q : cornerCylinder P => (q : Time × P).1) :=
    contMDiff_fst.comp hj
  have hp : ContMDiff PrismModel CornerModel ∞ (fun q : cornerCylinder P => (q : Time × P).2) :=
    contMDiff_snd.comp hj
  have hmap : ContMDiff CylinderCornerModel ((𝓡∂ 1).prod J) 1
      (Prod.map (id : Time → Time) f) := contMDiff_id.prodMap hc
  refine ⟨hmap.comp (hj.of_le (by simp)), ?_, ?_⟩
  · intro q
    change Function.Injective (mfderiv PrismModel ((𝓡∂ 1).prod J)
      (Prod.map (id : Time → Time) f ∘ j) q)
    rw [mfderiv_comp q (hmap.mdifferentiableAt (by simp)) (hj.mdifferentiableAt (by simp))]
    apply Function.Injective.comp _ (cornerCylinder_projection_rank P q)
    rw [mfderiv_prodMap mdifferentiableAt_id (hc.mdifferentiableAt (by simp)), mfderiv_id]
    intro a b hab
    change (a.1, mfderiv CornerModel J f (q : Time × P).2 a.2) =
      (b.1, mfderiv CornerModel J f (q : Time × P).2 b.2) at hab
    obtain ⟨htime, hspace⟩ := Prod.mk.inj hab
    exact Prod.ext htime (hr _ hspace)
  · intro q hq
    have hi := cornerCylinder_interior P q hq
    have hs' := hs.contMDiffAt ((CornerModel.isOpen_interior (n := ∞) (by simp)).mem_nhds hi)
    exact ((ht q).prodMk (hs'.comp q (hp q))).contMDiffWithinAt

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
