import A5NearbySpliceV472

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers
universe u v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

abbrev GraphRegular (P : CompactCornerPrism.{u}) (G : P → Time × M) : Prop :=
  ContMDiff PrismModel ((𝓡∂ 1).prod (𝓡∂ 3)) 1 G ∧
    (∀ q, Function.Injective (mfderiv PrismModel ((𝓡∂ 1).prod (𝓡∂ 3)) G q)) ∧
    ContMDiffOn PrismModel ((𝓡∂ 1).prod (𝓡∂ 3)) ∞ G (PrismModel.interior P)

theorem graphRegular_affine {P : CompactCornerPrism.{u}} {G : P → Time × M}
    (w : AffineTimeWindow) (hG : GraphRegular P G) :
    GraphRegular P (affineCylinder w ∘ G) := by
  refine ⟨((affine_graph_smooth w).of_le (by simp)).comp hG.1, ?_,
    (affine_graph_smooth w).comp_contMDiffOn hG.2.2⟩
  intro q
  rw [mfderiv_comp q ((affine_graph_smooth w).mdifferentiableAt (by simp))
    (hG.1.mdifferentiableAt (by simp))]
  exact (affine_graph_rank w _).comp (hG.2.1 q)

def track_of_indexed {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (K : Time × S → M)
    {ι : Type*} [Fintype ι]
    (P : ι → CompactCornerPrism.{u}) (p : ∀ i, C(P i, Time × S))
    (he : ∀ i, IsEmbedding (p i))
    (hc : ∀ z, ∃ i q, p i q = z)
    (hs : ∀ i, GraphRegular (P i) (fun q => ((p i q).1, F.map (p i q).2)))
    (ht : ∀ i, GraphRegular (P i) (fun q => ((p i q).1, K (p i q)))) :
    GeometricTrack F K where
  count := Fintype.card ι
  prism i := P ((Fintype.equivFin ι).symm i)
  parametrization i := p ((Fintype.equivFin ι).symm i)
  embedding i := he ((Fintype.equivFin ι).symm i)
  covers := by
    ext z
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨i, q, hq⟩ := hc z
      refine mem_iUnion.2 ⟨(Fintype.equivFin ι) i, ?_⟩
      change z ∈ Set.range (p ((Fintype.equivFin ι).symm ((Fintype.equivFin ι) i)))
      rw [Equiv.symm_apply_apply]
      exact ⟨q, hq⟩
  source_c1 i := (hs _).1
  source_injective i := (hs _).2.1
  source_smooth_interior i := (hs _).2.2
  target_c1 i := (ht _).1
  target_injective i := (ht _).2.1
  target_smooth_interior i := (ht _).2.2

theorem geometric_splice_track
    {S R Q : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    {d : S → R} (D : GeometricSourceMap F G d)
    (f : Time × S → M) (old : GeometricTrack F f)
    (q : S → Q)
    (hq : ∀ i, ContMDiff CornerModel (𝓡∂ 2) 1 (q ∘ D.parametrization i) ∧
      (∀ x, Function.Injective (mfderiv CornerModel (𝓡∂ 2) (q ∘ D.parametrization i) x)) ∧
      ContMDiffOn CornerModel (𝓡∂ 2) ∞ (q ∘ D.parametrization i)
        (CornerModel.interior (D.domain i)))
    (H : Time × Q → M)
    (hH : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 2)) (𝓡∂ 3) ∞ H)
    (hHr : ∀ t x, Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) (fun x => H (t,x)) x))
    (hjoin : ∀ x, f (1,x) = H (0,q x)) :
    Nonempty (GeometricTrack F (splice f (fun p => H (p.1,q p.2)))) := by
  classical
  let P : Fin old.count ⊕ Fin D.count → CompactCornerPrism.{u} :=
    Sum.elim old.prism (fun i => cornerCylinder (D.domain i))
  let p : ∀ i, C(P i, Time × S) := fun i => match i with
    | Sum.inl j => ⟨affineCylinder firstHalfWindow ∘ old.parametrization j,
        ((affineTime_properties firstHalfWindow).1.continuous.prodMap continuous_id).comp
          (old.parametrization j).continuous⟩
    | Sum.inr j => ⟨fun z => (affineTime secondHalfWindow (z : Time × D.domain j).1,
        D.parametrization j (z : Time × D.domain j).2),
        ((affineTime_properties secondHalfWindow).1.continuous.comp continuous_fst).prodMk
          ((D.parametrization j).continuous.comp continuous_snd)⟩
  have he (i) : IsEmbedding (p i) := by
    cases i with
    | inl j =>
      exact ((affineTime_properties firstHalfWindow).1.prodMap Topology.IsEmbedding.id).comp
        (old.embedding j)
    | inr j =>
      exact (affineTime_properties secondHalfWindow).1.prodMap (D.embedding j)
  have hc (z : Time × S) : ∃ i a, p i a = z := by
    by_cases hz : (z.1 : ℝ) ≤ 1 / 2
    · let s : Time := ⟨2 * (z.1 : ℝ), by constructor <;> linarith [z.1.property.1]⟩
      have hst : affineTime firstHalfWindow s = z.1 := by
        apply Subtype.ext
        dsimp [s, affineTime, firstHalfWindow]
        ring
      have hz' : (s,z.2) ∈ ⋃ i, Set.range (old.parametrization i) := by rw [old.covers]; trivial
      obtain ⟨i,a,ha⟩ := mem_iUnion.1 hz'
      refine ⟨Sum.inl i,a,?_⟩
      change affineCylinder firstHalfWindow (old.parametrization i a) = z
      rw [ha]
      exact Prod.ext hst rfl
    · let s : Time := ⟨2 * (z.1 : ℝ) - 1, by constructor <;> linarith [z.1.property.2]⟩
      have hst : affineTime secondHalfWindow s = z.1 := by
        apply Subtype.ext
        dsimp [s, affineTime, secondHalfWindow]
        ring
      have hz' : z.2 ∈ ⋃ i, Set.range (D.parametrization i) := by rw [D.covers]; trivial
      obtain ⟨i,a,ha⟩ := mem_iUnion.1 hz'
      refine ⟨Sum.inr i,(s,a),?_⟩
      exact Prod.ext hst ha
  have hs (i) : GraphRegular (P i) (fun a => ((p i a).1, F.map (p i a).2)) := by
    cases i with
    | inl j =>
      exact graphRegular_affine firstHalfWindow
        ⟨old.source_c1 j, old.source_injective j, old.source_smooth_interior j⟩
    | inr j =>
      exact graphRegular_affine secondHalfWindow
        (cornerCylinder_product_regular (𝓡∂ 3) (D.domain j) (F.map ∘ D.parametrization j)
          (D.source_c1 j) (D.source_injective j) (D.source_smooth_interior j))
  have ht (i) : GraphRegular (P i)
      (fun a => ((p i a).1, splice f (fun p => H (p.1,q p.2)) (p i a))) := by
    cases i with
    | inl j =>
      have heq : (fun a => ((p (Sum.inl j) a).1,
          splice f (fun p => H (p.1,q p.2)) (p (Sum.inl j) a))) =
          affineCylinder firstHalfWindow ∘
            (fun a => ((old.parametrization j a).1, f (old.parametrization j a))) := by
        funext a
        change (affineTime firstHalfWindow (old.parametrization j a).1,
          splice f (fun p => H (p.1,q p.2))
            (affineCylinder firstHalfWindow (old.parametrization j a))) =
          (affineTime firstHalfWindow (old.parametrization j a).1, f (old.parametrization j a))
        congr 1
        change splice f (fun p => H (p.1,q p.2))
          (affineCylinder firstHalfWindow (old.parametrization j a)) = f (old.parametrization j a)
        exact splice_first _ _ _
      rw [heq]
      exact graphRegular_affine firstHalfWindow
        ⟨old.target_c1 j, old.target_injective j, old.target_smooth_interior j⟩
    | inr j =>
      let l : cornerCylinder (D.domain j) → Time × Q := fun a =>
        ((a : Time × D.domain j).1, q (D.parametrization j (a : Time × D.domain j).2))
      have hl := cornerCylinder_product_regular (𝓡∂ 2) (D.domain j)
        (q ∘ D.parametrization j) (hq j).1 (hq j).2.1 (hq j).2.2
      let graph : Time × Q → Time × M := fun b => (b.1,H b)
      have hg : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 2)) ((𝓡∂ 1).prod (𝓡∂ 3)) ∞ graph :=
        contMDiff_fst.prodMk hH
      have hreg : GraphRegular (cornerCylinder (D.domain j)) (graph ∘ l) := by
        refine ⟨(hg.of_le (by simp)).comp hl.1, ?_, hg.comp_contMDiffOn hl.2.2⟩
        intro a
        have hlc : ContMDiff PrismModel ((𝓡∂ 1).prod (𝓡∂ 2)) 1 l := hl.1
        rw [mfderiv_comp a (f := l) (g := graph) (hg.mdifferentiableAt (by simp))
          (hlc.mdifferentiableAt (by simp))]
        exact (smooth_family_graph_rank H (hH.of_le (by simp)) hHr _).comp (hl.2.1 a)
      have heq : (fun a => ((p (Sum.inr j) a).1,
          splice f (fun p => H (p.1,q p.2)) (p (Sum.inr j) a))) =
          affineCylinder secondHalfWindow ∘ (graph ∘ l) := by
        funext a
        exact Prod.ext rfl (splice_second f (fun p => H (p.1,q p.2)) hjoin
          ((a : Time × D.domain j).1, D.parametrization j (a : Time × D.domain j).2))
      rw [heq]
      exact graphRegular_affine secondHalfWindow hreg
  exact ⟨track_of_indexed F _ P p he hc hs ht⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
