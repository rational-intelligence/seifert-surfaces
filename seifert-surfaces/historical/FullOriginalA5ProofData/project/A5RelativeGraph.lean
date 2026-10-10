import A5RelativeC1Inverse
import SectorPieces

set_option autoImplicit false
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations

/-- Once the actual projection inverse is continuous, every native piece is
C1 over its actual curved projected region. Unique within derivatives on that
region are derived from the transverse projection, not supplied as a premise.
No chart-center, convexity or straight-edge assumption is used. -/
theorem C1_section_of_continuous_projection_inverse
    (S : Set (Euc 2)) (hS : UniqueDiffOn ℝ S)
    (G : Euc 2 → Euc 3) (P : Euc 3 →L[ℝ] Euc 2) (q : Euc 2 → Euc 2)
    (hG : ContDiffOn ℝ 1 G S)
    (hP : ∀ x ∈ S, Function.Bijective (P.comp (fderivWithin ℝ G S x)))
    (hq : ContinuousOn q ((P ∘ G) '' S))
    (hinv : ∀ x ∈ S, q (P (G x)) = x) :
    UniqueDiffOn ℝ ((P ∘ G) '' S) ∧
      ContDiffOn ℝ 1 (G ∘ q) ((P ∘ G) '' S) ∧
      (∀ y ∈ (P ∘ G) '' S, P ((G ∘ q) y) = y) ∧
      (G ∘ q) '' ((P ∘ G) '' S) = G '' S ∧
      ∀ x ∈ S, (fderivWithin ℝ (G ∘ q) ((P ∘ G) '' S) (P (G x))).toLinearMap.range =
        (fderivWithin ℝ G S x).toLinearMap.range := by
  let T := (P ∘ G) '' S
  have hmaps : MapsTo q T S := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [Function.comp_apply, hinv x hx] using hx
  have hsection : ∀ y ∈ T, (P ∘ G) (q y) = y := by
    rintro y ⟨x, hx, rfl⟩
    change P (G (q (P (G x)))) = P (G x)
    rw [hinv x hx]
  have hderiv (x : Euc 2) (hx : x ∈ S) : HasFDerivWithinAt (P ∘ G)
      (P.comp (fderivWithin ℝ G S x)) S x :=
    P.hasFDerivAt.comp_hasFDerivWithinAt x ((hG x hx).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  have hT : UniqueDiffOn ℝ T := by
    rintro y ⟨x, hx, rfl⟩
    exact (hderiv x hx).uniqueDiffWithinAt (hS x hx) (hP x hx).2.denseRange
  have hPg : ContDiffOn ℝ 1 (P ∘ G) S := P.contDiff.comp_contDiffOn hG
  have hPrank : ∀ x ∈ S, Function.Injective (fderivWithin ℝ (P ∘ G) S x) := by
    intro x hx
    rw [(hderiv x hx).fderivWithin (hS x hx)]
    exact (hP x hx).1
  obtain ⟨hqC, hchain⟩ := C1_lift_through_relative_immersion S T hS hT
    (P ∘ G) id q hPg contDiffOn_id hPrank hq hmaps hsection
  refine ⟨hT, hG.comp hqC hmaps, hsection, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨q y, hmaps hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨P (G x), ⟨x, hx, rfl⟩, by change G (q (P (G x))) = G x; rw [hinv x hx]⟩
  · intro x hx
    have hy : P (G x) ∈ T := ⟨x, hx, rfl⟩
    have hc := hchain (P (G x)) hy
    rw [hinv x hx, fderivWithin_id (hT _ hy)] at hc
    have hqin : Function.Injective (fderivWithin ℝ q T (P (G x))) := by
      intro v w hvw
      have hv := congrArg (fun L : Euc 2 →L[ℝ] Euc 2 => L v) hc
      have hw := congrArg (fun L : Euc 2 →L[ℝ] Euc 2 => L w) hc
      exact hv.symm.trans ((congrArg (fderivWithin ℝ (P ∘ G) S x) hvw).trans hw)
    have hqsurj := (LinearMap.injective_iff_surjective
      (f := (fderivWithin ℝ q T (P (G x))).toLinearMap)).mp hqin
    rw [fderivWithin_comp _ ((hG _ (hmaps hy)).differentiableWithinAt (by norm_num))
      ((hqC _ hy).differentiableWithinAt (by norm_num)) hmaps (hT _ hy), hinv x hx]
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨fderivWithin ℝ q T (P (G x)) v, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := hqsurj v
      exact ⟨w, congrArg (fderivWithin ℝ G S x) hw⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
