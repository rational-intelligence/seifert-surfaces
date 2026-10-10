import A5HalfballDomainsV466
import A5SignedOrientationProducerV466

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
universe u

/-- Finite signed refinement package. The sign compatibility predicate is the exact
remaining topological input; all compactness and half-ball bookkeeping is discharged here. -/
theorem a5_signed_finite_refinement
    (S : A5CompactSmoothCarrier.{u})
    (U : S → Set S) (hUopen : ∀ p, IsOpen (U p)) (hUp : ∀ p, p ∈ U p)
    (hUsub : ∀ p, U p ⊆ (extChartAt (𝓡∂ 2) p).source)
    (σ : S → ℝ)
    (hσunit : ∀ x, σ x = 1 ∨ σ x = -1)
    (hσoverlap : ∀ p q x,
      x ∈ U p → x ∈ U q →
      0 < σ q * σ p * (a5TransitionJacobian S p q x).det) :
    Nonempty (A5SignedFiniteChartCover S) := by
  classical
  obtain ⟨centers, hcenters⟩ := (isCompact_univ : IsCompact (univ : Set S)).elim_finite_subcover
    (fun p => U p) (fun p => hUopen p) (by intro p _; exact mem_iUnion.mpr ⟨p,hUp p⟩)
  let n := centers.card
  let center : Fin n → S := fun i => ((centers.equivFin).symm i).val
  let domain : Fin n → Set S := fun i => U (center i)
  let sign : Fin n → ℝ := fun i => σ (center i)
  have hcover : (⋃ i, domain i) = (univ : Set S) := by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨p,hpx⟩ := mem_iUnion.mp (hcenters (mem_univ x))
    obtain ⟨hp,hpx⟩ := mem_iUnion.mp hpx
    refine mem_iUnion.mpr ⟨centers.equivFin ⟨p,hp⟩,?_⟩
    simpa [domain,center] using hpx
  have hdomain_open : ∀ i, IsOpen (domain i) := fun i => hUopen (center i)
  have hdomain_subset : ∀ i, domain i ⊆ (extChartAt (𝓡∂ 2) (center i)).source :=
    fun i => hUsub (center i)
  have hsign_unit : ∀ i, sign i = 1 ∨ sign i = -1 := fun i => hσunit _
  have hpositive : ∀ i j x, x ∈ domain i → x ∈ domain j →
      0 < sign j * sign i * (a5TransitionJacobian S (center i) (center j) x).det := by
    intro i j x hi hj
    exact hσoverlap _ _ x hi hj
  exact ⟨{
    count := n
    center := center
    domain := domain
    domain_open := hdomain_open
    domain_subset := hdomain_subset
    covers := hcover
    sign := sign
    sign_unit := hsign_unit
    positive_transition := hpositive}⟩

#print axioms a5_signed_finite_refinement
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
