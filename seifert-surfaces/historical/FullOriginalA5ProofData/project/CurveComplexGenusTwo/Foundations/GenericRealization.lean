import Mathlib

/-!
The geometric realization uses the weak topology on an infinite simplicial
complex, not the product topology on all vertex coordinates.
-/

namespace CurveComplex

variable {V : Type*}

/-- Barycentric points with finite support contained in a face. -/
structure RealizationPoint (K : AbstractSimplicialComplex V) where
  weight : V → ℝ
  nonneg : ∀ v, 0 ≤ weight v
  liesInFace : ∃ σ : Finset V, σ ∈ K.faces ∧
    (∀ v ∉ σ, weight v = 0) ∧
    ∑ v ∈ σ, weight v = 1

/-- A closed finite simplex with its Euclidean subspace topology. -/
abbrev FiniteSimplex (σ : Finset V) :=
  {x : (↥σ → ℝ) // (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1}

/-- Inclusion of a finite closed simplex into the realization. -/
noncomputable def faceInclusion
    (K : AbstractSimplicialComplex V) (σ : Finset V)
    (hσ : σ ∈ K.faces) : FiniteSimplex σ → RealizationPoint K := by
  classical
  exact fun x => {
    weight := fun v => if hv : v ∈ σ then x.val ⟨v, hv⟩ else 0
    nonneg := by
      intro v
      split_ifs with hv
      · exact x.property.1 ⟨v, hv⟩
      · exact le_refl 0
    liesInFace := by
      refine ⟨σ, hσ, ?_, ?_⟩
      · intro v hv
        simp [hv]
      · calc
          (∑ v ∈ σ, if hv : v ∈ σ then x.val ⟨v, hv⟩ else 0) =
              ∑ v ∈ σ.attach,
                (if hv : (v : V) ∈ σ then x.val ⟨v, hv⟩ else 0) := by
                rw [← Finset.sum_attach]
          _ = ∑ v : σ, x.val v := by simp [Finset.univ_eq_attach]
          _ = 1 := by simpa [Finset.univ_eq_attach] using x.property.2 }

/-- The weak topology: a set is open precisely when its pullback to every
closed finite simplex is open. This is the final topology for face inclusions. -/
instance realizationTopology
    (K : AbstractSimplicialComplex V) : TopologicalSpace (RealizationPoint K) where
  IsOpen U := ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
    IsOpen ((faceInclusion K σ hσ) ⁻¹' U)
  isOpen_univ := by
    intro σ hσ
    simp
  isOpen_inter := by
    intro U W hU hW σ hσ
    simpa [Set.preimage_inter] using (hU σ hσ).inter (hW σ hσ)
  isOpen_sUnion := by
    intro A hA σ hσ
    simpa [Set.preimage_sUnion, Set.sUnion_eq_biUnion] using
      (isOpen_biUnion (fun U hU => hA U hU σ hσ))

end CurveComplex
