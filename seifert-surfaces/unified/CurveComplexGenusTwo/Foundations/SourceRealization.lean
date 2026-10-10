import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort
import CurveComplexGenusTwo.Foundations.GenericRealization

/-! Source: curve-complex-genus-two.pdf, Sections 1.1 and 2.4.
The flag complex uses the canonical ambient-isotopy vertex classes and
geometric intersection number. Its realization uses the canonical weak topology.
-/

namespace CurveComplex

/-- The flag complex on all essential curve classes whose pairwise geometric
intersection number is at most `d`. Faces are nonempty finite cliques. -/
noncomputable def curveComplex (S : Type*) [TopologicalSpace S] (d : ℕ) :
    AbstractSimplicialComplex (Vertex S) := by
  classical
  exact {
    faces := {σ | σ.Nonempty ∧
      ∀ α ∈ σ, ∀ β ∈ σ, α ≠ β → geometricIntersection α β ≤ d}
    isRelLowerSet_faces := by
      intro σ hσ
      refine ⟨hσ.1, ?_⟩
      intro τ hτσ hτ
      exact ⟨hτ, fun α hα β hβ hne => hσ.2 α (hτσ hα) β (hτσ hβ) hne⟩
    singleton_mem := by
      intro v
      refine ⟨Finset.singleton_nonempty v, ?_⟩
      intro α hα β hβ hne
      exact (hne ((Finset.mem_singleton.mp hα).trans
        (Finset.mem_singleton.mp hβ).symm)).elim }

theorem curveComplex_mono (S : Type*) [TopologicalSpace S]
    {d e : ℕ} (h : d ≤ e) : curveComplex S d ≤ curveComplex S e := by
  intro σ hσ
  exact ⟨hσ.1, fun α hα β hβ hne => (hσ.2 α hα β hβ hne).trans h⟩

/-- The actual weak geometric realization of the source's flag complex. -/
abbrev curveComplexRealization (S : Type*) [TopologicalSpace S] (d : ℕ) :=
  RealizationPoint (curveComplex S d)

end CurveComplex

#print axioms CurveComplex.curveComplex
#print axioms CurveComplex.curveComplex_mono
#print axioms CurveComplex.curveComplexRealization
#print axioms CurveComplex.realizationTopology
#print axioms CurveComplex.faceInclusion
