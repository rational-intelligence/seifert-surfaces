import CurveComplexGenusTwo.Foundations.SourceNonseparating
import CurveComplexGenusTwo.Foundations.FullSubcomplex
import CurveComplexGenusTwo.Foundations.RealizationCW

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex

/-- Separating means some representative has disconnected complement. -/
def IsSeparatingVertex (S : Type) [TopologicalSpace S] (v : Vertex S) : Prop :=
  ∃ c : EssentialCurve S, Quotient.mk (essentialCurveSetoid S) c = v ∧
    ¬ IsConnected c.val.imageᶜ

def NonseparatingLocus (S : Type) [TopologicalSpace S] :
    Set (curveComplexRealization S 1) :=
  {x | ∀ v, IsSeparatingVertex S v → x.weight v = 0}

theorem separatingVertex_iff_not_nonseparatingVertex
    (S : Type) [TopologicalSpace S] (v : Vertex S) :
    IsSeparatingVertex S v ↔ ¬ nonseparatingVertex v := by
  induction v using Quotient.inductionOn with
  | _ c =>
    constructor
    · rintro ⟨d, hd, hdisc⟩ hconn
      have hrel : (essentialCurveSetoid S).r d c := Quotient.exact hd
      exact hdisc ((nonseparating_isotopy_invariant hrel).mpr hconn)
    · intro hdisc
      exact ⟨c, rfl, hdisc⟩

theorem nonseparatingLocus_eq_fullSupportLocus
    (S : Type) [TopologicalSpace S] :
    NonseparatingLocus S = fullSupportLocus (curveComplex S 1)
      (fun v => nonseparatingVertex v) := by
  ext x
  simp only [NonseparatingLocus, fullSupportLocus, Set.mem_ofPred_eq,
    separatingVertex_iff_not_nonseparatingVertex]

theorem nonseparatingComplex_eq_fullSubcomplex
    (S : Type) [TopologicalSpace S] :
    nonseparatingComplex S = @fullSubcomplex (Vertex S) (Classical.decEq _)
      (curveComplex S 1) (fun v => nonseparatingVertex v) := by
  classical
  apply AbstractSimplicialComplex.ext
  ext σ
  simp [nonseparatingComplex, fullSubcomplex, curveComplex, Finset.mem_image]

/-- The genuine nonseparating complex realization is the source support-zero
locus, with its ambient subspace topology. -/
noncomputable def nonseparatingRealizationHomeomorph
    (S : Type) [TopologicalSpace S] :
    RealizationPoint (nonseparatingComplex S) ≃ₜ NonseparatingLocus S := by
  classical
  rw [nonseparatingComplex_eq_fullSubcomplex,
    nonseparatingLocus_eq_fullSupportLocus]
  exact @fullSubcomplexHomeomorphSupported (Vertex S) (Classical.decEq _)
    (curveComplex S 1) (fun v => nonseparatingVertex v)

/-- CW structure for the actual nonseparating complex, without finiteness. -/
theorem nonseparatingRealization_cw
    (S : Type) [TopologicalSpace S] :
    Nonempty (Topology.CWComplex
      (Set.univ : Set (RealizationPoint (nonseparatingComplex S)))) :=
  ⟨inferInstance⟩

end CurveComplexGenusTwo.SourceTopology

#print axioms CurveComplexGenusTwo.SourceTopology.separatingVertex_iff_not_nonseparatingVertex
#print axioms CurveComplexGenusTwo.SourceTopology.nonseparatingRealizationHomeomorph
#print axioms CurveComplexGenusTwo.SourceTopology.nonseparatingRealization_cw
