import CurveComplexGenusTwo.Foundations.SourceRealization

/-! Source: curve-complex-genus-two.pdf, Sections 1.1 and 2.4. -/

namespace CurveComplex

/-- A curve is nonseparating when its complement is connected. -/
def Nonseparating {S : Type*} [TopologicalSpace S] (c : Curve S) : Prop :=
  IsConnected c.imageᶜ

theorem nonseparating_isotopy_invariant {S : Type*} [TopologicalSpace S]
    {a b : EssentialCurve S} (h : (essentialCurveSetoid S).r a b) :
    Nonseparating a.val ↔ Nonseparating b.val := by
  obtain ⟨H, hH⟩ := h
  obtain ⟨e, he⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
  have hefinal : (e : S → S) = H.finalMap := funext he
  have himage : e '' a.val.image = b.val.image := by
    rw [hefinal]
    exact hH
  change IsConnected a.val.imageᶜ ↔ IsConnected b.val.imageᶜ
  rw [← himage, ← e.image_compl]
  exact e.isConnected_image.symm

def nonseparatingVertex {S : Type*} [TopologicalSpace S]
    (α : Vertex S) : Prop :=
  Quotient.liftOn α (fun c : EssentialCurve S => Nonseparating c.val)
    (by
      intro a b h
      exact propext (nonseparating_isotopy_invariant h))

/-- The full subcomplex of `C₁` on nonseparating curve classes. -/
noncomputable def nonseparatingComplex (S : Type*) [TopologicalSpace S] :
    AbstractSimplicialComplex {α : Vertex S // nonseparatingVertex α} := by
  classical
  exact {
    faces := {σ | (σ.image Subtype.val) ∈ (curveComplex S 1).faces}
    isRelLowerSet_faces := by
      intro σ hσ
      refine ⟨Finset.image_nonempty.mp
        ((curveComplex S 1).isRelLowerSet_faces hσ).1, ?_⟩
      intro τ hτσ hτ
      exact ((curveComplex S 1).isRelLowerSet_faces hσ).2
        (Finset.image_subset_image hτσ) (Finset.image_nonempty.mpr hτ)
    singleton_mem := by
      intro v
      change Finset.image Subtype.val {v} ∈ (curveComplex S 1).faces
      simpa only [Finset.image_singleton] using (curveComplex S 1).singleton_mem v.val }

end CurveComplex

#print axioms CurveComplex.Nonseparating
#print axioms CurveComplex.nonseparating_isotopy_invariant
#print axioms CurveComplex.nonseparatingVertex
#print axioms CurveComplex.nonseparatingComplex
