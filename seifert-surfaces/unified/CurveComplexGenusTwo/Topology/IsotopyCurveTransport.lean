import CurveComplexGenusTwo.Foundations.Definitions

namespace CurveComplex

theorem position_essential_curve_of_isotopy
    {S : Type*} [TopologicalSpace S]
    (H : AmbientIsotopy S) (c : EssentialCurve S) :
    ∃ d : EssentialCurve S,
      d.val.image = H.finalMap '' c.val.image ∧
      Quotient.mk (essentialCurveSetoid S) d =
        Quotient.mk (essentialCurveSetoid S) c := by
  obtain ⟨e, he⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
  have hfinal (x : S) : e x = H.finalMap x := he x
  let d₀ : Curve S := ⟨e ∘ c.val.map, e.isEmbedding.comp c.val.embedded⟩
  have himage : d₀.image = H.finalMap '' c.val.image := by
    change Set.range (e ∘ c.val.map) = H.finalMap '' Set.range c.val.map
    rw [Set.range_comp]
    exact Set.image_congr (fun x _ => hfinal x)
  have hrel : (curveSetoid S).r c.val d₀ := ⟨H, himage.symm⟩
  let d : EssentialCurve S := ⟨d₀, (essential_isotopy_invariant hrel).mp c.property⟩
  refine ⟨d, himage, ?_⟩
  exact (Quotient.sound (s := essentialCurveSetoid S) (a := c) (b := d) hrel).symm

#print axioms position_essential_curve_of_isotopy

end CurveComplex
