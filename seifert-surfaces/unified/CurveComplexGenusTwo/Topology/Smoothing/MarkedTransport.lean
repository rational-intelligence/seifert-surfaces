import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Maximal connected components of a complement are carried by a homeomorphism. -/
theorem complementComponent_image (h : S ≃ₜ S) {A U : Set S}
    (hU : IsComplementComponent A U) :
    IsComplementComponent (h '' A) (h '' U) := by
  rcases hU with ⟨hne, hconn, hsub, hmax⟩
  refine ⟨hne.image h, hconn.image h h.continuous.continuousOn, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    exact hsub hx (h.injective heq ▸ hy)
  · intro V hV hUV hVA
    have hUV' : U ⊆ h.symm '' V := by
      intro x hx
      exact ⟨h x, hUV ⟨x, hx, rfl⟩, h.symm_apply_apply x⟩
    have hVA' : h.symm '' V ⊆ Aᶜ := by
      rintro _ ⟨x, hx, rfl⟩ ha
      exact hVA hx ⟨h.symm x, ha, h.apply_symm_apply x⟩
    have hEq := hmax (h.symm '' V) (hV.image h.symm h.symm.continuous.continuousOn)
      hUV' hVA'
    calc
      V = h '' (h.symm '' V) := by
        ext x
        simp only [Set.mem_image]
        constructor
        · intro hx; exact ⟨h.symm x, ⟨x, hx, rfl⟩, h.apply_symm_apply x⟩
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
      _ = h '' U := congrArg (fun W : Set S => h '' W) hEq

/-- Transport retains the interval parametrization and ordered marked endpoints. -/
def MarkedArc.transport {M : HyperellipticModel E S} (a : MarkedArc M)
    (h : S ≃ₜ S) (hfix : ∀ b, b ∈ M.cover.branch → h b = b) : MarkedArc M where
  map := h ∘ a.map
  continuous := h.continuous.comp a.continuous
  injective_except_loop_closure := fun t u heq =>
    a.injective_except_loop_closure t u (h.injective heq)
  start_marked := by simpa only [Function.comp_apply, hfix _ a.start_marked] using a.start_marked
  end_marked := by simpa only [Function.comp_apply, hfix _ a.end_marked] using a.end_marked
  marked_only_at_ends := by
    intro t ht
    have heq : h (a.map t) = a.map t :=
      h.injective (hfix _ ht)
    exact a.marked_only_at_ends t (heq ▸ ht)

@[simp] theorem MarkedArc.transport_image {M : HyperellipticModel E S}
    (a : MarkedArc M) (h : S ≃ₜ S) (hfix : ∀ b, b ∈ M.cover.branch → h b = b) :
    (a.transport h hfix).image = h '' a.image := by
  exact Set.range_comp h a.map

/-- Essentiality is preserved, including the component condition for loops. -/
theorem essential_transport {M : HyperellipticModel E S}
    (a : EssentialMarkedArc M) (h : S ≃ₜ S)
    (hfix : ∀ b, b ∈ M.cover.branch → h b = b) :
    IsEssentialMarkedArc M (a.val.transport h hfix) := by
  rcases a.property with hn | hl
  · left
    exact fun heq => hn (h.injective heq)
  · right
    intro U hU
    rw [MarkedArc.transport_image] at hU
    have hcomp := complementComponent_image h.symm hU
    have hback : h.symm '' (h '' a.val.image) = a.val.image := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
      · intro hx; exact ⟨h x, ⟨x, hx, rfl⟩, h.symm_apply_apply x⟩
    rw [hback] at hcomp
    obtain ⟨b, hb, hbU⟩ := hl (h.symm '' U) hcomp
    refine ⟨b, hb, ?_⟩
    obtain ⟨x, hx, heq⟩ := hbU
    have heq' : x = b := by
      calc
        x = h (h.symm x) := (h.apply_symm_apply x).symm
        _ = h b := congrArg h heq
        _ = b := hfix b hb
    exact heq' ▸ hx

def EssentialMarkedArc.transport {M : HyperellipticModel E S}
    (a : EssentialMarkedArc M) (h : S ≃ₜ S)
    (hfix : ∀ b, b ∈ M.cover.branch → h b = b) : EssentialMarkedArc M :=
  ⟨a.val.transport h hfix, essential_transport a h hfix⟩

/-- Removing fixed marked points commutes with transport. -/
theorem arcInterior_transport {M : HyperellipticModel E S}
    (a : EssentialMarkedArc M) (h : S ≃ₜ S)
    (hfix : ∀ b, b ∈ M.cover.branch → h b = b) :
    arcInterior M (a.transport h hfix) = h '' arcInterior M a := by
  change (a.val.transport h hfix).image \ (M.cover.branch : Set S) =
    h '' (a.val.image \ (M.cover.branch : Set S))
  rw [MarkedArc.transport_image]
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hn⟩
    exact ⟨y, ⟨hy, fun hb => hn (by simpa only [hfix y hb] using hb)⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hn⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    intro hb
    have heq : h y = y := h.injective (hfix (h y) hb)
    exact hn (heq ▸ hb)

theorem arcInterior_transport_disjoint {M : HyperellipticModel E S}
    (a b : EssentialMarkedArc M) (h : S ≃ₜ S)
    (hfix : ∀ x, x ∈ M.cover.branch → h x = x)
    (hd : Disjoint (arcInterior M a) (arcInterior M b)) :
    Disjoint (arcInterior M (a.transport h hfix))
      (arcInterior M (b.transport h hfix)) := by
  rw [arcInterior_transport, arcInterior_transport]
  exact (Set.disjoint_image_iff h.injective).mpr hd

#print axioms essential_transport
#print axioms arcInterior_transport_disjoint
end CurveComplex.HyperellipticModel
