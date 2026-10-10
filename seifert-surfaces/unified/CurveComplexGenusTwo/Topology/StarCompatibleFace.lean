import CurveComplexGenusTwo.Topology.StarSubcomplexTopology

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

variable {V : Type*} [DecidableEq V]

/-- The largest part of a finite face whose vertices can occur with nonzero
weight in the realized star of `v`. -/
def compatiblePart (intersect : V → V → ℕ)
    (v : V) (σ : Finset V) : Finset V :=
  σ.filter (fun w => w = v ∨
    (intersect v w ≤ 1 ∧ intersect w v ≤ 1))

theorem compatiblePart_subset (intersect : V → V → ℕ)
    (v : V) (σ : Finset V) :
    compatiblePart intersect v σ ⊆ σ := Finset.filter_subset _ _

theorem compatiblePart_closedStarFace
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (σ : Finset V) (hσ : σ ∈ K.faces)
    (hcurve : ∀ τ : Finset V, τ ∈ K.faces → CurveFace intersect 1 τ) :
    ClosedStarFace intersect v (compatiblePart intersect v σ) := by
  have hc := hcurve σ hσ
  intro a ha b hb hab
  have ha' := Finset.mem_insert.mp ha
  have hb' := Finset.mem_insert.mp hb
  rcases ha' with hav | ha
  · subst a
    rcases hb' with hbv | hb
    · exact False.elim (hab hbv.symm)
    · obtain ⟨_, hcomp⟩ := Finset.mem_filter.mp hb
      rcases hcomp with hbv | hcompat
      · subst b
        exact False.elim (hab rfl)
      · exact hcompat.1
  · rcases hb' with hbv | hb
    · subst b
      obtain ⟨_, hcomp⟩ := Finset.mem_filter.mp ha
      rcases hcomp with hav | hcompat
      · subst a
        exact False.elim (hab rfl)
      · exact hcompat.2
    · exact hc (Finset.mem_filter.mp ha).1
        (Finset.mem_filter.mp hb).1 hab

/-- A star point supported on an ambient face is supported on its compatible
part. No fullness hypothesis is needed for this direction. -/
theorem closedStar_support_compatiblePart
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (σ : Finset V) (x : RealizationPoint K)
    (hstar : x ∈ ClosedStarLocus K intersect v)
    (hσ : ∀ w ∉ σ, x.weight w = 0) :
    ∀ w ∉ compatiblePart intersect v σ, x.weight w = 0 := by
  intro w hw
  by_cases hmem : w ∈ σ
  · by_contra hn
    have hwv : w ≠ v := by
      intro he
      apply hw
      exact Finset.mem_filter.mpr ⟨hmem, Or.inl he⟩
    have hcomp := closedStar_nonzero_coordinate_compatible
      K intersect v x hstar w hwv hn
    exact hw (Finset.mem_filter.mpr ⟨hmem, Or.inr hcomp⟩)
  · exact hσ w hmem

end CurveComplexGenusTwo.Topology
