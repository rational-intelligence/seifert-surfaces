import CurveComplexGenusTwo.Topology.FaceCoverAssembly
import CurveComplexGenusTwo.Topology.CurveCombinatorics

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

/-- The union of finite closed faces in the star of a vertex, as a subset of
the actual weak realization. -/
def ClosedStarLocus {V : Type*} [DecidableEq V] (K : AbstractSimplicialComplex V)
    (intersect : V → V → ℕ) (v : V) : Set (RealizationPoint K) :=
  {x | ∃ σ : Finset V, σ ∈ K.faces ∧ ClosedStarFace intersect v σ ∧
    ∀ w ∉ σ, x.weight w = 0}

/-- The realized full subcomplex on nonseparating vertices. -/
def NonseparatingWeightLocus {V : Type*} (K : AbstractSimplicialComplex V)
    (separating : V → Prop) : Set (RealizationPoint K) :=
  {x | ∀ v, separating v → x.weight v = 0}

/-- The face-level core/star covering gives a weak covering by actual
realization subsets. -/
theorem realization_core_stars_weak_cover
    {V : Type*} [DecidableEq V] (K : AbstractSimplicialComplex V)
    (intersect : V → V → ℕ) (separating : V → Prop)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ) :
    HasWeakTopologyFromCover (fun j : Option {v : V // separating v} =>
      match j with
      | none => NonseparatingWeightLocus K separating
      | some v => ClosedStarLocus K intersect v) := by
  apply realization_hasWeakTopologyFromFaceCover
  intro σ hσ
  rcases face_core_or_separating_star intersect separating σ (hcurve σ hσ) with
    hcore | ⟨v, hv, hstar⟩
  · refine ⟨none, ?_⟩
    intro p w hw
    by_cases hws : w ∈ σ
    · exact False.elim (hcore.2 w hws hw)
    · simp [faceInclusion, hws]
  · refine ⟨some ⟨v, hv⟩, ?_⟩
    intro p
    change faceInclusion K σ hσ p ∈ ClosedStarLocus K intersect v
    refine ⟨σ, hσ, hstar, ?_⟩
    intro w hw
    simp [faceInclusion, hw]

/-- The corresponding core/star cover of the homotopy cylinder has the
required product weak topology, without finite-type assumptions. -/
theorem realization_core_stars_product_weak_cover
    {V : Type*} [DecidableEq V] (K : AbstractSimplicialComplex V)
    (intersect : V → V → ℕ) (separating : V → Prop)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ) :
    HasWeakTopologyFromCover (fun j : Option {v : V // separating v} =>
      match j with
      | none => {p : RealizationPoint K × Interval |
          p.1 ∈ NonseparatingWeightLocus K separating}
      | some v => {p : RealizationPoint K × Interval |
          p.1 ∈ ClosedStarLocus K intersect v}) := by
  convert weakTopologyFromCover_product (Y := Interval) _
    (realization_core_stars_weak_cover K intersect separating hcurve) using 1
  funext j
  cases j <;> rfl

/-- Distinct separating stars overlap only where every separating barycentric
coordinate vanishes. -/
theorem closedStarLoci_overlap_in_core
    {V : Type*} [DecidableEq V] (K : AbstractSimplicialComplex V)
    (intersect : V → V → ℕ) (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v w : {u : V // separating u}) (hvw : v ≠ w) :
    ClosedStarLocus K intersect v ∩ ClosedStarLocus K intersect w ⊆
      NonseparatingWeightLocus K separating := by
  intro x hx u hu
  by_contra hxu
  obtain ⟨σv, _, hstarv, hzerov⟩ := hx.1
  obtain ⟨σw, _, hstarw, hzerow⟩ := hx.2
  have huv : u ∈ σv := by
    by_contra hn
    exact hxu (hzerov u hn)
  have huw : u ∈ σw := by
    by_contra hn
    exact hxu (hzerow u hn)
  have hveq : (v : V) = u :=
    face_at_most_one_separating intersect separating hsep
      (insert (v : V) σv) hstarv (v : V) (Finset.mem_insert_self _ _)
      v.property u (Finset.mem_insert_of_mem huv) hu
  have hweq : (w : V) = u :=
    face_at_most_one_separating intersect separating hsep
      (insert (w : V) σw) hstarw (w : V) (Finset.mem_insert_self _ _)
      w.property u (Finset.mem_insert_of_mem huw) hu
  exact hvw (Subtype.ext (hveq.trans hweq.symm))

end CurveComplexGenusTwo.Topology
