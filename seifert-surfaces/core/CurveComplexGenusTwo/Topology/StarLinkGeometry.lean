import CurveComplexGenusTwo.Topology.StarFaceAssembly

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

/-- Every barycentric coordinate is continuous for the actual weak
realization topology. -/
theorem realization_weight_continuous
    {V : Type*} (K : AbstractSimplicialComplex V) (v : V) :
    Continuous (fun x : RealizationPoint K => x.weight v) := by
  rw [continuous_def]
  intro U hU σ hσ
  change IsOpen ((fun p : FiniteSimplex σ =>
    (faceInclusion K σ hσ p).weight v) ⁻¹' U)
  have hc : Continuous (fun p : FiniteSimplex σ =>
      (faceInclusion K σ hσ p).weight v) := by
    by_cases hv : v ∈ σ
    · simp only [faceInclusion, hv, dite_true]
      exact (continuous_apply (⟨v, hv⟩ : σ)).comp continuous_subtype_val
    · simp only [faceInclusion, hv, dite_false]
      exact continuous_const
  exact hc.isOpen_preimage U hU

theorem realization_weight_le_one
    {V : Type*} (K : AbstractSimplicialComplex V)
    (x : RealizationPoint K) (v : V) : x.weight v ≤ 1 := by
  obtain ⟨σ, _, hzero, hsum⟩ := x.liesInFace
  by_cases hv : v ∈ σ
  · have hle : x.weight v ≤ ∑ w ∈ σ, x.weight w := by
      simpa only [Finset.sum_attach, Finset.univ_eq_attach] using
        Finset.single_le_sum (fun w hw => x.nonneg w) hv
    simpa [hsum] using hle
  · simp [hzero v hv]

/-- Inside a separating closed star, the realized link is exactly the
zero-height face opposite the apex. This uses separation of distinct
separating vertices, not a finite-type assumption. -/
theorem closedStar_inter_core_eq_zero_apex
    {V : Type*} [DecidableEq V] (K : AbstractSimplicialComplex V)
    (intersect : V → V → ℕ) (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u}) :
    ClosedStarLocus K intersect v ∩ NonseparatingWeightLocus K separating =
      {x | x ∈ ClosedStarLocus K intersect v ∧ x.weight v = 0} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, hx.2 v v.property⟩
  · rintro ⟨hstar, hvzero⟩
    refine ⟨hstar, ?_⟩
    intro u hu
    rcases hstar with ⟨σ, hσ, hface, hzero⟩
    by_cases hmem : u ∈ σ
    · have hveq : (v : V) = u :=
        face_at_most_one_separating intersect separating hsep
          (insert (v : V) σ) hface (v : V)
          (Finset.mem_insert_self _ _) v.property u
          (Finset.mem_insert_of_mem hmem) hu
      simpa [hveq] using hvzero
    · exact hzero u hmem

/-- Every nonzero coordinate of a realized closed star is compatible with
its apex in both ordered directions of the face predicate. -/
theorem closedStar_nonzero_coordinate_compatible
    {V : Type*} [DecidableEq V] (K : AbstractSimplicialComplex V)
    (intersect : V → V → ℕ) (v : V)
    (x : RealizationPoint K) (hx : x ∈ ClosedStarLocus K intersect v)
    (w : V) (hw : w ≠ v) (hpositive : x.weight w ≠ 0) :
    intersect v w ≤ 1 ∧ intersect w v ≤ 1 := by
  rcases hx with ⟨σ, _, hstar, hzero⟩
  have hmem : w ∈ σ := by
    by_contra hnot
    exact hpositive (hzero w hnot)
  constructor
  · exact hstar (Finset.mem_insert_self v σ)
      (Finset.mem_insert_of_mem hmem) hw.symm
  · exact hstar (Finset.mem_insert_of_mem hmem)
      (Finset.mem_insert_self v σ) hw

end CurveComplexGenusTwo.Topology
