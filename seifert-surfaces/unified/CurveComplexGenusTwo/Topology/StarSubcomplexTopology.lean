import CurveComplexGenusTwo.Topology.StarLinkGeometry
import CurveComplexGenusTwo.Topology.StarInterpolation

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

variable {V : Type*} [DecidableEq V]

/-- Coordinate condition for a point to lie in the closed star of `v`.
Both ordered intersection inequalities are retained because `CurveFace`
does not encode symmetry of the supplied intersection function. -/
def StarCoordinateCompatible (K : AbstractSimplicialComplex V)
    (intersect : V → V → ℕ) (v : V) (x : RealizationPoint K) : Prop :=
  ∀ w, w ≠ v → x.weight w ≠ 0 →
    intersect v w ≤ 1 ∧ intersect w v ≤ 1

theorem closedStar_iff_coordinate_compatible
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces)
    (x : RealizationPoint K) :
    x ∈ ClosedStarLocus K intersect v ↔
      StarCoordinateCompatible K intersect v x := by
  constructor
  · intro hx w hw hn
    exact closedStar_nonzero_coordinate_compatible K intersect v x hx w hw hn
  · intro hc
    obtain ⟨σ, hσ, hzero, hsum⟩ := x.liesInFace
    let ρ : Finset V := σ.filter (fun w => x.weight w ≠ 0)
    have hρsubset : ρ ⊆ σ := Finset.filter_subset _ _
    have hρnonempty : ρ.Nonempty := by
      by_contra hnot
      have hρempty : ρ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
      have hsumzero : ∑ w ∈ σ, x.weight w = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        by_contra hn
        have hmem : w ∈ ρ := Finset.mem_filter.mpr ⟨hw, hn⟩
        rw [hρempty] at hmem
        simp at hmem
      rw [hsumzero] at hsum
      norm_num at hsum
    have hρcurve : CurveFace intersect 1 ρ :=
      (hcurve σ hσ).mono hρsubset
    have hρstar : ClosedStarFace intersect v ρ := by
      intro a ha b hb hab
      have ha' : a = v ∨ a ∈ ρ := Finset.mem_insert.mp ha
      have hb' : b = v ∨ b ∈ ρ := Finset.mem_insert.mp hb
      rcases ha' with hav | haρ
      · subst a
        rcases hb' with hbv | hbρ
        · exact False.elim (hab hbv.symm)
        · exact (hc b (Ne.symm hab)
            (Finset.mem_filter.mp hbρ).2).1
      · rcases hb' with hbv | hbρ
        · subst b
          exact (hc a hab (Finset.mem_filter.mp haρ).2).2
        · exact hρcurve haρ hbρ hab
    refine ⟨ρ, hfull ρ hρnonempty hρcurve, hρstar, ?_⟩
    intro w hw
    by_cases hσw : w ∈ σ
    · by_contra hn
      exact hw (Finset.mem_filter.mpr ⟨hσw, hn⟩)
    · exact hzero w hσw

/-- The coordinate description makes each realized star a closed subspace of
the weak realization. Closedness alone is not the quotient-cone topology
theorem, but it is a required subcomplex-topology input. -/
theorem isClosed_closedStarLocus
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces) :
    IsClosed (ClosedStarLocus K intersect v) := by
  classical
  let bad (w : V) : Prop :=
    w ≠ v ∧ (1 < intersect v w ∨ 1 < intersect w v)
  let D (w : V) : Set (RealizationPoint K) :=
    if bad w then {x | x.weight w = 0} else Set.univ
  have hD (w : V) : IsClosed (D w) := by
    by_cases hw : bad w
    · have hc : IsClosed ((fun x : RealizationPoint K => x.weight w) ⁻¹'
          {(0 : ℝ)}) :=
        isClosed_singleton.preimage (realization_weight_continuous K w)
      convert hc using 1
      ext x
      simp [D, hw]
    · simp [D, hw]
  have heq : ClosedStarLocus K intersect v = ⋂ w, D w := by
    ext x
    rw [closedStar_iff_coordinate_compatible K intersect v hcurve hfull]
    simp only [Set.mem_iInter]
    constructor
    · intro hx w
      by_cases hw : bad w
      · have hzero : x.weight w = 0 := by
          by_contra hn
          obtain ⟨hvw, hbad⟩ := hw
          have hgood := hx w hvw hn
          rcases hbad with hbad | hbad <;> omega
        simpa [D, hw] using hzero
      · simp [D, hw]
    · intro hx w hw hn
      constructor
      · by_contra hbad
        have hB : bad w := ⟨hw, Or.inl (Nat.lt_of_not_ge hbad)⟩
        have hz : x.weight w = 0 := by simpa [D, hB] using hx w
        exact hn hz
      · by_contra hbad
        have hB : bad w := ⟨hw, Or.inr (Nat.lt_of_not_ge hbad)⟩
        have hz : x.weight w = 0 := by simpa [D, hB] using hx w
        exact hn hz
  rw [heq]
  exact isClosed_iInter hD


end CurveComplexGenusTwo.Topology
