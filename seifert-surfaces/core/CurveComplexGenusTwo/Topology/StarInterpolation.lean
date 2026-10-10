import CurveComplexGenusTwo.Topology.StarFaceAssembly
import CurveComplexGenusTwo.Foundations.ConeRealization

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

variable {V : Type*} [DecidableEq V]

/-- The additional face-completeness condition needed to realize a
combinatorial closed star as an actual cone. It follows for the full
intersection-one curve complex from its defining face equivalence. -/
def HasRealizedStarFaces (K : AbstractSimplicialComplex V)
    (intersect : V → V → ℕ) (v : V) : Prop :=
  ∀ σ : Finset V, σ ∈ K.faces → ClosedStarFace intersect v σ →
    insert v σ ∈ K.faces

theorem hasRealizedStarFaces_of_fullCurveFaces
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces) :
    HasRealizedStarFaces K intersect v := by
  intro σ hσ hstar
  exact hfull (insert v σ) (Finset.insert_nonempty v σ) hstar

/-- Radial interpolation toward the apex stays in the realized closed star,
provided every combinatorial star face is actually a face of `K`. -/
noncomputable def closedStarInterpolate
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (hfull : HasRealizedStarFaces K intersect v)
    (t : ConeTime) (x : ClosedStarLocus K intersect v) :
    ClosedStarLocus K intersect v := by
  classical
  let σ : Finset V := Classical.choose x.property
  have hσ : σ ∈ K.faces := (Classical.choose_spec x.property).1
  have hstar : ClosedStarFace intersect v σ :=
    (Classical.choose_spec x.property).2.1
  have hzero : ∀ w ∉ σ, x.1.weight w = 0 :=
    (Classical.choose_spec x.property).2.2
  let y : RealizationPoint K := {
    weight := coneWeight K v t x.1
    nonneg := coneWeight_nonneg K v t x.1
    liesInFace := by
      obtain ⟨τ, hτ, hτzero, hτsum⟩ := x.1.liesInFace
      have hsum : ∑ w ∈ σ, x.1.weight w = 1 := by
        have hσu : ∑ w ∈ σ, x.1.weight w =
            ∑ w ∈ σ ∪ τ, x.1.weight w := by
          apply Finset.sum_subset_zero_on_sdiff
          · exact Finset.subset_union_left
          · intro w hw
            exact hzero w (Finset.mem_sdiff.mp hw).2
          · intro w hw
            rfl
        have hτu : ∑ w ∈ τ, x.1.weight w =
            ∑ w ∈ σ ∪ τ, x.1.weight w := by
          apply Finset.sum_subset_zero_on_sdiff
          · exact Finset.subset_union_right
          · intro w hw
            exact hτzero w (Finset.mem_sdiff.mp hw).2
          · intro w hw
            rfl
        calc
          _ = ∑ w ∈ σ ∪ τ, x.1.weight w := hσu
          _ = ∑ w ∈ τ, x.1.weight w := hτu.symm
          _ = 1 := hτsum
      exact ⟨insert v σ, hfull σ hσ hstar,
        coneWeight_zero_outside K v t x.1 σ hzero,
        coneWeight_sum K v t x.1 σ hzero hsum⟩
  }
  refine ⟨y, insert v σ, hfull σ hσ hstar, ?_, ?_⟩
  · simpa [ClosedStarFace, Finset.insert_idem] using hstar
  · exact coneWeight_zero_outside K v t x.1 σ hzero

theorem closedStarInterpolate_weight
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (hfull : HasRealizedStarFaces K intersect v)
    (t : ConeTime) (x : ClosedStarLocus K intersect v) (w : V) :
    (closedStarInterpolate K intersect v hfull t x).1.weight w =
      coneWeight K v t x.1 w := rfl

omit [DecidableEq V] in
private theorem realizationPoint_ext_weight
    (K : AbstractSimplicialComplex V) {x y : RealizationPoint K}
    (h : x.weight = y.weight) : x = y := by
  cases x with
  | mk wx hx px =>
    cases y with
    | mk wy hy py =>
      cases h
      rfl

/-- The apex lies in every realized closed star of its vertex. -/
noncomputable def closedStarApex
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) : ClosedStarLocus K intersect v := by
  classical
  refine ⟨coneVertex K v, {v}, K.singleton_mem v, ?_, ?_⟩
  · simp [ClosedStarFace, CurveFace]
  · intro w hw
    have hne : w ≠ v := by
      simpa using hw
    simp [coneVertex, hne]

theorem closedStarInterpolate_zero
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (hfull : HasRealizedStarFaces K intersect v)
    (x : ClosedStarLocus K intersect v) :
    closedStarInterpolate K intersect v hfull ⟨0, by norm_num⟩ x = x := by
  apply Subtype.ext
  apply realizationPoint_ext_weight K
  funext w
  rw [closedStarInterpolate_weight]
  simp [coneWeight]

theorem closedStarInterpolate_one
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (hfull : HasRealizedStarFaces K intersect v)
    (x : ClosedStarLocus K intersect v) :
    closedStarInterpolate K intersect v hfull ⟨1, by norm_num⟩ x =
      closedStarApex K intersect v := by
  apply Subtype.ext
  apply realizationPoint_ext_weight K
  funext w
  rw [closedStarInterpolate_weight]
  simp [coneWeight, closedStarApex, coneVertex]

end CurveComplexGenusTwo.Topology
