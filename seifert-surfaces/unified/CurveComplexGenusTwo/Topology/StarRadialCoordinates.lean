import CurveComplexGenusTwo.Topology.StarInterpolation
import CurveComplexGenusTwo.Topology.StarLinkGeometry
import CurveComplexGenusTwo.Topology.RealizationStarDeletion

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
private theorem point_ext_weight
    (K : AbstractSimplicialComplex V) {x y : RealizationPoint K}
    (h : x.weight = y.weight) : x = y := by
  cases x with
  | mk wx hx px =>
    cases y with
    | mk wy hy py =>
      cases h
      rfl

private theorem sum_on_any_support
    (K : AbstractSimplicialComplex V) (x : RealizationPoint K)
    (σ : Finset V) (hzero : ∀ w ∉ σ, x.weight w = 0) :
    ∑ w ∈ σ, x.weight w = 1 := by
  obtain ⟨τ, _, hτzero, hτsum⟩ := x.liesInFace
  have hσu : ∑ w ∈ σ, x.weight w =
      ∑ w ∈ σ ∪ τ, x.weight w := by
    apply Finset.sum_subset_zero_on_sdiff
    · exact Finset.subset_union_left
    · intro w hw
      exact hzero w (Finset.mem_sdiff.mp hw).2
    · intro w hw
      rfl
  have hτu : ∑ w ∈ τ, x.weight w =
      ∑ w ∈ σ ∪ τ, x.weight w := by
    apply Finset.sum_subset_zero_on_sdiff
    · exact Finset.subset_union_right
    · intro w hw
      exact hτzero w (Finset.mem_sdiff.mp hw).2
    · intro w hw
      rfl
  calc
    _ = ∑ w ∈ σ ∪ τ, x.weight w := hσu
    _ = ∑ w ∈ τ, x.weight w := hτu.symm
    _ = 1 := hτsum

/-- The mass away from `v` of a barycentric point. It is positive exactly on
the punctured star, where radial normalization is defined. -/
def offApexMass (K : AbstractSimplicialComplex V)
    (v : V) (x : RealizationPoint K) : ℝ := 1 - x.weight v

omit [DecidableEq V] in
theorem offApexMass_pos_of_lt
    (K : AbstractSimplicialComplex V) (v : V)
    (x : RealizationPoint K) (hv : x.weight v < 1) :
    0 < offApexMass K v x := by
  unfold offApexMass
  linarith

theorem realization_eq_vertex_of_weight_one
    (K : AbstractSimplicialComplex V) (x : RealizationPoint K)
    (v : V) (hv : x.weight v = 1) : x = coneVertex K v := by
  classical
  obtain ⟨σ, _, hzero, hsum⟩ := x.liesInFace
  have hvσ : v ∈ σ := by
    by_contra hn
    have hz := hzero v hn
    linarith
  have herase : ∑ w ∈ σ.erase v, x.weight w = 0 := by
    have he := Finset.sum_erase_add σ (fun w => x.weight w) hvσ
    rw [hsum, hv] at he
    linarith
  apply point_ext_weight K
  funext w
  by_cases hw : w = v
  · subst w
    simp [coneVertex, hv]
  · have hzw : x.weight w = 0 := by
      by_cases hmem : w ∈ σ
      · have hle : x.weight w ≤ ∑ u ∈ σ.erase v, x.weight u := by
          simpa only [Finset.sum_attach, Finset.univ_eq_attach] using
            Finset.single_le_sum (fun u hu => x.nonneg u)
              (Finset.mem_erase.mpr ⟨hw, hmem⟩)
        rw [herase] at hle
        exact le_antisymm hle (x.nonneg w)
      · exact hzero w hmem
    simp [coneVertex, hw, hzw]

private theorem sum_offApex
    (K : AbstractSimplicialComplex V) (x : RealizationPoint K)
    (v : V) (σ : Finset V) (hzero : ∀ w ∉ σ, x.weight w = 0) :
    ∑ w ∈ σ, (if w = v then (0 : ℝ) else x.weight w) =
      offApexMass K v x := by
  classical
  have hsum := sum_on_any_support K x σ hzero
  by_cases hvσ : v ∈ σ
  · let g : V → ℝ := fun w => if w = v then 0 else x.weight w
    have hg : g v = 0 := by simp [g]
    have hge : ∑ w ∈ σ, g w = ∑ w ∈ σ.erase v, x.weight w := by
      calc
        _ = ∑ w ∈ σ.erase v, g w :=
          (Finset.sum_erase σ hg).symm
        _ = ∑ w ∈ σ.erase v, x.weight w := by
          apply Finset.sum_congr rfl
          intro w hw
          simp [g, Finset.ne_of_mem_erase hw]
    have he := Finset.sum_erase_add σ (fun w => x.weight w) hvσ
    change (∑ w ∈ σ, g w) = offApexMass K v x
    rw [hge]
    dsimp [offApexMass]
    linarith
  · have hvzero : x.weight v = 0 := hzero v hvσ
    have hg : (∑ w ∈ σ, if w = v then (0 : ℝ) else x.weight w) =
        ∑ w ∈ σ, x.weight w := by
      apply Finset.sum_congr rfl
      intro w hw
      simp [show w ≠ v from fun h => hvσ (h ▸ hw)]
    rw [hg, hsum]
    simp [offApexMass, hvzero]

/-- Normalize the non-apex barycentric coordinates. The output is a point
of the realized link because the original star witness remains a face and
the apex coordinate is removed. -/
noncomputable def radialLinkPoint
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (x : ClosedStarLocus K intersect v)
    (hx : x.1.weight v < 1) :
    RealizedSeparatingLink K intersect separating v := by
  classical
  let σ : Finset V := Classical.choose x.property
  have hσ : σ ∈ K.faces := (Classical.choose_spec x.property).1
  have hstar : ClosedStarFace intersect v σ :=
    (Classical.choose_spec x.property).2.1
  have hzero : ∀ w ∉ σ, x.1.weight w = 0 :=
    (Classical.choose_spec x.property).2.2
  let d : ℝ := offApexMass K v x.1
  have hd : 0 < d := offApexMass_pos_of_lt K v x.1 hx
  let y : RealizationPoint K := {
    weight := fun w => if w = (v : V) then 0 else x.1.weight w / d
    nonneg := by
      intro w
      split_ifs
      · exact le_refl 0
      · exact div_nonneg (x.1.nonneg w) hd.le
    liesInFace := by
      refine ⟨σ, hσ, ?_, ?_⟩
      · intro w hw
        simp [hzero w hw]
      · have hmass := sum_offApex K x.1 (v : V) σ hzero
        have hdiv : (∑ w ∈ σ,
            (if w = (v : V) then (0 : ℝ) else x.1.weight w) / d) = 1 := by
          rw [← Finset.sum_div]
          simpa [d] using (div_self (ne_of_gt hd) : d / d = 1) ▸ congrArg (fun z : ℝ => z / d) hmass
        simpa only [ite_div, zero_div] using hdiv
  }
  refine ⟨y, ?_⟩
  change y ∈ ClosedStarLocus K intersect v ∩
    NonseparatingWeightLocus K separating
  rw [closedStar_inter_core_eq_zero_apex K intersect separating hsep v]
  refine ⟨⟨σ, hσ, hstar, ?_⟩, ?_⟩
  · intro w hw
    simp [y, hzero w hw]
  · simp [y]

theorem radialLinkPoint_weight
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (x : ClosedStarLocus K intersect v)
    (hx : x.1.weight v < 1) (w : V) :
    (radialLinkPoint K intersect separating hsep v x hx).1.weight w =
      if w = (v : V) then 0 else
        x.1.weight w / offApexMass K v x.1 := rfl

/-- Barycentric reconstruction of every non-apex star point from its apex
height and normalized link coordinate. -/
theorem closedStar_radial_reconstruct
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (separating : V → Prop)
    (hsep : ∀ a b, separating a → separating b → a ≠ b →
      1 < intersect a b)
    (v : {u : V // separating u})
    (hfull : HasRealizedStarFaces K intersect v)
    (x : ClosedStarLocus K intersect v)
    (hx : x.1.weight v < 1) :
    closedStarInterpolate K intersect v hfull
      ⟨x.1.weight v, x.1.nonneg v, realization_weight_le_one K x.1 v⟩
      ⟨(radialLinkPoint K intersect separating hsep v x hx).1,
        (radialLinkPoint K intersect separating hsep v x hx).property.1⟩ = x := by
  apply Subtype.ext
  apply point_ext_weight K
  funext w
  rw [closedStarInterpolate_weight]
  dsimp [coneWeight]
  rw [radialLinkPoint_weight]
  by_cases hw : w = (v : V)
  · subst w
    simp
  · simp only [ite_eq_right hw, add_zero]
    have hd : offApexMass K v x.1 ≠ 0 :=
      ne_of_gt (offApexMass_pos_of_lt K v x.1 hx)
    dsimp [offApexMass] at hd ⊢
    field_simp

end CurveComplexGenusTwo.Topology
