import CurveComplexGenusTwo.Filtration.BoundarySquare

namespace CurveGenusTwo.Filtration

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V]

section Chains

variable [LinearOrder V]

private theorem chainInclusion_of (K L : FiniteComplex V)
    (h : K.simplices ⊆ L.simplices) (n : ℤ) (σ : SimplexAt K n) :
    chainInclusion K L h n (FreeAbelianGroup.of σ) =
      FreeAbelianGroup.of (⟨σ.1, h σ.2.1, σ.2.2⟩ : SimplexAt L n) := by
  exact FreeAbelianGroup.lift_apply_of _ _



omit [LinearOrder V] in
private theorem face_valid (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) {v : V} (hv : v ∈ σ.1) :
    σ.1.erase v ∈ K ∧
      ((n - 1 = -1 ∧ σ.1.erase v = ∅) ∨
        (0 ≤ n - 1 ∧ ((σ.1.erase v).card : ℤ) = (n - 1) + 1)) := by
  classical
  have hmem : σ.1.erase v ∈ K := K.down_closed (Finset.erase_subset v σ.1) σ.2.1
  refine ⟨hmem, ?_⟩
  rcases σ.2.2 with hneg | hpos
  · exact False.elim (by simp [hneg.2] at hv)
  · have hcard : (σ.1.erase v).card + 1 = σ.1.card := by
      simpa using Finset.card_erase_add_one hv
    by_cases hn : n = 0
    · left
      constructor
      · omega
      · have hσcard : σ.1.card = 1 := by omega
        exact Finset.card_eq_zero.mp (by omega)
    · right
      constructor <;> omega

private def faceAt (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) (v : σ.1) : SimplexAt K (n - 1) :=
  ⟨σ.1.erase v.1, face_valid K n σ v.2⟩

private theorem faceBoundary_eq (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) :
    faceBoundary K n σ = ∑ v ∈ σ.1.attach,
      (-1 : ℤ) ^ (σ.1.filter (· < v.1)).card •
        FreeAbelianGroup.of (faceAt K n σ v) := by
  classical
  rw [faceBoundary]
  conv_lhs => rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro v hv
  have hvalid := face_valid K n σ v.2
  have hproof : (⟨σ.1.erase v.1, hvalid⟩ : SimplexAt K (n - 1)) =
      faceAt K n σ v := Subtype.ext rfl
  exact (dite_eq_left hvalid).trans (congrArg
    (fun x : SimplexAt K (n - 1) =>
      (-1 : ℤ) ^ (σ.1.filter (· < v.1)).card • FreeAbelianGroup.of x) hproof)

noncomputable abbrev relativeQuotient (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) : Type u :=
  (chains (filtration K a p) n) ⧸
    (chainInclusion (filtration K a ((p : ℤ) - 1))
      (filtration K a p) (filtration_mono K a (by omega)) n).range

private noncomputable def relativeProjection (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    chains (filtration K a p) n →+ relativeChains K a p n :=
  FreeAbelianGroup.lift fun σ =>
    if h : (badVertices a σ.1).card = p then
      FreeAbelianGroup.of
        (⟨⟨σ.1, σ.2.1.1, σ.2.2⟩, h⟩ : RelativeSimplexAt K a p n)
    else 0

private noncomputable def relativeSection (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    relativeChains K a p n →+ chains (filtration K a p) n :=
  FreeAbelianGroup.lift fun σ =>
    FreeAbelianGroup.of
      (⟨σ.1.1, ⟨σ.1.2.1, by have hp := σ.2; omega⟩, σ.1.2.2⟩ :
        SimplexAt (filtration K a p) n)

private theorem relativeProjection_of (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ)
    (σ : SimplexAt (filtration K a p) n) :
    relativeProjection K a p n (FreeAbelianGroup.of σ) =
      if h : (badVertices a σ.1).card = p then
        FreeAbelianGroup.of
          (⟨⟨σ.1, σ.2.1.1, σ.2.2⟩, h⟩ : RelativeSimplexAt K a p n)
      else 0 := by
  exact FreeAbelianGroup.lift_apply_of _ _

private theorem relativeSection_of (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ)
    (σ : RelativeSimplexAt K a p n) :
    relativeSection K a p n (FreeAbelianGroup.of σ) =
      FreeAbelianGroup.of
        (⟨σ.1.1, ⟨σ.1.2.1, by have hp := σ.2; omega⟩, σ.1.2.2⟩ :
          SimplexAt (filtration K a p) n) := by
  exact FreeAbelianGroup.lift_apply_of _ _

private theorem relativeProjection_section (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    (relativeProjection K a p n).comp (relativeSection K a p n) =
      AddMonoidHom.id (relativeChains K a p n) := by
  ext σ
  let τ : SimplexAt (filtration K a p) n :=
    ⟨σ.1.1, ⟨σ.1.2.1, by have hp := σ.2; omega⟩, σ.1.2.2⟩
  change (relativeProjection K a p n)
    ((relativeSection K a p n) (FreeAbelianGroup.of σ)) = FreeAbelianGroup.of σ
  rw [relativeSection_of]
  change (relativeProjection K a p n) (FreeAbelianGroup.of τ) = FreeAbelianGroup.of σ
  rw [relativeProjection_of]
  have hp : (badVertices a σ.1.1).card = p := σ.2
  have hpτ : (badVertices a τ.1).card = p := hp
  simp only [dif_pos hpτ]
  congr 1

private theorem relativeProjection_inclusion_zero (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    (relativeProjection K a p n).comp
      (chainInclusion (filtration K a ((p : ℤ) - 1))
        (filtration K a p) (filtration_mono K a (by omega)) n) = 0 := by
  ext σ
  change (relativeProjection K a p n)
    (chainInclusion (filtration K a ((p : ℤ) - 1))
      (filtration K a p) (filtration_mono K a (by omega)) n
      (FreeAbelianGroup.of σ)) = 0
  rw [chainInclusion_of]
  let τ : SimplexAt (filtration K a p) n :=
    ⟨σ.1, (filtration_mono K a (by omega)) σ.2.1, σ.2.2⟩
  change (relativeProjection K a p n) (FreeAbelianGroup.of τ) = 0
  rw [relativeProjection_of]
  have hlt : (badVertices a τ.1).card ≤ (p : ℤ) - 1 := σ.2.1.2
  have hne : (badVertices a τ.1).card ≠ p := by omega
  simp [hne]
  rfl

private noncomputable def relativeQuotientProjection (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    relativeQuotient K a p n →+ relativeChains K a p n := by
  let i := chainInclusion (filtration K a ((p : ℤ) - 1))
    (filtration K a p) (filtration_mono K a (by omega)) n
  have hle : i.range ≤ (relativeProjection K a p n).ker := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    have hzero := congrArg (fun f => f y) (relativeProjection_inclusion_zero K a p n)
    simpa [i] using hzero
  exact QuotientAddGroup.lift i.range (relativeProjection K a p n) hle

private noncomputable def relativeQuotientSection (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    relativeChains K a p n →+ relativeQuotient K a p n :=
  (QuotientAddGroup.mk' _).comp (relativeSection K a p n)

private theorem relativeQuotientProjection_section (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    (relativeQuotientProjection K a p n).comp
      (relativeQuotientSection K a p n) =
        AddMonoidHom.id (relativeChains K a p n) := by
  ext x
  change (relativeProjection K a p n) ((relativeSection K a p n)
    (FreeAbelianGroup.of x)) = FreeAbelianGroup.of x
  exact congrArg (fun f => f (FreeAbelianGroup.of x))
    (relativeProjection_section K a p n)

private theorem relativeQuotientSection_projection (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    (relativeQuotientSection K a p n).comp (relativeQuotientProjection K a p n) =
      AddMonoidHom.id (relativeQuotient K a p n) := by
  apply AddMonoidHom.ext
  intro q
  induction q using QuotientAddGroup.induction_on with
  | _ c =>
    induction c using FreeAbelianGroup.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | neg x hx => simp [map_neg, hx]
    | of σ =>
      change relativeQuotientSection K a p n
          (relativeQuotientProjection K a p n
            (QuotientAddGroup.mk' _ (FreeAbelianGroup.of σ))) =
          QuotientAddGroup.mk' _ (FreeAbelianGroup.of σ)
      change relativeQuotientSection K a p n
          (relativeProjection K a p n (FreeAbelianGroup.of σ)) =
          QuotientAddGroup.mk' _ (FreeAbelianGroup.of σ)
      rw [relativeProjection_of]
      by_cases hp : (badVertices a σ.1).card = p
      · rw [dif_pos hp]
        change QuotientAddGroup.mk' _
            (relativeSection K a p n (FreeAbelianGroup.of
              (⟨⟨σ.1, σ.2.1.1, σ.2.2⟩, hp⟩ : RelativeSimplexAt K a p n))) =
          QuotientAddGroup.mk' _ (FreeAbelianGroup.of σ)
        exact congrArg (QuotientAddGroup.mk' _) (relativeSection_of K a p n
          (⟨⟨σ.1, σ.2.1.1, σ.2.2⟩, hp⟩ : RelativeSimplexAt K a p n)) |>.trans
          (by congr 1)
      · rw [dif_neg hp]
        change QuotientAddGroup.mk' _ 0 = QuotientAddGroup.mk' _ (FreeAbelianGroup.of σ)
        rw [map_zero]
        have hlt : (badVertices a σ.1).card ≤ (p : ℤ) - 1 := by
          have hle := σ.2.1.2
          omega
        let τ : SimplexAt (filtration K a ((p : ℤ) - 1)) n :=
          ⟨σ.1, ⟨σ.2.1.1, hlt⟩, σ.2.2⟩
        have hmem : FreeAbelianGroup.of σ ∈
            (chainInclusion (filtration K a ((p : ℤ) - 1))
              (filtration K a p) (filtration_mono K a (by omega)) n).range := by
          refine ⟨FreeAbelianGroup.of τ, ?_⟩
          rw [chainInclusion_of]
          congr 1
        symm
        exact (QuotientAddGroup.eq_zero_iff _).2 hmem

/-- The exact-support basis is the relative group of the augmented filtration. -/
theorem relativeChains_are_quotient (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) :
    Nonempty (relativeQuotient K a p n ≃+ relativeChains K a p n) := by
  let f := relativeQuotientProjection K a p n
  let g := relativeQuotientSection K a p n
  refine ⟨{
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    map_add' := f.map_add }⟩
  · intro x
    exact congrArg (fun h => h x) (relativeQuotientSection_projection K a p n)
  · intro x
    exact congrArg (fun h => h x) (relativeQuotientProjection_section K a p n)


/-- Relative boundary is the ordinary face sum with faces in lower filtration discarded. -/
noncomputable def relativeFaceBoundary (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) (σ : RelativeSimplexAt K a p n) :
    relativeChains K a p (n - 1) := by
  classical
  exact ∑ v ∈ σ.1.1,
    if h : (σ.1.1.erase v ∈ K ∧
      (((n - 1) = -1 ∧ σ.1.1.erase v = ∅) ∨
        (0 ≤ n - 1 ∧ ((σ.1.1.erase v).card : ℤ) = (n - 1) + 1))) ∧
        (badVertices a (σ.1.1.erase v)).card = p then
      (-1 : ℤ) ^ (σ.1.1.filter (· < v)).card •
        FreeAbelianGroup.of
          (⟨⟨σ.1.1.erase v, h.1⟩, h.2⟩ : RelativeSimplexAt K a p (n - 1))
    else 0

noncomputable def relativeBoundary (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) : relativeChains K a p n →+ relativeChains K a p (n - 1) :=
  FreeAbelianGroup.lift (relativeFaceBoundary K a p n)

theorem chainInclusion_boundary (K L : FiniteComplex V)
    (h : K.simplices ⊆ L.simplices) (n : ℤ) :
    (boundary L n).comp (chainInclusion K L h n) =
      (chainInclusion K L h (n - 1)).comp (boundary K n) := by
  classical
  apply FreeAbelianGroup.lift_ext
  intro σ
  change boundary L n (chainInclusion K L h n (FreeAbelianGroup.of σ)) =
    chainInclusion K L h (n - 1) (boundary K n (FreeAbelianGroup.of σ))
  rw [chainInclusion_of]
  let τ : SimplexAt L n := ⟨σ.1, h σ.2.1, σ.2.2⟩
  have hτ : boundary L n (FreeAbelianGroup.of τ) = faceBoundary L n τ := by
    simp [boundary]
  have hσ : boundary K n (FreeAbelianGroup.of σ) = faceBoundary K n σ := by
    simp [boundary]
  change boundary L n (FreeAbelianGroup.of τ) =
    chainInclusion K L h (n - 1) (boundary K n (FreeAbelianGroup.of σ))
  rw [hτ, hσ]
  rw [faceBoundary_eq, faceBoundary_eq, map_sum]
  simp_rw [map_zsmul, chainInclusion_of]
  apply Finset.sum_congr rfl
  intro v hv
  congr 1

private theorem relativeProjection_boundary_section (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    (relativeProjection K a p (n - 1)).comp
      ((boundary (filtration K a p) n).comp (relativeSection K a p n)) =
        relativeBoundary K a p n := by
  apply FreeAbelianGroup.lift_ext
  intro σ
  change relativeProjection K a p (n - 1)
      (boundary (filtration K a p) n
        (relativeSection K a p n (FreeAbelianGroup.of σ))) =
      relativeBoundary K a p n (FreeAbelianGroup.of σ)
  rw [relativeSection_of]
  let τ : SimplexAt (filtration K a p) n :=
    ⟨σ.1.1, ⟨σ.1.2.1, by have hp := σ.2; omega⟩, σ.1.2.2⟩
  have hτ : boundary (filtration K a p) n (FreeAbelianGroup.of τ) =
      faceBoundary (filtration K a p) n τ := by simp [boundary]
  have hσ : relativeBoundary K a p n (FreeAbelianGroup.of σ) =
      relativeFaceBoundary K a p n σ := by simp [relativeBoundary]
  change relativeProjection K a p (n - 1)
      (boundary (filtration K a p) n (FreeAbelianGroup.of τ)) =
    relativeBoundary K a p n (FreeAbelianGroup.of σ)
  rw [hτ, hσ]
  rw [faceBoundary_eq, map_sum]
  simp_rw [map_zsmul, relativeProjection_of]
  rw [relativeFaceBoundary]
  conv_rhs => rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro v hv
  have hvalid := face_valid K n σ.1 v.2
  have hsub := badVertices_mono a (Finset.erase_subset v.1 σ.1.1)
  have hle : (badVertices a (σ.1.1.erase v.1)).card ≤ (p : ℤ) := by
    have hc := Finset.card_le_card hsub
    have hp := σ.2
    omega
  have hvalidFiltration :
      σ.1.1.erase v.1 ∈ filtration K a p := ⟨hvalid.1, hle⟩
  by_cases hp : (badVertices a (σ.1.1.erase v.1)).card = p
  · have ht : (σ.1.1.erase v.1 ∈ K ∧
      ((n - 1 = -1 ∧ σ.1.1.erase v.1 = ∅) ∨
        (0 ≤ n - 1 ∧ ((σ.1.1.erase v.1).card : ℤ) = (n - 1) + 1))) ∧
        (badVertices a (σ.1.1.erase v.1)).card = p := ⟨hvalid, hp⟩
    simp [faceAt, τ, hp]
    symm
    apply dite_eq_left ht
  · have ht : ¬ ((σ.1.1.erase v.1 ∈ K ∧
      ((n - 1 = -1 ∧ σ.1.1.erase v.1 = ∅) ∨
        (0 ≤ n - 1 ∧ ((σ.1.1.erase v.1).card : ℤ) = (n - 1) + 1))) ∧
        (badVertices a (σ.1.1.erase v.1)).card = p) := fun x => hp x.2
    simp [faceAt, τ, hp]
    let z : ℤ := (-1 : ℤ) ^ (σ.1.1.filter (· < v.1)).card
    change z • (0 : relativeChains K a p (n - 1)) = 0
    exact smul_zero z

/-- The quotient differential is induced by the ordinary augmented differential,
    and the exact-support basis identifies it with `relativeBoundary`. -/
theorem relativeQuotient_boundary (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) :
    ∃ d : (n : ℤ) → relativeQuotient K a p n →+
      relativeQuotient K a p (n - 1),
      ∃ e : (n : ℤ) → relativeQuotient K a p n ≃+ relativeChains K a p n,
        (∀ n : ℤ, ∀ c : chains (filtration K a p) n,
          d n (QuotientAddGroup.mk' _ c) =
            QuotientAddGroup.mk' _ (boundary (filtration K a p) n c)) ∧
        (∀ n : ℤ, ∀ c : relativeQuotient K a p n,
          e (n - 1) (d n c) = relativeBoundary K a p n (e n c)) := by
  let I (n : ℤ) := chainInclusion (filtration K a ((p : ℤ) - 1))
    (filtration K a p) (filtration_mono K a (by omega)) n
  let q (n : ℤ) := QuotientAddGroup.mk' (I n).range
  let d (n : ℤ) : relativeQuotient K a p n →+
      relativeQuotient K a p (n - 1) := by
    have hle : (I n).range ≤ ((q (n - 1)).comp (boundary (filtration K a p) n)).ker := by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      have hnat := congrArg (fun f => f y)
        (chainInclusion_boundary (filtration K a ((p : ℤ) - 1))
          (filtration K a p) (filtration_mono K a (by omega)) n)
      change q (n - 1) (boundary (filtration K a p) n (I n y)) = 0
      rw [show boundary (filtration K a p) n (I n y) =
          I (n - 1) (boundary (filtration K a ((p : ℤ) - 1)) n y) from hnat]
      exact (QuotientAddGroup.eq_zero_iff _).2 ⟨_, rfl⟩
    exact QuotientAddGroup.lift (I n).range
      ((q (n - 1)).comp (boundary (filtration K a p) n)) hle
  let e (n : ℤ) : relativeQuotient K a p n ≃+ relativeChains K a p n := {
    toFun := relativeQuotientProjection K a p n
    invFun := relativeQuotientSection K a p n
    left_inv := fun x => congrArg (fun f => f x)
      (relativeQuotientSection_projection K a p n)
    right_inv := fun x => congrArg (fun f => f x)
      (relativeQuotientProjection_section K a p n)
    map_add' := (relativeQuotientProjection K a p n).map_add }
  refine ⟨d, e, ?_, ?_⟩
  · intro n c
    change d n (q n c) = q (n - 1) (boundary (filtration K a p) n c)
    rfl
  · intro n c
    have hc : (relativeQuotientSection K a p n)
        ((relativeQuotientProjection K a p n) c) = c :=
      congrArg (fun f => f c) (relativeQuotientSection_projection K a p n)
    conv_lhs => rw [← hc]
    change relativeProjection K a p (n - 1)
      (boundary (filtration K a p) n
        (relativeSection K a p n ((relativeQuotientProjection K a p n) c))) =
      relativeBoundary K a p n ((relativeQuotientProjection K a p n) c)
    exact congrArg (fun f => f ((relativeQuotientProjection K a p n) c))
      (relativeProjection_boundary_section K a p n)

theorem relative_boundary_boundary (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) :
    (relativeBoundary K a p (n - 1)).comp (relativeBoundary K a p n) = 0 := by
  obtain ⟨d, e, hdesc, hcompat⟩ := relativeQuotient_boundary K a p
  have hdd (m : ℤ) (x : relativeQuotient K a p m) :
      d (m - 1) (d m x) = 0 := by
    induction x using QuotientAddGroup.induction_on with
    | _ c =>
      change d (m - 1) (d m (QuotientAddGroup.mk' _ c)) = 0
      rw [hdesc m c, hdesc (m - 1) (boundary (filtration K a p) m c)]
      have hsquare := congrArg (fun f => f c)
        (boundary_boundary (filtration K a p) m)
      change boundary (filtration K a p) (m - 1)
        (boundary (filtration K a p) m c) = 0 at hsquare
      rw [hsquare, map_zero]
  apply AddMonoidHom.ext
  intro c
  change relativeBoundary K a p (n - 1) (relativeBoundary K a p n c) = 0
  let x := (e n).symm c
  have hex : e n x = c := (e n).apply_symm_apply c
  have hfirst := hcompat n x
  have hsecond := hcompat (n - 1) (d n x)
  rw [← hex, ← hfirst, ← hsecond, hdd n x, map_zero]

end Chains

end CurveGenusTwo.Filtration
