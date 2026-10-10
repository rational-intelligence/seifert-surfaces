import CurveComplexGenusTwo.Filtration.FiltrationSplittingIntegrated
import CurveComplexGenusTwo.Filtration.DirectSumHomologyLocal

namespace CurveGenusTwo.Filtration

universe u v w

private noncomputable def quotientAddEquiv
    {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (SA : AddSubgroup A) (SB : AddSubgroup B)
    (h : ∀ x : A, x ∈ SA ↔ e x ∈ SB) :
    A ⧸ SA ≃+ B ⧸ SB := by
  let f : A ⧸ SA →+ B ⧸ SB :=
    QuotientAddGroup.lift SA
      ((QuotientAddGroup.mk' SB).comp e.toAddMonoidHom)
      (by
        intro x hx
        change QuotientAddGroup.mk' SB (e x) = 0
        exact (QuotientAddGroup.eq_zero_iff (e x)).2 ((h x).mp hx))
  let g : B ⧸ SB →+ A ⧸ SA :=
    QuotientAddGroup.lift SB
      ((QuotientAddGroup.mk' SA).comp e.symm.toAddMonoidHom)
      (by
        intro y hy
        change QuotientAddGroup.mk' SA (e.symm y) = 0
        exact (QuotientAddGroup.eq_zero_iff (e.symm y)).2
          ((h (e.symm y)).mpr (by simpa using hy)))
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    map_add' := f.map_add }
  · intro x
    induction x using QuotientAddGroup.induction_on with
    | _ x =>
      change QuotientAddGroup.mk' SA (e.symm (e x)) =
        QuotientAddGroup.mk' SA x
      rw [e.symm_apply_apply]
  · intro y
    induction y using QuotientAddGroup.induction_on with
    | _ y =>
      change QuotientAddGroup.mk' SB (e (e.symm y)) =
        QuotientAddGroup.mk' SB y
      rw [e.apply_symm_apply]

private noncomputable def chainHomologyEquiv
    {A₀ : Type u} {A₁ : Type u} {A₂ : Type u}
    {B₀ : Type v} {B₁ : Type v} {B₂ : Type v}
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    (dA : A₁ →+ A₀) (uA : A₂ →+ A₁)
    (dB : B₁ →+ B₀) (uB : B₂ →+ B₁)
    (e₀ : A₀ ≃+ B₀) (e₁ : A₁ ≃+ B₁) (e₂ : A₂ ≃+ B₂)
    (hd : ∀ x, e₀ (dA x) = dB (e₁ x))
    (hu : ∀ x, e₁ (uA x) = uB (e₂ x)) :
    dA.ker ⧸ (uA.range.comap dA.ker.subtype) ≃+
      dB.ker ⧸ (uB.range.comap dB.ker.subtype) := by
  let ec : dA.ker ≃+ dB.ker := {
    toFun := fun x => ⟨e₁ x.1, by
      have hx : dA x.1 = 0 := x.2
      have hh := hd x.1
      rw [hx, map_zero] at hh
      exact hh.symm⟩
    invFun := fun y => ⟨e₁.symm y.1, by
      apply e₀.injective
      rw [hd, map_zero]
      have hy : dB y.1 = 0 := y.2
      simpa only [e₁.apply_symm_apply] using hy⟩
    left_inv := fun x => Subtype.ext (e₁.symm_apply_apply x.1)
    right_inv := fun y => Subtype.ext (e₁.apply_symm_apply y.1)
    map_add' := fun x y => Subtype.ext (e₁.map_add x.1 y.1) }
  apply quotientAddEquiv ec _ _
  intro x
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e₂ y, ?_⟩
    change uB (e₂ y) = e₁ x.1
    rw [← hu y]
    change uA y = x.1 at hy
    exact congrArg e₁ hy
  · rintro ⟨y, hy⟩
    refine ⟨e₂.symm y, ?_⟩
    apply e₁.injective
    rw [hu, e₂.apply_symm_apply]
    exact hy

universe u₁ v₁

variable {V : Type u₁} {B : Type v₁} [DecidableEq V]

section ZeroColumn

variable [LinearOrder V]


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

private noncomputable def freeAbelianEquiv {α β : Type*} (e : α ≃ β) :
    FreeAbelianGroup α ≃+ FreeAbelianGroup β :=
  (FreeAbelianGroup.equivFinsupp α).trans
    ((Finsupp.domCongr e).trans (FreeAbelianGroup.equivFinsupp β).symm)

private theorem freeAbelianEquiv_of {α β : Type*} (e : α ≃ β) (x : α) :
    freeAbelianEquiv e (FreeAbelianGroup.of x) = FreeAbelianGroup.of (e x) := by
  simp [freeAbelianEquiv, Finsupp.domCongr_apply, Finsupp.equivMapDomain_single]

private def zeroSupportEquiv (K : FiniteComplex V) (a : ArcLabels V B) (n : ℤ) :
    RelativeSimplexAt K a 0 n ≃ SimplexAt (goodSubcomplex K a) n where
  toFun σ := ⟨σ.1.1, ⟨⟨σ.1.2.1, by have hp := σ.2; omega⟩, σ.1.2.2⟩⟩
  invFun σ := ⟨⟨σ.1, σ.2.1.1, σ.2.2⟩, by
    change (badVertices a σ.1).card = 0
    have hp : (badVertices a σ.1).card ≤ (0 : ℤ) := σ.2.1.2
    omega⟩
  left_inv σ := by cases σ; rfl
  right_inv σ := by cases σ; rfl

private theorem zero_face_valid (K : FiniteComplex V) (a : ArcLabels V B)
    (n : ℤ) (σ : RelativeSimplexAt K a 0 n) (v : σ.1.1) :
    (σ.1.1.erase v.1 ∈ K ∧
      ((n - 1 = -1 ∧ σ.1.1.erase v.1 = ∅) ∨
        (0 ≤ n - 1 ∧ ((σ.1.1.erase v.1).card : ℤ) = (n - 1) + 1))) ∧
      (badVertices a (σ.1.1.erase v.1)).card = 0 := by
  refine ⟨face_valid K n σ.1 v.2, ?_⟩
  have hzero : badVertices a σ.1.1 = ∅ := Finset.card_eq_zero.mp σ.2
  have hsub := badVertices_mono a (Finset.erase_subset v.1 σ.1.1)
  have : badVertices a (σ.1.1.erase v.1) = ∅ :=
    Finset.subset_empty.mp (by simpa [hzero] using hsub)
  simp [this]

private def zeroFaceAt (K : FiniteComplex V) (a : ArcLabels V B)
    (n : ℤ) (σ : RelativeSimplexAt K a 0 n) (v : σ.1.1) :
    RelativeSimplexAt K a 0 (n - 1) :=
  ⟨⟨σ.1.1.erase v.1, (zero_face_valid K a n σ v).1⟩,
    (zero_face_valid K a n σ v).2⟩

private theorem relativeFaceBoundary_zero_eq (K : FiniteComplex V)
    (a : ArcLabels V B) (n : ℤ) (σ : RelativeSimplexAt K a 0 n) :
    relativeFaceBoundary K a 0 n σ = ∑ v ∈ σ.1.1.attach,
      (-1 : ℤ) ^ (σ.1.1.filter (· < v.1)).card •
        FreeAbelianGroup.of (zeroFaceAt K a n σ v) := by
  classical
  rw [relativeFaceBoundary]
  conv_lhs => rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro v hv
  have hvalid := zero_face_valid K a n σ v
  have hproof :
      (⟨⟨σ.1.1.erase v.1, hvalid.1⟩, hvalid.2⟩ :
        RelativeSimplexAt K a 0 (n - 1)) = zeroFaceAt K a n σ v :=
    Subtype.ext (Subtype.ext rfl)
  exact (dif_pos hvalid).trans (congrArg
    (fun x : RelativeSimplexAt K a 0 (n - 1) =>
      (-1 : ℤ) ^ (σ.1.1.filter (· < v.1)).card • FreeAbelianGroup.of x) hproof)

/-- Proposition 8.7 at `p = 0`: the void `Y₋₁` leaves augmentation intact. -/
theorem relativeChains_zero (K : FiniteComplex V) (a : ArcLabels V B) :
    ∃ e : (n : ℤ) → relativeChains K a 0 n ≃+ chains (goodSubcomplex K a) n,
      ∀ n : ℤ, ∀ c : relativeChains K a 0 n,
        e (n - 1) (relativeBoundary K a 0 n c) =
          boundary (goodSubcomplex K a) n (e n c) := by
  let e : (n : ℤ) → relativeChains K a 0 n ≃+ chains (goodSubcomplex K a) n :=
    fun n => freeAbelianEquiv (zeroSupportEquiv K a n)
  refine ⟨e, ?_⟩
  intro n c
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | neg x hx => simp [map_neg, hx]
  | of x =>
      simp only [relativeBoundary, FreeAbelianGroup.lift_apply_of]
      rw [freeAbelianEquiv_of]
      simp only [boundary, FreeAbelianGroup.lift_apply_of]
      change e (n - 1) (relativeFaceBoundary K a 0 n x) =
        faceBoundary (goodSubcomplex K a) n (zeroSupportEquiv K a n x)
      rw [relativeFaceBoundary_zero_eq, faceBoundary_eq]
      simp only [map_sum, map_zsmul]
      apply Finset.sum_congr
      · rfl
      intro v hv
      congr 1
      change (e (n - 1)) (FreeAbelianGroup.of (zeroFaceAt K a n x v)) =
        FreeAbelianGroup.of (faceAt (goodSubcomplex K a) n
          (zeroSupportEquiv K a n x) v)
      dsimp [e]
      rw [freeAbelianEquiv_of]
      congr 1

set_option maxHeartbeats 2000000

noncomputable abbrev firstPage (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (q : ℤ) : Type u₁ := relativeHomology K a p (p + q)

theorem firstPage_zero (K : FiniteComplex V) (a : ArcLabels V B)
    (h : (∅ : Finset V) ∈ K) (q : ℤ) :
    Nonempty (firstPage K a 0 q ≃+ reducedHomology (goodSubcomplex K a) q) := by
  obtain ⟨e, he⟩ := relativeChains_zero K a
  have hq : q + 1 - 1 = q := by omega
  let uA : relativeChains K a 0 (q + 1) →+ relativeChains K a 0 q :=
    cast (congrArg (fun m : ℤ => relativeChains K a 0 (q + 1) →+
      relativeChains K a 0 m) hq) (relativeBoundary K a 0 (q + 1))
  let uB : chains (goodSubcomplex K a) (q + 1) →+
      chains (goodSubcomplex K a) q :=
    cast (congrArg (fun m : ℤ => chains (goodSubcomplex K a) (q + 1) →+
      chains (goodSubcomplex K a) m) hq)
      (boundary (goodSubcomplex K a) (q + 1))
  have transport (m n : ℤ) (hmn : m = n)
      (fA : relativeChains K a 0 (q + 1) →+ relativeChains K a 0 m)
      (fB : chains (goodSubcomplex K a) (q + 1) →+
        chains (goodSubcomplex K a) m)
      (x : relativeChains K a 0 (q + 1))
      (hc : e m (fA x) = fB (e (q + 1) x)) :
      e n ((cast (congrArg (fun k : ℤ => relativeChains K a 0 (q + 1) →+
        relativeChains K a 0 k) hmn) fA) x) =
      (cast (congrArg (fun k : ℤ => chains (goodSubcomplex K a) (q + 1) →+
        chains (goodSubcomplex K a) k) hmn) fB) (e (q + 1) x) := by
    cases hmn
    exact hc
  have hnat : ∀ x : relativeChains K a 0 (q + 1),
      e q (uA x) = uB (e (q + 1) x) := by
    intro x
    exact transport (q + 1 - 1) q hq _ _ x (he (q + 1) x)
  have hh := chainHomologyEquiv (relativeBoundary K a 0 q) uA
    (boundary (goodSubcomplex K a) q) uB
    (e (q - 1)) (e q) (e (q + 1)) (he q) hnat
  have rangeA (m n : ℤ) (hmn : m = n)
      (f : relativeChains K a 0 (q + 1) →+ relativeChains K a 0 m) :
      (cast (congrArg (fun k : ℤ => relativeChains K a 0 (q + 1) →+
        relativeChains K a 0 k) hmn) f).range =
      Eq.mp (congrArg (fun k : ℤ => AddSubgroup (relativeChains K a 0 k)) hmn)
        f.range := by
    cases hmn
    rfl
  have rangeB (m n : ℤ) (hmn : m = n)
      (f : chains (goodSubcomplex K a) (q + 1) →+
        chains (goodSubcomplex K a) m) :
      (cast (congrArg (fun k : ℤ => chains (goodSubcomplex K a) (q + 1) →+
        chains (goodSubcomplex K a) k) hmn) f).range =
      Eq.mp (congrArg (fun k : ℤ => AddSubgroup
        (chains (goodSubcomplex K a) k)) hmn) f.range := by
    cases hmn
    rfl
  have hrA : uA.range = relativeBoundaries K a 0 q := by
    simpa only [uA, relativeBoundaries] using
      rangeA (q + 1 - 1) q hq (relativeBoundary K a 0 (q + 1))
  have hrB : uB.range = boundaries (goodSubcomplex K a) q := by
    simpa only [uB, boundaries] using
      rangeB (q + 1 - 1) q hq (boundary (goodSubcomplex K a) (q + 1))
  rw [hrA, hrB] at hh
  let idq : relativeHomology K a 0 q ≃+
      relativeHomology K a 0 (0 + q) :=
    AddEquiv.cast (M := fun n : ℤ => relativeHomology K a 0 n)
      (Int.zero_add q).symm
  have hfinal : Nonempty (relativeHomology K a 0 (0 + q) ≃+
      reducedHomology (goodSubcomplex K a) q) := ⟨idq.symm.trans hh⟩
  exact hfinal

end ZeroColumn

end CurveGenusTwo.Filtration
