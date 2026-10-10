import CurveComplexGenusTwo.Filtration.SpectralConvergenceRebased

namespace CurveGenusTwo.Filtration

universe u v
variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

private theorem chainInclusion_of_eq (K L : FiniteComplex V)
    (h : K.simplices ⊆ L.simplices) (heq : K = L) (n : ℤ)
    (c : chains K n) :
    chainInclusion K L h n c = heq ▸ c := by
  subst L
  have hi : chainInclusion K K h n = AddMonoidHom.id (chains K n) := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    exact FreeAbelianGroup.lift_apply_of _ _
  exact congrArg (fun f => f c) hi

private theorem all_cycles_lift_of_eq (K L : FiniteComplex V)
    (h : K.simplices ⊆ L.simplices) (heq : K = L) (n : ℤ)
    (z : cycles L n) :
    ∃ c : chains K n, ∃ hc : boundary K n c = 0,
      (⟨chainInclusion K L h n c, by
        subst L
        change boundary K n (chainInclusion K K h n c) = 0
        simpa [chainInclusion_of_eq] using hc⟩ : cycles L n) = z := by
  subst L
  refine ⟨z.1, z.2, ?_⟩
  apply Subtype.ext
  simpa only [chainInclusion_of_eq]

theorem inducedHomologyFiltration_top (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12) (n : ℤ) :
    inducedHomologyFiltration K a n 13 = ⊤ := by
  apply le_antisymm le_top
  intro x _
  induction x using Quotient.inductionOn with
  | _ z =>
    have htop : filtration K a 12 = K := filtration_top K a hcard
    have hp : ((13 : ℕ) : ℤ) - 1 = 12 := by norm_num
    let hinc : (filtration K a 12).simplices ⊆ K.simplices := by
      intro σ hσ
      exact hσ.1
    obtain ⟨c, hc, he⟩ := all_cycles_lift_of_eq
      (filtration K a 12) K hinc htop n z
    unfold inducedHomologyFiltration
    apply AddSubgroup.subset_closure
    refine ⟨c, hc, ?_⟩
    unfold filteredCycleClass
    exact congrArg (QuotientAddGroup.mk' _) he

noncomputable def filteredCycleInclusion (K : FiniteComplex V) (a : ArcLabels V B)
    (p n : ℤ) : cycles (filtration K a p) n →+ cycles K n :=
  ((chainInclusion (filtration K a p) K
    (by intro σ hσ; exact hσ.1) n).comp
      (cycles (filtration K a p) n).subtype).codRestrict
    (cycles K n) (by
      intro c
      exact filteredCycle_inclusion_isCycle K a p n c.1 c.2)

noncomputable def filteredHomologyMap (K : FiniteComplex V) (a : ArcLabels V B)
    (p n : ℤ) : cycles (filtration K a p) n →+ reducedHomology K n :=
  (QuotientAddGroup.mk' _).comp (filteredCycleInclusion K a p n)

theorem filteredHomologyMap_apply (K : FiniteComplex V) (a : ArcLabels V B)
    (p n : ℤ) (c : cycles (filtration K a p) n) :
    filteredHomologyMap K a p n c = filteredCycleClass K a p n c.1 c.2 := by
  rfl

theorem inducedHomologyFiltration_eq_range (K : FiniteComplex V) (a : ArcLabels V B)
    (n : ℤ) (p : ℕ) :
    inducedHomologyFiltration K a n p =
      (filteredHomologyMap K a ((p : ℤ) - 1) n).range := by
  apply le_antisymm
  · unfold inducedHomologyFiltration
    apply (AddSubgroup.closure_le _).mpr
    intro h hh
    obtain ⟨c, hc, rfl⟩ := hh
    exact ⟨⟨c, hc⟩, filteredHomologyMap_apply K a _ n ⟨c, hc⟩⟩
  · intro h hh
    obtain ⟨c, rfl⟩ := hh
    apply AddSubgroup.subset_closure
    exact ⟨c.1, c.2, (filteredHomologyMap_apply K a _ n c).symm⟩

private theorem filtration_filtration_eq (K : FiniteComplex V) (a : ArcLabels V B)
    {p p' : ℤ} (hpp' : p ≤ p') :
    filtration (filtration K a p') a p = filtration K a p := by
  apply FiniteComplex.ext
  ext σ
  constructor
  · intro hσ
    exact ⟨hσ.1.1, hσ.2⟩
  · intro hσ
    exact ⟨⟨hσ.1, le_trans hσ.2 hpp'⟩, hσ.2⟩

private theorem chainInclusion_comp (A B C : FiniteComplex V)
    (hab : A.simplices ⊆ B.simplices)
    (hbc : B.simplices ⊆ C.simplices)
    (hac : A.simplices ⊆ C.simplices) (n : ℤ) :
    (chainInclusion B C hbc n).comp (chainInclusion A B hab n) =
      chainInclusion A C hac n := by
  apply FreeAbelianGroup.lift_ext
  intro σ
  simp only [AddMonoidHom.comp_apply, chainInclusion, FreeAbelianGroup.lift_apply_of]
  rfl

private theorem boundary_zero_transport (A B : FiniteComplex V)
    (heq : A = B) (n : ℤ) (c : chains B n)
    (hc : boundary B n c = 0) :
    boundary A n (heq.symm ▸ c) = 0 := by
  subst B
  exact hc

private theorem chainInclusion_transport (A B C : FiniteComplex V)
    (heq : A = B) (ha : A.simplices ⊆ C.simplices)
    (hb : B.simplices ⊆ C.simplices) (n : ℤ) (c : chains B n) :
    chainInclusion A C ha n (heq.symm ▸ c) =
      chainInclusion B C hb n c := by
  subst B
  rfl

private theorem filtered_cycle_mono_lift (K : FiniteComplex V) (a : ArcLabels V B)
    {p p' : ℤ} (hpp' : p ≤ p') (n : ℤ)
    (c : cycles (filtration K a p) n) :
    ∃ c' : cycles (filtration K a p') n,
      chainInclusion (filtration K a p') K
        (by intro σ hσ; exact hσ.1) n c'.1 =
      chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) n c.1 := by
  let L := filtration K a p'
  have hfil : filtration L a p = filtration K a p :=
    filtration_filtration_eq K a hpp'
  let d : chains (filtration L a p) n := hfil.symm ▸ c.1
  have hd : boundary (filtration L a p) n d = 0 := by
    exact boundary_zero_transport _ _ hfil n c.1 c.2
  let j : chains L n := chainInclusion (filtration L a p) L
    (by intro σ hσ; exact hσ.1) n d
  have hj : j ∈ cycles L n :=
    filteredCycle_inclusion_isCycle L a p n d hd
  refine ⟨⟨j, hj⟩, ?_⟩
  change chainInclusion L K (by intro σ hσ; exact hσ.1) n j =
    chainInclusion (filtration K a p) K (by intro σ hσ; exact hσ.1) n c.1
  have hcomp := chainInclusion_comp (filtration L a p) L K
    (by intro σ hσ; exact hσ.1)
    (by intro σ hσ; exact hσ.1)
    (by intro σ hσ; exact hσ.1.1) n
  calc
    chainInclusion L K (by intro σ hσ; exact hσ.1) n j =
        chainInclusion (filtration L a p) K
          (by intro σ hσ; exact hσ.1.1) n d := by
            exact congrArg (fun f => f d) hcomp
    _ = chainInclusion (filtration K a p) K
          (by intro σ hσ; exact hσ.1) n c.1 :=
      chainInclusion_transport _ _ K hfil _ _ n c.1

theorem inducedHomologyFiltration_mono (K : FiniteComplex V) (a : ArcLabels V B)
    (n : ℤ) {p p' : ℕ} (hpp' : p ≤ p') :
    inducedHomologyFiltration K a n p ≤ inducedHomologyFiltration K a n p' := by
  rw [inducedHomologyFiltration_eq_range, inducedHomologyFiltration_eq_range]
  intro x hx
  obtain ⟨c, rfl⟩ := hx
  have hle : ((p : ℤ) - 1) ≤ ((p' : ℤ) - 1) := by omega
  obtain ⟨c', he⟩ := filtered_cycle_mono_lift K a hle n c
  refine ⟨c', ?_⟩
  unfold filteredHomologyMap filteredCycleInclusion
  apply congrArg (QuotientAddGroup.mk' _)
  apply Subtype.ext
  exact he

noncomputable def filteredHomologyToStage (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    cycles (filtration K a p) n →+
      inducedHomologyFiltration K a n (p + 1) :=
  (filteredHomologyMap K a p n).codRestrict
    (inducedHomologyFiltration K a n (p + 1)) (by
      intro c
      rw [inducedHomologyFiltration_eq_range]
      have hp : (((p + 1 : ℕ) : ℤ) - 1) = (p : ℤ) := by omega
      rw [hp]
      exact ⟨c, rfl⟩)

noncomputable def gradedHomologyMap (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    cycles (filtration K a p) n →+
      (inducedHomologyFiltration K a n (p + 1) ⧸
        (inducedHomologyFiltration K a n p).comap
          (inducedHomologyFiltration K a n (p + 1)).subtype) :=
  (QuotientAddGroup.mk' _).comp (filteredHomologyToStage K a p n)

theorem gradedHomologyMap_surjective (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    Function.Surjective (gradedHomologyMap K a p n) := by
  intro y
  induction y using QuotientAddGroup.induction_on with
  | _ z =>
    have hz : z.1 ∈ (filteredHomologyMap K a p n).range := by
      have heq := inducedHomologyFiltration_eq_range K a n (p + 1)
      have hz' : z.1 ∈
          (filteredHomologyMap K a (((p + 1 : ℕ) : ℤ) - 1) n).range :=
        Eq.mp (congrArg (fun H : AddSubgroup (reducedHomology K n) => z.1 ∈ H)
          heq) z.2
      have hp : (((p + 1 : ℕ) : ℤ) - 1) = (p : ℤ) := by omega
      rw [hp] at hz'
      exact hz'
    obtain ⟨c, hc⟩ := hz
    refine ⟨c, ?_⟩
    unfold gradedHomologyMap filteredHomologyToStage
    apply congrArg (QuotientAddGroup.mk' _)
    apply Subtype.ext
    exact hc

theorem gradedHomologyMap_ker (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    (gradedHomologyMap K a p n).ker =
      (inducedHomologyFiltration K a n p).comap
        (filteredHomologyMap K a p n) := by
  ext c
  simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_comap]
  change ((QuotientAddGroup.mk' _).comp
    (filteredHomologyToStage K a p n)) c = 0 ↔
      filteredHomologyMap K a p n c ∈ inducedHomologyFiltration K a n p
  rw [AddMonoidHom.comp_apply]
  have hk := QuotientAddGroup.ker_mk'
    ((inducedHomologyFiltration K a n p).comap
      (inducedHomologyFiltration K a n (p + 1)).subtype)
  rw [← AddMonoidHom.mem_ker, hk]
  rfl

noncomputable def gradedHomologyFirstIso (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    (cycles (filtration K a p) n ⧸
      (inducedHomologyFiltration K a n p).comap
        (filteredHomologyMap K a p n)) ≃+
      (inducedHomologyFiltration K a n (p + 1) ⧸
        (inducedHomologyFiltration K a n p).comap
          (inducedHomologyFiltration K a n (p + 1)).subtype) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (gradedHomologyMap_ker K a p n).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (gradedHomologyMap K a p n) (gradedHomologyMap_surjective K a p n))

private theorem freeAbelian_lift_of_injective {α β : Type*}
    (f : α → β) (hf : Function.Injective f) :
    Function.Injective (FreeAbelianGroup.lift
      (fun a : α => FreeAbelianGroup.of (f a))) := by
  classical
  by_cases hα : Nonempty α
  · let g : β → α := fun b =>
      if hb : ∃ a, f a = b then Classical.choose hb else Classical.choice hα
    have hgf : ∀ a : α, g (f a) = a := by
      intro a
      dsimp [g]
      rw [dif_pos ⟨a, rfl⟩]
      exact hf (Classical.choose_spec (show ∃ x, f x = f a from ⟨a, rfl⟩))
    let F : FreeAbelianGroup α →+ FreeAbelianGroup β :=
      FreeAbelianGroup.lift (fun a => FreeAbelianGroup.of (f a))
    let G : FreeAbelianGroup β →+ FreeAbelianGroup α :=
      FreeAbelianGroup.lift (fun b => FreeAbelianGroup.of (g b))
    have hcomp : G.comp F = AddMonoidHom.id (FreeAbelianGroup α) := by
      apply FreeAbelianGroup.lift_ext
      intro a
      change G (F (FreeAbelianGroup.of a)) = FreeAbelianGroup.of a
      simp only [F, G, FreeAbelianGroup.lift_apply_of, hgf]
    intro x y hxy
    change F x = F y at hxy
    calc
      x = (G.comp F) x := (congrArg (fun H => H x) hcomp).symm
      _ = (G.comp F) y := congrArg G hxy
      _ = y := congrArg (fun H => H y) hcomp
  · haveI : IsEmpty α := not_nonempty_iff.mp hα
    haveI : Subsingleton (FreeAbelianGroup α) := inferInstance
    intro x y _
    exact Subsingleton.elim x y

private theorem chainInclusion_injective (A B : FiniteComplex V)
    (h : A.simplices ⊆ B.simplices) (n : ℤ) :
    Function.Injective (chainInclusion A B h n) := by
  let f : SimplexAt A n → SimplexAt B n :=
    fun σ => ⟨σ.1, h σ.2.1, σ.2.2⟩
  have hf : Function.Injective f := by
    intro σ τ he
    have hv : σ.1 = τ.1 := congrArg (fun z : SimplexAt B n => z.1) he
    exact Subtype.ext hv
  exact freeAbelian_lift_of_injective f hf

private theorem face_valid_for_inclusion_aux (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) {v : V} (hv : v ∈ σ.1) :
    σ.1.erase v ∈ K ∧
      ((n - 1 = -1 ∧ σ.1.erase v = ∅) ∨
        (0 ≤ n - 1 ∧ ((σ.1.erase v).card : ℤ) = (n - 1) + 1)) := by
  classical
  have hmem : σ.1.erase v ∈ K := K.down_closed (Finset.erase_subset v σ.1) σ.2.1
  refine ⟨hmem, ?_⟩
  rcases σ.2.2 with hneg | hpos
  · exact False.elim (by simpa [hneg.2] using hv)
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

private theorem chainInclusion_boundary_aux (A B : FiniteComplex V)
    (h : A.simplices ⊆ B.simplices) (n : ℤ) :
    (boundary B n).comp (chainInclusion A B h n) =
      (chainInclusion A B h (n - 1)).comp (boundary A n) := by
  classical
  apply FreeAbelianGroup.lift_ext
  intro σ
  change {s : Finset V // s ∈ A ∧
    ((n = -1 ∧ s = ∅) ∨ (0 ≤ n ∧ (s.card : ℤ) = n + 1))} at σ
  let τ : SimplexAt B n := ⟨σ.1, h σ.2.1, σ.2.2⟩
  change {s : Finset V // s ∈ B ∧
    ((n = -1 ∧ s = ∅) ∨ (0 ≤ n ∧ (s.card : ℤ) = n + 1))} at τ
  change boundary B n (chainInclusion A B h n (FreeAbelianGroup.of σ)) =
    chainInclusion A B h (n - 1) (boundary A n (FreeAbelianGroup.of σ))
  have hincl : chainInclusion A B h n (FreeAbelianGroup.of σ) =
      FreeAbelianGroup.of τ := FreeAbelianGroup.lift_apply_of _ _
  rw [hincl]
  have hleft : boundary B n (FreeAbelianGroup.of τ) = faceBoundary B n τ :=
    FreeAbelianGroup.lift_apply_of _ _
  have hright : boundary A n (FreeAbelianGroup.of σ) = faceBoundary A n σ :=
    FreeAbelianGroup.lift_apply_of _ _
  refine hleft.trans ?_
  refine Eq.trans ?_ (congrArg (chainInclusion A B h (n - 1)) hright.symm)
  unfold faceBoundary
  rw [map_sum]
  unfold chains SimplexAt at *
  apply Finset.sum_congr rfl
  intro v hv
  have hA := face_valid_for_inclusion_aux A n σ hv
  have hB : σ.1.erase v ∈ B ∧
      ((n - 1 = -1 ∧ σ.1.erase v = ∅) ∨
        (0 ≤ n - 1 ∧ ((σ.1.erase v).card : ℤ) = (n - 1) + 1)) :=
    ⟨h hA.1, hA.2⟩
  dsimp only [τ]
  simp only [dif_pos hB, dif_pos hA]
  have hgen : chainInclusion A B h (n - 1)
      (FreeAbelianGroup.of
        (⟨σ.1.erase v, hA⟩ : SimplexAt A (n - 1))) =
      FreeAbelianGroup.of
        (⟨σ.1.erase v, hB⟩ : SimplexAt B (n - 1)) := by
    exact FreeAbelianGroup.lift_apply_of _ _
  have hz := (chainInclusion A B h (n - 1)).map_zsmul
    ((-1 : ℤ) ^ (σ.1.filter (· < v)).card)
    (FreeAbelianGroup.of (⟨σ.1.erase v, hA⟩ : SimplexAt A (n - 1)))
  rw [hgen] at hz
  exact hz.symm

theorem filteredChain_cycle_iff_ambient (K : FiniteComplex V) (a : ArcLabels V B)
    (p n : ℤ) (c : chains (filtration K a p) n) :
    boundary (filtration K a p) n c = 0 ↔
      boundary K n
        (chainInclusion (filtration K a p) K
          (by intro σ hσ; exact hσ.1) n c) = 0 := by
  have hnat := congrArg (fun f => f c)
    (chainInclusion_boundary_aux (filtration K a p) K
      (by intro σ hσ; exact hσ.1) n)
  constructor
  · intro hc
    simpa [hc] using hnat
  · intro hc
    have hzero : chainInclusion (filtration K a p) K
        (by intro σ hσ; exact hσ.1) (n - 1)
        (boundary (filtration K a p) n c) = 0 := by
      simpa [hc] using hnat.symm
    exact chainInclusion_injective (filtration K a p) K
      (by intro σ hσ; exact hσ.1) (n - 1) (by simpa using hzero)

noncomputable def filteredCyclesToAmbient (K : FiniteComplex V)
    (a : ArcLabels V B) (p n : ℤ) :
    cycles (filtration K a p) n →+
      ↥(filteredChains K a p n ⊓ cycles K n) :=
  ((chainInclusion (filtration K a p) K
    (by intro σ hσ; exact hσ.1) n).comp
      (cycles (filtration K a p) n).subtype).codRestrict
    (filteredChains K a p n ⊓ cycles K n) (by
      intro c
      exact ⟨⟨c.1, rfl⟩,
        filteredCycle_inclusion_isCycle K a p n c.1 c.2⟩)

theorem filteredCyclesToAmbient_bijective (K : FiniteComplex V)
    (a : ArcLabels V B) (p n : ℤ) :
    Function.Bijective (filteredCyclesToAmbient K a p n) := by
  constructor
  · intro c d he
    apply Subtype.ext
    apply chainInclusion_injective (filtration K a p) K
      (by intro σ hσ; exact hσ.1) n
    exact congrArg Subtype.val he
  · intro x
    obtain ⟨c, hc⟩ := x.2.1
    have hc0 : boundary (filtration K a p) n c = 0 := by
      apply (filteredChain_cycle_iff_ambient K a p n c).2
      rw [hc]
      exact x.2.2
    refine ⟨⟨c, hc0⟩, ?_⟩
    apply Subtype.ext
    exact hc

noncomputable def filteredCyclesAmbientEquiv (K : FiniteComplex V)
    (a : ArcLabels V B) (p n : ℤ) :
    cycles (filtration K a p) n ≃+
      ↥(filteredChains K a p n ⊓ cycles K n) :=
  AddEquiv.ofBijective (filteredCyclesToAmbient K a p n)
    (filteredCyclesToAmbient_bijective K a p n)

theorem filteredCyclesAmbientEquiv_class (K : FiniteComplex V)
    (a : ArcLabels V B) (p n : ℤ)
    (c : cycles (filtration K a p) n) :
    (QuotientAddGroup.mk' _)
      (⟨(filteredCyclesAmbientEquiv K a p n c).1,
        (filteredCyclesAmbientEquiv K a p n c).2.2⟩ : cycles K n) =
      filteredHomologyMap K a p n c := by
  rfl

noncomputable def ambientGradedHomologyMap (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    ↥(filteredChains K a p n ⊓ cycles K n) →+
      (inducedHomologyFiltration K a n (p + 1) ⧸
        (inducedHomologyFiltration K a n p).comap
          (inducedHomologyFiltration K a n (p + 1)).subtype) :=
  (gradedHomologyMap K a p n).comp
    (filteredCyclesAmbientEquiv K a p n).symm.toAddMonoidHom

theorem ambientGradedHomologyMap_surjective (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    Function.Surjective (ambientGradedHomologyMap K a p n) := by
  intro y
  obtain ⟨c, hc⟩ := gradedHomologyMap_surjective K a p n y
  refine ⟨filteredCyclesAmbientEquiv K a p n c, ?_⟩
  unfold ambientGradedHomologyMap
  change gradedHomologyMap K a p n
      ((filteredCyclesAmbientEquiv K a p n).symm
        (filteredCyclesAmbientEquiv K a p n c)) = y
  simpa using hc

theorem ambientGradedHomologyMap_ker (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    (ambientGradedHomologyMap K a p n).ker =
      (inducedHomologyFiltration K a n p).comap
        ((filteredHomologyMap K a p n).comp
          (filteredCyclesAmbientEquiv K a p n).symm.toAddMonoidHom) := by
  ext x
  simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_comap]
  change gradedHomologyMap K a p n
      ((filteredCyclesAmbientEquiv K a p n).symm x) = 0 ↔
    filteredHomologyMap K a p n
      ((filteredCyclesAmbientEquiv K a p n).symm x) ∈
        inducedHomologyFiltration K a n p
  rw [← AddMonoidHom.mem_ker, gradedHomologyMap_ker]
  rfl

noncomputable def ambientGradedHomologyFirstIso (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    (↥(filteredChains K a p n ⊓ cycles K n) ⧸
      (inducedHomologyFiltration K a n p).comap
        ((filteredHomologyMap K a p n).comp
          (filteredCyclesAmbientEquiv K a p n).symm.toAddMonoidHom)) ≃+
      (inducedHomologyFiltration K a n (p + 1) ⧸
        (inducedHomologyFiltration K a n p).comap
          (inducedHomologyFiltration K a n (p + 1)).subtype) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (ambientGradedHomologyMap_ker K a p n).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (ambientGradedHomologyMap K a p n)
        (ambientGradedHomologyMap_surjective K a p n))

end CurveGenusTwo.Filtration
