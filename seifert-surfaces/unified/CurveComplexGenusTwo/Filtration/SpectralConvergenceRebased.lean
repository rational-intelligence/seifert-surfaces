import CurveComplexGenusTwo.Filtration.SpectralDefinitions

namespace CurveGenusTwo.Filtration

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

theorem filteredChains_top (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12) (n : ℤ) :
    filteredChains K a 12 n = ⊤ := by
  have htop := filtration_top K a hcard
  let i := chainInclusion (filtration K a 12) K
    (by intro σ hσ; exact hσ.1) n
  have hrev : K.simplices ⊆ (filtration K a 12).simplices := by
    rw [htop]
  let j := chainInclusion K (filtration K a 12) hrev n
  have hcomp : i.comp j = AddMonoidHom.id (chains K n) := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    change i (j (FreeAbelianGroup.of σ)) = FreeAbelianGroup.of σ
    have hj : j (FreeAbelianGroup.of σ) =
        FreeAbelianGroup.of
          (⟨σ.1, hrev σ.2.1, σ.2.2⟩ : SimplexAt (filtration K a 12) n) :=
      FreeAbelianGroup.lift_apply_of _ _
    rw [hj]
    exact FreeAbelianGroup.lift_apply_of _ _
  change i.range = ⊤
  apply le_antisymm le_top
  intro x _
  exact ⟨j x, congrArg (fun f => f x) hcomp⟩

theorem filteredChains_bottom (K : FiniteComplex V) (a : ArcLabels V B)
    (n : ℤ) : filteredChains K a (-1) n = ⊥ := by
  classical
  haveI : IsEmpty (SimplexAt (filtration K a (-1)) n) := ⟨by
    intro σ
    have h := σ.2.1.2
    omega⟩
  haveI : Subsingleton (chains (filtration K a (-1)) n) := inferInstance
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    have hy : y = 0 := Subsingleton.elim y 0
    simp [hy]
  · exact bot_le

theorem filteredChains_mono (K : FiniteComplex V) (a : ArcLabels V B)
    {p p' : ℤ} (hp : p ≤ p') (n : ℤ) :
    filteredChains K a p n ≤ filteredChains K a p' n := by
  let hpp' : (filtration K a p).simplices ⊆
      (filtration K a p').simplices := by
    intro σ hσ
    exact ⟨hσ.1, le_trans hσ.2 hp⟩
  let hpk : (filtration K a p).simplices ⊆ K.simplices := by
    intro σ hσ
    exact hσ.1
  let hp'k : (filtration K a p').simplices ⊆ K.simplices := by
    intro σ hσ
    exact hσ.1
  let i := chainInclusion (filtration K a p) (filtration K a p') hpp' n
  let j := chainInclusion (filtration K a p') K hp'k n
  let k := chainInclusion (filtration K a p) K hpk n
  have hcomp : j.comp i = k := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    change j (i (FreeAbelianGroup.of σ)) = k (FreeAbelianGroup.of σ)
    have hi : i (FreeAbelianGroup.of σ) =
        FreeAbelianGroup.of
          (⟨σ.1, hpp' σ.2.1, σ.2.2⟩ : SimplexAt (filtration K a p') n) := by
      exact FreeAbelianGroup.lift_apply_of _ _
    have hj : j (FreeAbelianGroup.of
        (⟨σ.1, hpp' σ.2.1, σ.2.2⟩ : SimplexAt (filtration K a p') n)) =
        FreeAbelianGroup.of
          (⟨σ.1, hp'k (hpp' σ.2.1), σ.2.2⟩ : SimplexAt K n) := by
      exact FreeAbelianGroup.lift_apply_of _ _
    have hk : k (FreeAbelianGroup.of σ) =
        FreeAbelianGroup.of
          (⟨σ.1, hpk σ.2.1, σ.2.2⟩ : SimplexAt K n) := by
      exact FreeAbelianGroup.lift_apply_of _ _
    exact (congrArg j hi).trans (hj.trans (hk.symm.trans (by
      rfl)))
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨i y, congrArg (fun f => f y) hcomp ▸ rfl⟩

theorem spectralCycles_mem_filtered (K : FiniteComplex V) (a : ArcLabels V B)
    (r p n : ℤ) {x : chains K n}
    (hx : x ∈ spectralCycles K a r p n) :
    x ∈ filteredChains K a p n := hx.1

theorem spectralCycles_boundary_mem (K : FiniteComplex V) (a : ArcLabels V B)
    (r p n : ℤ) {x : chains K n}
    (hx : x ∈ spectralCycles K a r p n) :
    boundary K n x ∈ filteredChains K a (p - r) (n - 1) := hx.2

theorem filteredChains_mem_spectralNullChains (K : FiniteComplex V)
    (a : ArcLabels V B) (r p n : ℤ) {x : chains K n}
    (hx : x ∈ filteredChains K a (p - 1) n) :
    x ∈ spectralNullChains K a r p n := by
  change x ∈ filteredChains K a (p - 1) n ⊔ _
  exact (le_sup_left :
    filteredChains K a (p - 1) n ≤
      filteredChains K a (p - 1) n ⊔ _) hx

theorem spectralCycles_le_filteredChains (K : FiniteComplex V)
    (a : ArcLabels V B) (r p n : ℤ) :
    spectralCycles K a r p n ≤ filteredChains K a p n := by
  exact inf_le_left

theorem spectralCycles_boundary_mem' (K : FiniteComplex V) (a : ArcLabels V B)
    (r p n : ℤ) :
    (boundary K n) '' (spectralCycles K a r p n : Set (chains K n)) ⊆
      (filteredChains K a (p - r) (n - 1) : Set (chains K (n - 1))) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact spectralCycles_boundary_mem K a r p n hx

theorem spectralNullChains_contains_filteredChains (K : FiniteComplex V)
    (a : ArcLabels V B) (r p n : ℤ) :
    filteredChains K a (p - 1) n ≤ spectralNullChains K a r p n := by
  intro x hx
  exact filteredChains_mem_spectralNullChains K a r p n hx

theorem spectralCycles_top_eq_filteredChains (K : FiniteComplex V)
    (a : ArcLabels V B) (r n : ℤ) :
    spectralCycles K a r 12 n =
      filteredChains K a 12 n ⊓
        (filteredChains K a (12 - r) (n - 1)).comap (boundary K n) := by
  rfl

theorem spectralCycles_bottom_le (K : FiniteComplex V) (a : ArcLabels V B)
    (r n : ℤ) :
    spectralCycles K a r (-1) n ≤ ⊥ := by
  rw [show spectralCycles K a r (-1) n =
      filteredChains K a (-1) n ⊓
        (filteredChains K a (-1 - r) (n - 1)).comap (boundary K n) by rfl]
  exact inf_le_left.trans_eq (filteredChains_bottom K a n)

theorem filteredChains_eq_bot_of_le (K : FiniteComplex V) (a : ArcLabels V B)
    {p : ℤ} (hp : p ≤ -1) (n : ℤ) :
    filteredChains K a p n = ⊥ := by
  apply le_antisymm
  · exact (filteredChains_mono K a hp n).trans_eq (filteredChains_bottom K a n)
  · exact bot_le

theorem filteredChains_eq_top_of_ge (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {p : ℤ} (hp : 12 ≤ p) (n : ℤ) :
    filteredChains K a p n = ⊤ := by
  apply le_antisymm le_top
  exact (filteredChains_top K a hcard n).symm ▸ filteredChains_mono K a hp n

theorem spectralCycles_stable (K : FiniteComplex V) (a : ArcLabels V B)
    {r p n : ℤ} (hr : 13 ≤ r) (hp : p ≤ 12) :
    spectralCycles K a r p n = filteredChains K a p n ⊓ cycles K n := by
  have hbot : filteredChains K a (p - r) (n - 1) = ⊥ :=
    filteredChains_eq_bot_of_le K a (by omega) _
  simp only [spectralCycles, cycles, hbot]
  rfl

theorem spectralCycles_stable_eq (K : FiniteComplex V) (a : ArcLabels V B)
    {r s p n : ℤ} (hr : 13 ≤ r) (hs : 13 ≤ s) (hp : p ≤ 12) :
    spectralCycles K a r p n = spectralCycles K a s p n := by
  rw [spectralCycles_stable K a hr hp, spectralCycles_stable K a hs hp]

theorem spectralCycles_incoming_stable (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {r p n : ℤ} (hr : 13 ≤ r) (hp : 0 ≤ p) :
    spectralCycles K a (r - 1) (p + r - 1) (n + 1) =
      (filteredChains K a p (n + 1 - 1)).comap (boundary K (n + 1)) := by
  have htop : filteredChains K a (p + r - 1) (n + 1) = ⊤ :=
    filteredChains_eq_top_of_ge K a hcard (by omega) _
  have hi : p + r - 1 - (r - 1) = p := by omega
  simp only [spectralCycles, htop, hi, top_inf_eq]

theorem spectralNullChains_stable_eq (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {r s p n : ℤ} (hr : 13 ≤ r) (hs : 13 ≤ s) (hp : 0 ≤ p) :
    spectralNullChains K a r p n = spectralNullChains K a s p n := by
  unfold spectralNullChains
  rw [spectralCycles_incoming_stable K a hcard hr hp,
    spectralCycles_incoming_stable K a hcard hs hp]

theorem spectralPageGroup_stable (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {r s p q : ℤ} (hr : 13 ≤ r) (hs : 13 ≤ s)
    (hp0 : 0 ≤ p) (hp12 : p ≤ 12) :
    spectralPageGroup K a r p q = spectralPageGroup K a s p q := by
  unfold spectralPageGroup
  rw [spectralNullChains_stable_eq K a hcard hr hs hp0]
  rw [spectralCycles_stable_eq K a hr hs hp12]

theorem spectralPageGroup_stable_quotient (K : FiniteComplex V)
    (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {r p q : ℤ} (hr : 13 ≤ r) (hp0 : 0 ≤ p) (hp12 : p ≤ 12) :
    spectralPageGroup K a r p q =
      (↥(filteredChains K a p (p + q) ⊓ cycles K (p + q)) ⧸
        ((spectralNullChains K a 13 p (p + q)).comap
          (filteredChains K a p (p + q) ⊓ cycles K (p + q)).subtype)) := by
  rw [spectralPageGroup_stable K a hcard hr (show 13 ≤ (13 : ℤ) by omega)
    hp0 hp12]
  unfold spectralPageGroup
  rw [spectralCycles_stable K a (show 13 ≤ (13 : ℤ) by omega) hp12]

theorem inducedHomologyFiltration_zero (K : FiniteComplex V) (a : ArcLabels V B)
    (n : ℤ) : inducedHomologyFiltration K a n 0 = ⊥ := by
  apply le_antisymm _ bot_le
  unfold inducedHomologyFiltration
  apply (AddSubgroup.closure_le _).mpr
  intro h hh
  obtain ⟨c, hc, rfl⟩ := hh
  have hc0 : c = 0 := by
    have hsub : Subsingleton (chains (filtration K a (-1)) n) := by
      classical
      haveI : IsEmpty (SimplexAt (filtration K a (-1)) n) := ⟨by
        intro σ
        have h := σ.2.1.2
        omega⟩
      infer_instance
    haveI : Subsingleton (chains (filtration K a (((0 : ℕ) : ℤ) - 1)) n) := by
      simpa using hsub
    exact Subsingleton.elim c 0
  subst c
  change filteredCycleClass K a (((0 : ℕ) : ℤ) - 1) n 0 hc ∈
    (⊥ : AddSubgroup (reducedHomology K n))
  change (QuotientAddGroup.mk' _ (⟨0, by simp⟩ : cycles K n)) = 0
  have hz : (⟨0, by simp⟩ : cycles K n) = 0 := rfl
  rw [hz]
  exact map_zero _

end CurveGenusTwo.Filtration
