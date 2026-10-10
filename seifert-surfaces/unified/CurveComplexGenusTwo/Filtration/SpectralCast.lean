import CurveComplexGenusTwo.Filtration.FiltrationRelative

namespace CurveGenusTwo.Filtration

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

noncomputable def filteredChains (K : FiniteComplex V) (a : ArcLabels V B)
    (p n : ℤ) : AddSubgroup (chains K n) :=
  (chainInclusion (filtration K a p) K (by intro σ hσ; exact hσ.1) n).range

noncomputable def spectralCycles (K : FiniteComplex V) (a : ArcLabels V B)
    (r p n : ℤ) : AddSubgroup (chains K n) :=
  filteredChains K a p n ⊓
    (filteredChains K a (p - r) (n - 1)).comap (boundary K n)

noncomputable def spectralNullChains (K : FiniteComplex V) (a : ArcLabels V B)
    (r p n : ℤ) : AddSubgroup (chains K n) := by
  have hn : n + 1 - 1 = n := by omega
  exact filteredChains K a (p - 1) n ⊔
    Eq.mp (congrArg (fun m : ℤ => AddSubgroup (chains K m)) hn)
      (((boundary K (n + 1)).comp
        (spectralCycles K a (r - 1) (p + r - 1) (n + 1)).subtype).range)

private theorem cast_apply {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) (x : A) :
    (Eq.mp (congrArg (fun k => A →+ F k) h) f) x =
      Eq.mp (congrArg F h) (f x) := by
  cases h
  rfl

private theorem cast_range {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) :
    Eq.mp (congrArg (fun k => AddSubgroup (F k)) h) f.range =
      (Eq.mp (congrArg (fun k => A →+ F k) h) f).range := by
  cases h
  rfl

private theorem cast_comp_range {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A D : Type*} [AddCommGroup A] [AddCommGroup D]
    (f : A →+ F i) (g : D →+ A) :
    Eq.mp (congrArg (fun k => AddSubgroup (F k)) h) (f.comp g).range =
      ((Eq.mp (congrArg (fun k => A →+ F k) h) f).comp g).range := by
  cases h
  rfl

private theorem cast_comp_zero {ι : Type*} {F G : ι → Type*}
    [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (G i)]
    {i j : ι} (h : i = j) {A : Type*} [AddCommGroup A]
    (f : A →+ F i) (g : (k : ι) → F k →+ G k)
    (hz : (g i).comp f = 0) :
    (g j).comp (Eq.mp (congrArg (fun k => A →+ F k) h) f) = 0 := by
  cases h
  exact hz

private theorem cast_subgroup_family {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] (H : (i : ι) → AddSubgroup (F i))
    {i j : ι} (h : i = j) :
    Eq.mp (congrArg (fun k => AddSubgroup (F k)) h) (H i) = H j := by
  cases h
  rfl

private theorem range_comp_comap {A C : Type*} [AddCommGroup A] [AddCommGroup C]
    (f : A →+ C) (H : AddSubgroup C) :
    (f.comp (H.comap f).subtype).range = f.range ⊓ H := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.1, rfl⟩, y.2⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨⟨y, hy⟩, rfl⟩

private theorem cast_comp_comap_range {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A]
    (f : A →+ F i) (H : AddSubgroup (F i)) :
    ((Eq.mp (congrArg (fun k => A →+ F k) h) f).comp
      (H.comap f).subtype).range =
      (Eq.mp (congrArg (fun k => A →+ F k) h) f).range ⊓
        Eq.mp (congrArg (fun k => AddSubgroup (F k)) h) H := by
  cases h
  exact range_comp_comap f H

noncomputable def filteredChainsCast (K : FiniteComplex V) (a : ArcLabels V B)
    (p n : ℤ) : AddSubgroup (chains K n) :=
  (chainInclusion (filtration K a p) K (by intro σ hσ; exact hσ.1) n).range

noncomputable def filteredCyclesCast (K : FiniteComplex V) (a : ArcLabels V B)
    (r p n : ℤ) : AddSubgroup (chains K n) :=
  filteredChainsCast K a p n ⊓
    (filteredChainsCast K a (p - r) (n - 1)).comap (boundary K n)

noncomputable def boundaryNextCast (K : FiniteComplex V) (n : ℤ) :
    chains K (n + 1) →+ chains K n := by
  have hn : n + 1 - 1 = n := by omega
  exact Eq.mp (congrArg (fun m : ℤ => chains K (n + 1) →+ chains K m) hn)
    (boundary K (n + 1))

theorem boundaryNextCast_apply (K : FiniteComplex V) (n : ℤ)
    (x : chains K (n + 1)) :
    boundaryNextCast K n x =
      Eq.mp (congrArg (fun m : ℤ => chains K m)
        (show n + 1 - 1 = n by omega)) (boundary K (n + 1) x) := by
  have hn : n + 1 - 1 = n := by omega
  change (Eq.mp (congrArg (fun m : ℤ => chains K (n + 1) →+ chains K m) hn)
      (boundary K (n + 1))) x = _
  exact cast_apply hn (boundary K (n + 1)) x

theorem boundaryNextCast_range (K : FiniteComplex V) (n : ℤ) :
    (boundaryNextCast K n).range =
      Eq.mp (congrArg (fun m : ℤ => AddSubgroup (chains K m))
        (show n + 1 - 1 = n by omega)) (boundary K (n + 1)).range := by
  have hn : n + 1 - 1 = n := by omega
  change (Eq.mp (congrArg (fun m : ℤ => chains K (n + 1) →+ chains K m) hn)
      (boundary K (n + 1))).range = _
  exact (cast_range hn (boundary K (n + 1))).symm

noncomputable def spectralNullChainsCast (K : FiniteComplex V) (a : ArcLabels V B)
    (r p n : ℤ) : AddSubgroup (chains K n) :=
  filteredChainsCast K a (p - 1) n ⊔
    ((boundaryNextCast K n).comp
      (filteredCyclesCast K a (r - 1) (p + r - 1) (n + 1)).subtype).range

omit [LinearOrder V] in
theorem filteredChainsCast_eq_original (K : FiniteComplex V) (a : ArcLabels V B)
    (p n : ℤ) : filteredChainsCast K a p n = filteredChains K a p n := rfl

theorem filteredCyclesCast_eq_original (K : FiniteComplex V) (a : ArcLabels V B)
    (r p n : ℤ) : filteredCyclesCast K a r p n = spectralCycles K a r p n := rfl

theorem spectralNullChainsCast_eq_source (K : FiniteComplex V) (a : ArcLabels V B)
    (r p n : ℤ) :
    spectralNullChainsCast K a r p n =
      filteredChainsCast K a (p - 1) n ⊔
        Eq.mp (congrArg (fun m : ℤ => AddSubgroup (chains K m))
          (show n + 1 - 1 = n by omega))
          (((boundary K (n + 1)).comp
            (filteredCyclesCast K a (r - 1) (p + r - 1) (n + 1)).subtype).range) := by
  unfold spectralNullChainsCast
  have hn : n + 1 - 1 = n := by omega
  have hcr := cast_comp_range (F := fun m : ℤ => chains K m) hn
    (boundary K (n + 1))
      (filteredCyclesCast K a (r - 1) (p + r - 1) (n + 1)).subtype
  change filteredChainsCast K a (p - 1) n ⊔
      (((boundaryNextCast K n).comp
        (filteredCyclesCast K a (r - 1) (p + r - 1) (n + 1)).subtype).range) = _
  rw [show boundaryNextCast K n =
      Eq.mp (congrArg (fun m : ℤ => chains K (n + 1) →+ chains K m) hn)
        (boundary K (n + 1)) by rfl]
  exact congrArg (fun H : AddSubgroup (chains K n) =>
      filteredChainsCast K a (p - 1) n ⊔ H) hcr.symm

theorem spectralNullChainsCast_eq_original (K : FiniteComplex V) (a : ArcLabels V B)
    (r p n : ℤ) :
    spectralNullChainsCast K a r p n = spectralNullChains K a r p n := by
  rw [spectralNullChainsCast_eq_source]
  rfl

theorem spectralNullChainsCast_mem_boundary_part_iff
    (K : FiniteComplex V) (a : ArcLabels V B) (r p n : ℤ)
    {x : chains K n} :
    x ∈ ((boundaryNextCast K n).comp
      (filteredCyclesCast K a (r - 1) (p + r - 1) (n + 1)).subtype).range ↔
      ∃ y : filteredCyclesCast K a (r - 1) (p + r - 1) (n + 1),
        boundaryNextCast K n y.1 = x := by
  rfl

theorem spectralNullChainsCast_mem_boundary_part_iff_source
    (K : FiniteComplex V) (a : ArcLabels V B) (r p n : ℤ)
    {x : chains K n} :
    x ∈ Eq.mp (congrArg (fun m : ℤ => AddSubgroup (chains K m))
        (show n + 1 - 1 = n by omega))
      (((boundary K (n + 1)).comp
        (filteredCyclesCast K a (r - 1) (p + r - 1) (n + 1)).subtype).range) ↔
      ∃ y : filteredCyclesCast K a (r - 1) (p + r - 1) (n + 1),
        Eq.mp (congrArg (fun m : ℤ => chains K m)
          (show n + 1 - 1 = n by omega))
          (boundary K (n + 1) y.1) = x := by
  have hn : n + 1 - 1 = n := by omega
  have hcr := cast_comp_range (F := fun m : ℤ => chains K m) hn
    (boundary K (n + 1))
      (filteredCyclesCast K a (r - 1) (p + r - 1) (n + 1)).subtype
  rw [hcr]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (spectralNullChainsCast_mem_boundary_part_iff K a r p n).mp hx
    exact ⟨y, (boundaryNextCast_apply K n y.1).symm.trans hy⟩
  · rintro ⟨y, hy⟩
    apply (spectralNullChainsCast_mem_boundary_part_iff K a r p n).mpr
    exact ⟨y, (boundaryNextCast_apply K n y.1).trans hy⟩

private theorem boundaryNextCast_boundary (K : FiniteComplex V) (n : ℤ) :
    (boundary K n).comp (boundaryNextCast K n) = 0 := by
  have hn : n + 1 - 1 = n := by omega
  change (boundary K n).comp
      (Eq.mp (congrArg (fun m : ℤ => chains K (n + 1) →+ chains K m) hn)
        (boundary K (n + 1))) = 0
  exact cast_comp_zero hn (boundary K (n + 1)) (boundary K)
    (boundary_boundary K (n + 1))

theorem spectralNullChainsCast_boundary_part_le_cycles
    (K : FiniteComplex V) (a : ArcLabels V B) (r p n : ℤ) :
    ((boundaryNextCast K n).comp
      (filteredCyclesCast K a (r - 1) (p + r - 1) (n + 1)).subtype).range ≤
      cycles K n := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  change boundary K n (boundaryNextCast K n y.1) = 0
  exact congrArg (fun f => f y.1) (boundaryNextCast_boundary K n)

omit [LinearOrder V] in
theorem filteredChainsCast_eq_top_of_ge
    (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {p : ℤ} (hp : 12 ≤ p) (n : ℤ) :
    filteredChainsCast K a p n = ⊤ := by
  have hfil : filtration K a p = K := by
    apply FiniteComplex.ext
    ext σ
    constructor
    · exact And.left
    · intro hσ
      have hσ12 : σ ∈ filtration K a 12 :=
        (filtration_top K a hcard).symm ▸ hσ
      exact filtration_mono K a hp hσ12
  unfold filteredChainsCast
  let hrev : K.simplices ⊆ (filtration K a p).simplices := by
    rw [hfil]
  let j := chainInclusion K (filtration K a p) hrev n
  let i := chainInclusion (filtration K a p) K
    (by intro σ hσ; exact hσ.1) n
  have hcomp : i.comp j = AddMonoidHom.id (chains K n) := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    change i (j (FreeAbelianGroup.of σ)) = FreeAbelianGroup.of σ
    simp only [i, j, chainInclusion, FreeAbelianGroup.lift_apply_of]
    rfl
  change i.range = ⊤
  apply le_antisymm le_top
  intro x _
  exact ⟨j x, congrArg (fun f => f x) hcomp ▸ rfl⟩

omit [LinearOrder V] in
theorem filteredChainsCast_mono (K : FiniteComplex V) (a : ArcLabels V B)
    {p p' : ℤ} (hpp' : p ≤ p') (n : ℤ) :
    filteredChainsCast K a p n ≤ filteredChainsCast K a p' n := by
  let hpp : (filtration K a p).simplices ⊆
      (filtration K a p').simplices := filtration_mono K a hpp'
  let hi : (filtration K a p).simplices ⊆ K.simplices :=
    fun _ hσ => hσ.1
  let hj : (filtration K a p').simplices ⊆ K.simplices :=
    fun _ hσ => hσ.1
  let f := chainInclusion (filtration K a p) (filtration K a p') hpp n
  let g := chainInclusion (filtration K a p') K hj n
  let k := chainInclusion (filtration K a p) K hi n
  have hcomp : g.comp f = k := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    simp only [f, g, k, chainInclusion, FreeAbelianGroup.lift_apply_of,
      AddMonoidHom.comp_apply]
    rfl
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨f y, congrArg (fun h => h y) hcomp ▸ rfl⟩

theorem boundaries_le_cycles_cast (K : FiniteComplex V) (n : ℤ) :
    boundaries K n ≤ cycles K n := by
  have hb : boundaries K n = (boundaryNextCast K n).range :=
    (boundaryNextCast_range K n).symm
  rw [hb]
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  change boundary K n (boundaryNextCast K n y) = 0
  exact congrArg (fun f => f y) (boundaryNextCast_boundary K n)

theorem filteredCyclesCast_incoming_stable
    (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {r p n : ℤ} (hr : 13 ≤ r) (hp : 0 ≤ p) :
    filteredCyclesCast K a (r - 1) (p + r - 1) (n + 1) =
      (filteredChainsCast K a p (n + 1 - 1)).comap (boundary K (n + 1)) := by
  have htop : filteredChainsCast K a (p + r - 1) (n + 1) = ⊤ :=
    filteredChainsCast_eq_top_of_ge K a hcard (by omega) _
  have hi : p + r - 1 - (r - 1) = p := by omega
  simp only [filteredCyclesCast, htop, hi, top_inf_eq]

theorem spectralNullChainsCast_stable_normal_form
    (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {r p n : ℤ} (hr : 13 ≤ r) (hp : 0 ≤ p) :
    spectralNullChainsCast K a r p n =
      filteredChainsCast K a (p - 1) n ⊔
        (boundaries K n ⊓ filteredChainsCast K a p n) := by
  rw [spectralNullChainsCast_eq_source]
  rw [filteredCyclesCast_incoming_stable K a hcard hr hp]
  have hn : n + 1 - 1 = n := by omega
  rw [cast_comp_range hn (boundary K (n + 1))
    ((filteredChainsCast K a p (n + 1 - 1)).comap
      (boundary K (n + 1))).subtype]
  rw [cast_comp_comap_range hn (boundary K (n + 1))
    (filteredChainsCast K a p (n + 1 - 1))]
  rw [← cast_range hn (boundary K (n + 1))]
  rw [cast_subgroup_family (filteredChainsCast K a p) hn]
  rfl

theorem spectralNullChains_stable_normal_form
    (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {r p n : ℤ} (hr : 13 ≤ r) (hp : 0 ≤ p) :
    spectralNullChains K a r p n =
      filteredChains K a (p - 1) n ⊔
        (boundaries K n ⊓ filteredChains K a p n) := by
  rw [← spectralNullChainsCast_eq_original]
  exact spectralNullChainsCast_stable_normal_form K a hcard hr hp

theorem graded_kernel_iff_null_chains
    {C : Type*} [AddCommGroup C]
    (L F B Z : AddSubgroup C) (hLF : L ≤ F) (hBZ : B ≤ Z)
    (x : ↥(F ⊓ Z)) :
    (QuotientAddGroup.mk' (B.comap Z.subtype))
        (⟨x.1, x.2.2⟩ : Z) ∈
      ((QuotientAddGroup.mk' (B.comap Z.subtype)).comp
        (((L ⊓ Z).subtype).codRestrict Z
          (by intro y; exact y.2.2))).range ↔
      x.1 ∈ L ⊔ (B ⊓ F) := by
  constructor
  · rintro ⟨y, hy⟩
    have heq :
        (QuotientAddGroup.mk' (B.comap Z.subtype))
          (⟨x.1, x.2.2⟩ : Z) =
        (QuotientAddGroup.mk' (B.comap Z.subtype))
          (⟨y.1, y.2.2⟩ : Z) := hy.symm
    have hdiff : x.1 - y.1 ∈ B := by
      have h := (QuotientAddGroup.eq_iff_sub_mem.mp heq)
      exact h
    apply AddSubgroup.mem_sup.mpr
    refine ⟨y.1, y.2.1, x.1 - y.1, ⟨hdiff, ?_⟩, by abel⟩
    exact F.sub_mem x.2.1 (hLF y.2.1)
  · intro hx
    obtain ⟨y, hy, b, hb, hsum⟩ := AddSubgroup.mem_sup.mp hx
    have hyz : y ∈ Z := by
      have hz : x.1 - b ∈ Z := Z.sub_mem x.2.2 (hBZ hb.1)
      have he : y = x.1 - b := by rw [← hsum]; abel
      exact he ▸ hz
    refine ⟨⟨y, hy, hyz⟩, ?_⟩
    have hdiff : x.1 - y ∈ B := by
      rw [← hsum]
      simpa using hb.1
    apply (QuotientAddGroup.eq_iff_sub_mem).mpr
    change y - x.1 ∈ B
    simpa only [neg_sub] using B.neg_mem hdiff

theorem spectralNullChainsCast_kernel_iff
    (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {r p n : ℤ} (hr : 13 ≤ r) (hp : 0 ≤ p)
    (x : ↥(filteredChainsCast K a p n ⊓ cycles K n)) :
    (QuotientAddGroup.mk'
      ((boundaries K n).comap (cycles K n).subtype))
        (⟨x.1, x.2.2⟩ : cycles K n) ∈
      ((QuotientAddGroup.mk'
        ((boundaries K n).comap (cycles K n).subtype)).comp
        (((filteredChainsCast K a (p - 1) n ⊓ cycles K n).subtype).codRestrict
          (cycles K n) (by intro y; exact y.2.2))).range ↔
      x.1 ∈ spectralNullChainsCast K a r p n := by
  rw [spectralNullChainsCast_stable_normal_form K a hcard hr hp]
  exact graded_kernel_iff_null_chains
    (filteredChainsCast K a (p - 1) n)
    (filteredChainsCast K a p n) (boundaries K n) (cycles K n)
    (filteredChainsCast_mono K a (by omega) n)
    (boundaries_le_cycles_cast K n) x

theorem spectralNullChains_kernel_iff
    (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {r p n : ℤ} (hr : 13 ≤ r) (hp : 0 ≤ p)
    (x : ↥(filteredChains K a p n ⊓ cycles K n)) :
    (QuotientAddGroup.mk'
      ((boundaries K n).comap (cycles K n).subtype))
        (⟨x.1, x.2.2⟩ : cycles K n) ∈
      ((QuotientAddGroup.mk'
        ((boundaries K n).comap (cycles K n).subtype)).comp
        (((filteredChains K a (p - 1) n ⊓ cycles K n).subtype).codRestrict
          (cycles K n) (by intro y; exact y.2.2))).range ↔
      x.1 ∈ spectralNullChains K a r p n := by
  rw [← spectralNullChainsCast_eq_original]
  exact spectralNullChainsCast_kernel_iff K a hcard hr hp x

noncomputable def castFilteredHomologyMap
    (K : FiniteComplex V) (a : ArcLabels V B) (p n : ℤ) :
    ↥(filteredChains K a p n ⊓ cycles K n) →+ reducedHomology K n :=
  (QuotientAddGroup.mk' ((boundaries K n).comap (cycles K n).subtype)).comp
    (((filteredChains K a p n ⊓ cycles K n).subtype).codRestrict
      (cycles K n) (by intro x; exact x.2.2))

noncomputable def castHomologyStage
    (K : FiniteComplex V) (a : ArcLabels V B) (p n : ℤ) :
    AddSubgroup (reducedHomology K n) :=
  (castFilteredHomologyMap K a p n).range

theorem castHomologyStage_mono
    (K : FiniteComplex V) (a : ArcLabels V B)
    {p p' : ℤ} (hpp' : p ≤ p') (n : ℤ) :
    castHomologyStage K a p n ≤ castHomologyStage K a p' n := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨⟨y.1, ⟨filteredChainsCast_mono K a hpp' n y.2.1, y.2.2⟩⟩, ?_⟩
  rfl

noncomputable def castGradedHomologyMap
    (K : FiniteComplex V) (a : ArcLabels V B) (p n : ℤ) :
    ↥(filteredChains K a p n ⊓ cycles K n) →+
      (castHomologyStage K a p n ⧸
        (castHomologyStage K a (p - 1) n).comap
          (castHomologyStage K a p n).subtype) :=
  (QuotientAddGroup.mk' _).comp
    ((castFilteredHomologyMap K a p n).codRestrict
      (castHomologyStage K a p n) (by intro x; exact ⟨x, rfl⟩))

theorem castGradedHomologyMap_ker_eq_spectralNullChains
    (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    {r p n : ℤ} (hr : 13 ≤ r) (hp : 0 ≤ p) :
    (castGradedHomologyMap K a p n).ker =
      (spectralNullChains K a r p n).comap
        (filteredChains K a p n ⊓ cycles K n).subtype := by
  ext x
  change castGradedHomologyMap K a p n x = 0 ↔
    x.1 ∈ spectralNullChains K a r p n
  unfold castGradedHomologyMap
  rw [AddMonoidHom.comp_apply, ← AddMonoidHom.mem_ker,
    QuotientAddGroup.ker_mk']
  exact spectralNullChains_kernel_iff K a hcard hr hp x

end CurveGenusTwo.Filtration
