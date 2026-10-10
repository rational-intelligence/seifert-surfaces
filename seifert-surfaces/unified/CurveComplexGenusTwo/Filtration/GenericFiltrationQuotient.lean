import CurveComplexGenusTwo.Filtration.FilteredComplexCategory

namespace CurveGenusTwo.Filtration

open CategoryTheory CategoryTheory.Limits

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

private theorem cast_apply {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) (x : A) :
    (Eq.mp (congrArg (fun k => A →+ F k) h) f) x =
      Eq.mp (congrArg F h) (f x) := by
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

private theorem cast_zero {ι : Type*} {F : ι → Type*}
    [∀ i, Zero (F i)] {i j : ι} (h : i = j) :
    Eq.mp (congrArg F h) (0 : F i) = 0 := by
  cases h
  rfl

private theorem cast_map_apply {ι : Type*} {F G : ι → Type*}
    [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (G i)]
    {i j : ι} (h : i = j)
    (f : (k : ι) → F k →+ G k) (x : F i) :
    Eq.mp (congrArg G h) (f i x) =
      f j (Eq.mp (congrArg F h) x) := by
  cases h
  rfl

noncomputable abbrev genericQuotient (K : FiniteComplex V)
    (a : ArcLabels V B) (p q : ℕ) (hpq : p ≤ q) (n : ℤ) : Type u :=
  (chains (filtration K a q) n) ⧸
    (chainInclusion (filtration K a p) (filtration K a q)
      (filtration_mono K a (by omega)) n).range

noncomputable def genericQuotientBoundary (K : FiniteComplex V)
    (a : ArcLabels V B) (p q : ℕ) (hpq : p ≤ q) (n : ℤ) :
    genericQuotient K a p q hpq n →+
      genericQuotient K a p q hpq (n - 1) := by
  let I (m : ℤ) := chainInclusion (filtration K a p) (filtration K a q)
    (filtration_mono K a (by omega)) m
  let Q (m : ℤ) := QuotientAddGroup.mk' (I m).range
  have hle : (I n).range ≤
      ((Q (n - 1)).comp (boundary (filtration K a q) n)).ker := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    have hnat := congrArg (fun f => f y)
      (chainInclusion_boundary (filtration K a p) (filtration K a q)
        (filtration_mono K a (by omega)) n)
    change Q (n - 1) (boundary (filtration K a q) n (I n y)) = 0
    rw [show boundary (filtration K a q) n (I n y) =
      I (n - 1) (boundary (filtration K a p) n y) from hnat]
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨_, rfl⟩
  exact QuotientAddGroup.lift (I n).range
    ((Q (n - 1)).comp (boundary (filtration K a q) n)) hle

private theorem genericQuotientBoundary_desc (K : FiniteComplex V)
    (a : ArcLabels V B) (p q : ℕ) (hpq : p ≤ q) (n : ℤ)
    (c : chains (filtration K a q) n) :
    genericQuotientBoundary K a p q hpq n (QuotientAddGroup.mk' _ c) =
      QuotientAddGroup.mk' _ (boundary (filtration K a q) n c) := by
  rfl

private theorem genericQuotientBoundary_sq (K : FiniteComplex V)
    (a : ArcLabels V B) (p q : ℕ) (hpq : p ≤ q) (n : ℤ) :
    (genericQuotientBoundary K a p q hpq (n - 1)).comp
      (genericQuotientBoundary K a p q hpq n) = 0 := by
  apply AddMonoidHom.ext
  intro c
  induction c using QuotientAddGroup.induction_on with
  | _ c =>
    change genericQuotientBoundary K a p q hpq (n - 1)
      (genericQuotientBoundary K a p q hpq n (QuotientAddGroup.mk' _ c)) = 0
    rw [genericQuotientBoundary_desc K a p q hpq n c,
      genericQuotientBoundary_desc K a p q hpq (n - 1)
        (boundary (filtration K a q) n c)]
    have h := congrArg (fun f => f c)
      (boundary_boundary (filtration K a q) n)
    have hz : boundary (filtration K a q) (n - 1)
        (boundary (filtration K a q) n c) = 0 := by
      simpa only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] using h
    rw [hz, map_zero]

private noncomputable def genericQuotientBoundaryNextCast (K : FiniteComplex V)
    (a : ArcLabels V B) (p q : ℕ) (hpq : p ≤ q) (n : ℤ) :
    genericQuotient K a p q hpq (n + 1) →+
      genericQuotient K a p q hpq n := by
  have hn : n + 1 - 1 = n := by omega
  exact Eq.mp (congrArg (fun m : ℤ =>
    genericQuotient K a p q hpq (n + 1) →+ genericQuotient K a p q hpq m) hn)
    (genericQuotientBoundary K a p q hpq (n + 1))

private theorem genericQuotientBoundaryNextCast_apply (K : FiniteComplex V)
    (a : ArcLabels V B) (p q : ℕ) (hpq : p ≤ q) (n : ℤ)
    (x : genericQuotient K a p q hpq (n + 1)) :
    genericQuotientBoundaryNextCast K a p q hpq n x =
      Eq.mp (congrArg (genericQuotient K a p q hpq)
        (show n + 1 - 1 = n by omega))
        (genericQuotientBoundary K a p q hpq (n + 1) x) := by
  have hn : n + 1 - 1 = n := by omega
  change (Eq.mp (congrArg (fun m : ℤ =>
    genericQuotient K a p q hpq (n + 1) →+ genericQuotient K a p q hpq m) hn)
    (genericQuotientBoundary K a p q hpq (n + 1))) x = _
  exact cast_apply hn (genericQuotientBoundary K a p q hpq (n + 1)) x

private theorem genericQuotientBoundaryNextCast_sq (K : FiniteComplex V)
    (a : ArcLabels V B) (p q : ℕ) (hpq : p ≤ q) (n : ℤ) :
    (genericQuotientBoundaryNextCast K a p q hpq n).comp
      (genericQuotientBoundaryNextCast K a p q hpq (n + 1)) = 0 := by
  have hn : n + 1 - 1 = n := by omega
  have hn' : (n + 1) + 1 - 1 = n + 1 := by omega
  have hsq : (genericQuotientBoundary K a p q hpq (n + 1)).comp
      (genericQuotientBoundaryNextCast K a p q hpq (n + 1)) = 0 := by
    change (genericQuotientBoundary K a p q hpq (n + 1)).comp
      (Eq.mp (congrArg (fun m : ℤ =>
        genericQuotient K a p q hpq ((n + 1) + 1) →+
          genericQuotient K a p q hpq m) hn')
          (genericQuotientBoundary K a p q hpq ((n + 1) + 1))) = 0
    exact cast_comp_zero hn'
      (genericQuotientBoundary K a p q hpq ((n + 1) + 1))
      (genericQuotientBoundary K a p q hpq)
      (genericQuotientBoundary_sq K a p q hpq ((n + 1) + 1))
  apply AddMonoidHom.ext
  intro x
  have hzero := congrArg (fun f => f x) hsq
  change genericQuotientBoundaryNextCast K a p q hpq n
    (genericQuotientBoundaryNextCast K a p q hpq (n + 1) x) = 0
  rw [genericQuotientBoundaryNextCast_apply K a p q hpq n]
  have hz : genericQuotientBoundary K a p q hpq (n + 1)
      (genericQuotientBoundaryNextCast K a p q hpq (n + 1) x) = 0 := by
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] using hzero
  rw [hz]
  exact cast_zero (F := genericQuotient K a p q hpq) hn

noncomputable def genericQuotientComplex (K : FiniteComplex V)
    (a : ArcLabels V B) (p q : ℕ) (hpq : p ≤ q) :
    ChainComplex (ModuleCat.{u} ℤ) ℤ :=
  ChainComplex.of
    (fun n => ModuleCat.of ℤ (genericQuotient K a p q hpq n))
    (fun n => ModuleCat.ofHom (AddMonoidHom.toIntLinearMap
      (genericQuotientBoundaryNextCast K a p q hpq n)))
    (by
      intro n
      ext c
      have h := congrArg (fun f => f c)
        (genericQuotientBoundaryNextCast_sq K a p q hpq n)
      simpa using h)

omit [DecidableEq V] [LinearOrder V] in
private theorem chainInclusion_comp_local (A B C : FiniteComplex V)
    (hAB : A.simplices ⊆ B.simplices) (hBC : B.simplices ⊆ C.simplices)
    (n : ℤ) :
    (chainInclusion B C hBC n).comp (chainInclusion A B hAB n) =
      chainInclusion A C (hAB.trans hBC) n := by
  apply AddMonoidHom.ext
  intro c
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | neg x hx => simp [map_neg, hx]
  | of σ =>
    change FreeAbelianGroup.of
        (⟨σ.1, hBC (hAB σ.2.1), σ.2.2⟩ : SimplexAt C n) = _
    rfl

omit [DecidableEq V] [LinearOrder V] in
private theorem chainInclusion_self_local (A : FiniteComplex V) (n : ℤ) :
    chainInclusion A A (by intro x hx; exact hx) n =
      AddMonoidHom.id (chains A n) := by
  apply FreeAbelianGroup.lift_ext
  intro σ
  rfl

noncomputable def genericQuotientMap
    (K : FiniteComplex V) (a : ArcLabels V B)
    {p q p' q' : ℕ} (hpq : p ≤ q) (hp : p ≤ p') (hq : q ≤ q')
    (hp'q' : p' ≤ q') (n : ℤ) :
    genericQuotient K a p q hpq n →+
      genericQuotient K a p' q' hp'q' n := by
  let I (m : ℤ) := chainInclusion (filtration K a p) (filtration K a q)
    (filtration_mono K a (by omega)) m
  let I' (m : ℤ) := chainInclusion (filtration K a p') (filtration K a q')
    (filtration_mono K a (by omega)) m
  let J (m : ℤ) := chainInclusion (filtration K a q) (filtration K a q')
    (filtration_mono K a (by omega)) m
  let Q := QuotientAddGroup.mk' (I' n).range
  have hle : (I n).range ≤ (Q.comp (J n)).ker := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    have hleft := chainInclusion_comp_local (filtration K a p)
      (filtration K a q) (filtration K a q')
      (filtration_mono K a (by omega)) (filtration_mono K a (by omega)) n
    have hright := chainInclusion_comp_local (filtration K a p)
      (filtration K a p') (filtration K a q')
      (filtration_mono K a (by omega)) (filtration_mono K a (by omega)) n
    have hsq : J n (I n y) = I' n
      (chainInclusion (filtration K a p) (filtration K a p')
        (filtration_mono K a (by omega)) n y) := by
      have hl := congrArg (fun z => z y) hleft
      have hr := congrArg (fun z => z y) hright
      exact hl.trans hr.symm
    change Q (J n (I n y)) = 0
    rw [hsq]
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨_, rfl⟩
  exact QuotientAddGroup.lift (I n).range (Q.comp (J n)) hle

omit [LinearOrder V] in
private theorem genericQuotientMap_desc
    (K : FiniteComplex V) (a : ArcLabels V B)
    {p q p' q' : ℕ} (hpq : p ≤ q) (hp : p ≤ p') (hq : q ≤ q')
    (hp'q' : p' ≤ q') (n : ℤ) (c : chains (filtration K a q) n) :
    genericQuotientMap K a hpq hp hq hp'q' n
      (QuotientAddGroup.mk' _ c) =
      QuotientAddGroup.mk' _
        (chainInclusion (filtration K a q) (filtration K a q')
          (filtration_mono K a (by omega)) n c) := by
  rfl

omit [LinearOrder V] in
theorem genericQuotientMap_comp
    (K : FiniteComplex V) (a : ArcLabels V B)
    {p q p' q' p'' q'' : ℕ} (hpq : p ≤ q) (hp : p ≤ p') (hq : q ≤ q')
    (hp'q' : p' ≤ q') (hpp : p' ≤ p'') (hqq : q' ≤ q'')
    (hpp'' : p'' ≤ q'') (n : ℤ) :
    (genericQuotientMap K a hp'q' hpp hqq hpp'' n).comp
      (genericQuotientMap K a hpq hp hq hp'q' n) =
      genericQuotientMap K a hpq (hp.trans hpp) (hq.trans hqq) hpp'' n := by
  apply AddMonoidHom.ext
  intro c
  induction c using QuotientAddGroup.induction_on with
  | _ c =>
    change genericQuotientMap K a hp'q' hpp hqq hpp'' n
        (genericQuotientMap K a hpq hp hq hp'q' n
          (QuotientAddGroup.mk' _ c)) =
      genericQuotientMap K a hpq (hp.trans hpp) (hq.trans hqq) hpp'' n
        (QuotientAddGroup.mk' _ c)
    rw [genericQuotientMap_desc, genericQuotientMap_desc,
      genericQuotientMap_desc]
    apply congrArg (QuotientAddGroup.mk' _)
    exact (chainInclusion_comp_local (filtration K a q) (filtration K a q')
      (filtration K a q'') (filtration_mono K a (by omega))
      (filtration_mono K a (by omega)) n) ▸ rfl

omit [LinearOrder V] in
theorem genericQuotientMap_id
    (K : FiniteComplex V) (a : ArcLabels V B)
    {p q : ℕ} (hpq : p ≤ q) (n : ℤ) :
    genericQuotientMap K a hpq (le_refl p) (le_refl q) hpq n =
      AddMonoidHom.id (genericQuotient K a p q hpq n) := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    change genericQuotientMap K a hpq (le_refl p) (le_refl q) hpq n
        (QuotientAddGroup.mk' _ c) = QuotientAddGroup.mk' _ c
    rw [genericQuotientMap_desc]
    have h := congrArg (fun f => f c)
      (chainInclusion_self_local (filtration K a q) n)
    exact congrArg (QuotientAddGroup.mk' _) h

private theorem genericQuotientMap_boundary
    (K : FiniteComplex V) (a : ArcLabels V B)
    {p q p' q' : ℕ} (hpq : p ≤ q) (hp : p ≤ p') (hq : q ≤ q')
    (hp'q' : p' ≤ q') (n : ℤ) :
    (genericQuotientBoundary K a p' q' hp'q' n).comp
      (genericQuotientMap K a hpq hp hq hp'q' n) =
    (genericQuotientMap K a hpq hp hq hp'q' (n - 1)).comp
      (genericQuotientBoundary K a p q hpq n) := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    change genericQuotientBoundary K a p' q' hp'q' n
        (genericQuotientMap K a hpq hp hq hp'q' n
          (QuotientAddGroup.mk' _ c)) =
      genericQuotientMap K a hpq hp hq hp'q' (n - 1)
        (genericQuotientBoundary K a p q hpq n
          (QuotientAddGroup.mk' _ c))
    rw [genericQuotientMap_desc, genericQuotientBoundary_desc,
      genericQuotientBoundary_desc, genericQuotientMap_desc]
    exact congrArg (QuotientAddGroup.mk' _)
      (congrArg (fun f => f c)
        (chainInclusion_boundary (filtration K a q) (filtration K a q')
          (filtration_mono K a (by omega)) n))

noncomputable def genericQuotientChainMap
    (K : FiniteComplex V) (a : ArcLabels V B)
    {p q p' q' : ℕ} (hpq : p ≤ q) (hp : p ≤ p') (hq : q ≤ q')
    (hp'q' : p' ≤ q') :
    genericQuotientComplex K a p q hpq ⟶
      genericQuotientComplex K a p' q' hp'q' :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (AddMonoidHom.toIntLinearMap
      (genericQuotientMap K a hpq hp hq hp'q' n)))
    (by
      intro n
      simp only [genericQuotientComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      ext c
      have hnat := congrArg (fun f => f c)
        (genericQuotientMap_boundary K a hpq hp hq hp'q' (n + 1))
      simp only [AddMonoidHom.comp_apply] at hnat
      change genericQuotientBoundaryNextCast K a p' q' hp'q' n
          (genericQuotientMap K a hpq hp hq hp'q' (n + 1) c) =
        genericQuotientMap K a hpq hp hq hp'q' n
          (genericQuotientBoundaryNextCast K a p q hpq n c)
      rw [genericQuotientBoundaryNextCast_apply, hnat,
        cast_map_apply (show n + 1 - 1 = n by omega)
          (genericQuotientMap K a hpq hp hq hp'q')]
      congr 1
      exact (genericQuotientBoundaryNextCast_apply K a p q hpq n c).symm)

theorem genericQuotientChainMap_id
    (K : FiniteComplex V) (a : ArcLabels V B)
    {p q : ℕ} (hpq : p ≤ q) :
    genericQuotientChainMap K a hpq (le_refl p) (le_refl q) hpq =
      𝟙 (genericQuotientComplex K a p q hpq) := by
  ext n x
  exact congrArg (fun f => f x) (genericQuotientMap_id K a hpq n)

theorem genericQuotientChainMap_comp
    (K : FiniteComplex V) (a : ArcLabels V B)
    {p q p' q' p'' q'' : ℕ} (hpq : p ≤ q) (hp : p ≤ p') (hq : q ≤ q')
    (hp'q' : p' ≤ q') (hpp : p' ≤ p'') (hqq : q' ≤ q'')
    (hpp'' : p'' ≤ q'') :
    genericQuotientChainMap K a hpq hp hq hp'q' ≫
      genericQuotientChainMap K a hp'q' hpp hqq hpp'' =
    genericQuotientChainMap K a hpq (hp.trans hpp) (hq.trans hqq) hpp'' := by
  ext n x
  exact congrArg (fun f => f x)
    (genericQuotientMap_comp K a hpq hp hq hp'q' hpp hqq hpp'' n)

omit [LinearOrder V] in
private theorem genericTripleMap_zero
    (K : FiniteComplex V) (a : ArcLabels V B)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) (n : ℤ) :
    (genericQuotientMap K a (hpq.trans hqr) hpq (le_refl r) hqr n).comp
      (genericQuotientMap K a hpq (le_refl p) hqr (hpq.trans hqr) n) = 0 := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    change genericQuotientMap K a (hpq.trans hqr) hpq (le_refl r) hqr n
        (genericQuotientMap K a hpq (le_refl p) hqr (hpq.trans hqr) n
          (QuotientAddGroup.mk' _ c)) = 0
    rw [genericQuotientMap_desc, genericQuotientMap_desc]
    have hself := congrArg (fun f => f
      (chainInclusion (filtration K a q) (filtration K a r)
        (filtration_mono K a (by omega)) n c))
      (chainInclusion_self_local (filtration K a r) n)
    rw [hself]
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨c, rfl⟩

omit [LinearOrder V] in
private theorem genericTripleMap_surjective
    (K : FiniteComplex V) (a : ArcLabels V B)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) (n : ℤ) :
    Function.Surjective
      (genericQuotientMap K a (hpq.trans hqr) hpq (le_refl r) hqr n) := by
  intro y
  induction y using QuotientAddGroup.induction_on with
  | _ c =>
    refine ⟨QuotientAddGroup.mk' _ c, ?_⟩
    rw [genericQuotientMap_desc]
    have h := congrArg (fun f => f c)
      (chainInclusion_self_local (filtration K a r) n)
    exact congrArg (QuotientAddGroup.mk' _) h

end CurveGenusTwo.Filtration
