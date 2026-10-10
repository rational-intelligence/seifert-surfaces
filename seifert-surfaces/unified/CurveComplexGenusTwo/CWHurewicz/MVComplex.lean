import CurveComplexGenusTwo.CWHurewicz.CoverSequence
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace CurveComplexGenusTwo.CWHurewicz
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable def mvOrdinaryComplex (X : TopCat) (U : Set X) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ (coverOrdinaryChains X U n))
    (fun n => ModuleCat.ofHom (singularBoundaryFinsupp (TopCat.of U) n))
    (fun n => by apply ModuleCat.hom_ext; apply LinearMap.ext; intro c; exact singularBoundaryFinsupp_comp_zero (TopCat.of U) n c)

noncomputable def mvPairComplex (X : TopCat) (U V : Set X) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of
    (fun n => ModuleCat.of ℤ (coverOrdinaryChains X U n × coverOrdinaryChains X V n))
    (fun n => ModuleCat.ofHom (coverOrdinaryPairBoundary X U V n))
    (fun n => by apply ModuleCat.hom_ext; apply LinearMap.ext; intro c; exact coverOrdinaryPairBoundary_square X U V n c)

noncomputable def mvSmallComplex (X : TopCat) (U V : Set X) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ (coverSmallChains X U V n))
    (fun n => ModuleCat.ofHom (smallSingularBoundary X V Uᶜ n))
    (fun n => by apply ModuleCat.hom_ext; apply LinearMap.ext; intro c; exact coverSmallBoundary_square X U V n c)

noncomputable def mvDifference (X : TopCat) (U V : Set X) :
    mvOrdinaryComplex X (U ∩ V) ⟶ mvPairComplex X U V :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (coverOrdinaryDifference X U V n))
    (fun n => by
      simp only [mvOrdinaryComplex, mvPairComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact coverOrdinaryDifference_boundary X U V n c)

noncomputable def mvSum (X : TopCat) (U V : Set X) :
    mvPairComplex X U V ⟶ mvSmallComplex X U V :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (coverOrdinarySum X U V n))
    (fun n => by
      simp only [mvPairComplex, mvSmallComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact coverOrdinarySum_boundary X U V n c)

theorem mvDifference_sum (X : TopCat) (U V : Set X) :
    mvDifference X U V ≫ mvSum X U V = 0 := by
  ext n c
  exact coverOrdinarySum_difference X U V n c

noncomputable def mvShortComplex (X : TopCat) (U V : Set X) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (mvDifference X U V) (mvSum X U V) (mvDifference_sum X U V)

theorem mvShortExact (X : TopCat) (U V : Set X) :
    (mvShortComplex X U V).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · intro c
    change coverOrdinarySum X U V n c = 0 ↔
      ∃ b, coverOrdinaryDifference X U V n b = c
    exact Iff.of_eq (congrArg (fun S => c ∈ S) (coverOrdinarySum_ker X U V n))
  · exact coverOrdinaryDifference_injective X U V n
  · exact coverOrdinarySum_surjective X U V n

noncomputable def mvHomologyDifference (X : TopCat) (U V : Set X) (n : ℕ) :
    (mvOrdinaryComplex X (U ∩ V)).homology n ⟶ (mvPairComplex X U V).homology n :=
  HomologicalComplex.homologyMap (mvDifference X U V) n

noncomputable def mvHomologySum (X : TopCat) (U V : Set X) (n : ℕ) :
    (mvPairComplex X U V).homology n ⟶ (mvSmallComplex X U V).homology n :=
  HomologicalComplex.homologyMap (mvSum X U V) n

noncomputable def mvConnecting (X : TopCat) (U V : Set X) (n : ℕ) :
    (mvSmallComplex X U V).homology (n + 1) ⟶
      (mvOrdinaryComplex X (U ∩ V)).homology n :=
  (mvShortExact X U V).δ (n + 1) n (by simp)

theorem mvConnecting_difference (X : TopCat) (U V : Set X) (n : ℕ) :
    mvConnecting X U V n ≫ mvHomologyDifference X U V n = 0 :=
  (mvShortExact X U V).δ_comp (n + 1) n (by simp)

theorem mvSum_connecting (X : TopCat) (U V : Set X) (n : ℕ) :
    mvHomologySum X U V (n + 1) ≫ mvConnecting X U V n = 0 :=
  (mvShortExact X U V).comp_δ (n + 1) n (by simp)

theorem mvHomologyDifference_sum (X : TopCat) (U V : Set X) (n : ℕ) :
    mvHomologyDifference X U V n ≫ mvHomologySum X U V n = 0 := by
  rw [mvHomologyDifference, mvHomologySum, ← HomologicalComplex.homologyMap_comp,
    mvDifference_sum, HomologicalComplex.homologyMap_zero]

theorem mvHomology_exact_intersection (X : TopCat) (U V : Set X) (n : ℕ) :
    (ShortComplex.mk (mvConnecting X U V n) (mvHomologyDifference X U V n)
      (mvConnecting_difference X U V n)).Exact :=
  (mvShortExact X U V).homology_exact₁ (n + 1) n (by simp)

theorem mvHomology_exact_pair (X : TopCat) (U V : Set X) (n : ℕ) :
    (ShortComplex.mk (mvHomologyDifference X U V n) (mvHomologySum X U V n)
      (mvHomologyDifference_sum X U V n)).Exact :=
  (mvShortExact X U V).homology_exact₂ n

theorem mvHomology_exact_small (X : TopCat) (U V : Set X) (n : ℕ) :
    (ShortComplex.mk (mvHomologySum X U V (n + 1)) (mvConnecting X U V n)
      (mvSum_connecting X U V n)).Exact :=
  (mvShortExact X U V).homology_exact₃ (n + 1) n (by simp)



noncomputable def mvSubsetMap (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    mvOrdinaryComplex X A ⟶ mvOrdinaryComplex X B :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (coverSubsetPush X A B h n))
    (fun n => by
      simp only [mvOrdinaryComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      exact LinearMap.ext (coverSubsetPush_boundary X A B h n))

noncomputable def mvPairFst (X : TopCat) (U V : Set X) :
    mvPairComplex X U V ⟶ mvOrdinaryComplex X U :=
  ChainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.fst ℤ _ _))
    (fun n => by simp only [mvPairComplex, mvOrdinaryComplex, ChainComplex.of_d]; rfl)

noncomputable def mvPairSnd (X : TopCat) (U V : Set X) :
    mvPairComplex X U V ⟶ mvOrdinaryComplex X V :=
  ChainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.snd ℤ _ _))
    (fun n => by simp only [mvPairComplex, mvOrdinaryComplex, ChainComplex.of_d]; rfl)

noncomputable def mvPairInl (X : TopCat) (U V : Set X) :
    mvOrdinaryComplex X U ⟶ mvPairComplex X U V :=
  ChainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.inl ℤ _ _))
    (fun n => by
      simp only [mvPairComplex, mvOrdinaryComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact Prod.ext rfl (map_zero (singularBoundaryFinsupp (TopCat.of V) n)))

noncomputable def mvPairInr (X : TopCat) (U V : Set X) :
    mvOrdinaryComplex X V ⟶ mvPairComplex X U V :=
  ChainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.inr ℤ _ _))
    (fun n => by
      simp only [mvPairComplex, mvOrdinaryComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact Prod.ext (map_zero (singularBoundaryFinsupp (TopCat.of U) n)) rfl)

theorem mvDifference_fst (X : TopCat) (U V : Set X) :
    mvDifference X U V ≫ mvPairFst X U V =
      mvSubsetMap X (U ∩ V) U Set.inter_subset_left := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact congrArg Prod.fst (coverOrdinaryDifference_inclusions X U V n c)

theorem mvDifference_snd (X : TopCat) (U V : Set X) :
    mvDifference X U V ≫ mvPairSnd X U V =
      -mvSubsetMap X (U ∩ V) V Set.inter_subset_right := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact congrArg Prod.snd (coverOrdinaryDifference_inclusions X U V n c)

theorem mvHomologyDifference_fst (X : TopCat) (U V : Set X) (n : ℕ) :
    mvHomologyDifference X U V n ≫ HomologicalComplex.homologyMap (mvPairFst X U V) n =
      HomologicalComplex.homologyMap (mvSubsetMap X (U ∩ V) U Set.inter_subset_left) n := by
  rw [mvHomologyDifference, ← HomologicalComplex.homologyMap_comp, mvDifference_fst]

theorem mvHomologyDifference_snd (X : TopCat) (U V : Set X) (n : ℕ) :
    mvHomologyDifference X U V n ≫ HomologicalComplex.homologyMap (mvPairSnd X U V) n =
      -HomologicalComplex.homologyMap (mvSubsetMap X (U ∩ V) V Set.inter_subset_right) n := by
  rw [mvHomologyDifference, ← HomologicalComplex.homologyMap_comp, mvDifference_snd,
    HomologicalComplex.homologyMap_neg]

noncomputable def mvAmbientComplex (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ ((TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ))
    (fun n => ModuleCat.ofHom (singularBoundaryFinsupp X n))
    (fun n => by apply ModuleCat.hom_ext; exact LinearMap.ext (singularBoundaryFinsupp_comp_zero X n))

noncomputable def mvSmallInclusion (X : TopCat) (U V : Set X) :
    mvSmallComplex X U V ⟶ mvAmbientComplex X :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (coverSmallChains X U V n).subtype)
    (fun n => by simp only [mvSmallComplex, mvAmbientComplex, ChainComplex.of_d]; rfl)

noncomputable def mvAmbientPush (X : TopCat) (U : Set X) :
    mvOrdinaryComplex X U ⟶ mvAmbientComplex X :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (coverOrdinaryPush X U n))
    (fun n => by
      simp only [mvOrdinaryComplex, mvAmbientComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      exact LinearMap.ext (coverOrdinaryPush_boundary X U n))

theorem mvInl_sum_inclusion (X : TopCat) (U V : Set X) :
    mvPairInl X U V ≫ mvSum X U V ≫ mvSmallInclusion X U V = mvAmbientPush X U := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change coverOrdinaryPush X U n c + coverOrdinaryPush X V n 0 = coverOrdinaryPush X U n c
  simp

theorem mvInr_sum_inclusion (X : TopCat) (U V : Set X) :
    mvPairInr X U V ≫ mvSum X U V ≫ mvSmallInclusion X U V = mvAmbientPush X V := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change coverOrdinaryPush X U n 0 + coverOrdinaryPush X V n c = coverOrdinaryPush X V n c
  simp

theorem mvHomologyInl_sum_inclusion (X : TopCat) (U V : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (mvPairInl X U V) n ≫ mvHomologySum X U V n ≫
      HomologicalComplex.homologyMap (mvSmallInclusion X U V) n =
        HomologicalComplex.homologyMap (mvAmbientPush X U) n := by
  rw [mvHomologySum, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, mvInl_sum_inclusion]

theorem mvHomologyInr_sum_inclusion (X : TopCat) (U V : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (mvPairInr X U V) n ≫ mvHomologySum X U V n ≫
      HomologicalComplex.homologyMap (mvSmallInclusion X U V) n =
        HomologicalComplex.homologyMap (mvAmbientPush X V) n := by
  rw [mvHomologySum, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, mvInr_sum_inclusion]



private noncomputable def mvCycleClass (S : ShortComplex (ModuleCat ℤ))
    (z : LinearMap.ker S.g.hom) : S.homology :=
  S.homologyπ (S.moduleCatCyclesIso.inv z)

private theorem mvCycleClass_iota (S : ShortComplex (ModuleCat ℤ))
    (z : LinearMap.ker S.g.hom) :
    S.homologyι (mvCycleClass S z) = S.pOpcycles z.1 := by
  have h := congrArg (fun f : S.cycles ⟶ S.opcycles => f (S.moduleCatCyclesIso.inv z))
    S.homology_π_ι
  have hz : S.iCycles (S.moduleCatCyclesIso.inv z) = z.1 :=
    congrArg (fun f : S.moduleCatLeftHomologyData.K ⟶ S.X₂ => f z)
      S.moduleCatCyclesIso_inv_iCycles
  simpa only [mvCycleClass, ConcreteCategory.comp_apply, hz] using h

private theorem mvCycleClass_surjective (S : ShortComplex (ModuleCat ℤ)) :
    Function.Surjective (mvCycleClass S) := by
  intro x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance x
  refine ⟨S.moduleCatCyclesIso.hom y, ?_⟩
  simp [mvCycleClass, ← ConcreteCategory.comp_apply]

private theorem mvCycleClass_eq_zero (S : ShortComplex (ModuleCat ℤ))
    (z : LinearMap.ker S.g.hom) :
    mvCycleClass S z = 0 ↔ z.1 ∈ LinearMap.range S.f.hom := by
  rw [← S.moduleCat_pOpcycles_eq_zero_iff, ← mvCycleClass_iota]
  exact ⟨fun h => by rw [h]; exact map_zero _,
    (injective_iff_map_eq_zero S.homologyι.hom).mp
      ((ModuleCat.mono_iff_injective _).mp inferInstance) _⟩

private theorem mvCycleClass_map {S T : ShortComplex (ModuleCat ℤ)}
    (φ : S ⟶ T) (z : LinearMap.ker S.g.hom)
    (w : LinearMap.ker T.g.hom) (hw : φ.τ₂ z.1 = w.1) :
    S.homologyMap φ (mvCycleClass S z) = mvCycleClass T w := by
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [mvCycleClass_iota]
  have h := congrArg (fun f : S.cycles ⟶ T.opcycles => f (S.moduleCatCyclesIso.inv z))
    (ShortComplex.π_homologyMap_ι φ)
  have hz : S.iCycles (S.moduleCatCyclesIso.inv z) = z.1 :=
    congrArg (fun f : S.moduleCatLeftHomologyData.K ⟶ S.X₂ => f z)
      S.moduleCatCyclesIso_inv_iCycles
  simpa only [mvCycleClass, ConcreteCategory.comp_apply, hz, hw] using h

private theorem mvCycleClass_eq (S : ShortComplex (ModuleCat ℤ))
    (z w : LinearMap.ker S.g.hom) :
    mvCycleClass S z = mvCycleClass S w ↔ z.1 - w.1 ∈ LinearMap.range S.f.hom := by
  rw [← S.moduleCat_pOpcycles_eq_iff, ← mvCycleClass_iota, ← mvCycleClass_iota]
  exact ((ModuleCat.mono_iff_injective S.homologyι).mp inferInstance).eq_iff.symm




private theorem mvAmbient_cycle_iff (X : TopCat) (n : ℕ)
    (c : (mvAmbientComplex X).X n) :
    ((mvAmbientComplex X).sc n).g c = 0 ↔ c ∈ absoluteSingularCycles X n := by
  change (mvAmbientComplex X).d n ((ComplexShape.down ℕ).next n) c = 0 ↔ _
  cases n with
  | zero =>
      rw [ChainComplex.next_nat_zero]
      simp only [mvAmbientComplex, ChainComplex.of_d_ne _ _ (by omega : 0 ≠ 0 + 1)]
      exact iff_of_true rfl (Submodule.mem_top)
  | succ n =>
      rw [ChainComplex.next_nat_succ]
      simp only [mvAmbientComplex, ChainComplex.of_d]
      rfl

private theorem mvSmall_cycle_iff (X : TopCat) (U V : Set X) (n : ℕ)
    (c : (mvSmallComplex X U V).X n) :
    ((mvSmallComplex X U V).sc n).g c = 0 ↔ c.1 ∈ absoluteSingularCycles X n := by
  change (mvSmallComplex X U V).d n ((ComplexShape.down ℕ).next n) c = 0 ↔ _
  cases n with
  | zero =>
      rw [ChainComplex.next_nat_zero]
      simp only [mvSmallComplex, ChainComplex.of_d_ne _ _ (by omega : 0 ≠ 0 + 1)]
      exact iff_of_true rfl (Submodule.mem_top)
  | succ n =>
      rw [ChainComplex.next_nat_succ]
      simp only [mvSmallComplex, ChainComplex.of_d]
      exact Subtype.ext_iff

private theorem mvAmbient_boundary_iff (X : TopCat) (n : ℕ)
    (c : (mvAmbientComplex X).X n) :
    c ∈ LinearMap.range ((mvAmbientComplex X).sc n).f.hom ↔
      ∃ b, singularBoundaryFinsupp X n b = c := by
  change c ∈ LinearMap.range ((mvAmbientComplex X).d ((ComplexShape.down ℕ).prev n) n).hom ↔ _
  rw [ChainComplex.prev]
  simp only [mvAmbientComplex, ChainComplex.of_d]
  rfl

private theorem mvSmall_boundary_iff (X : TopCat) (U V : Set X) (n : ℕ)
    (c : (mvSmallComplex X U V).X n) :
    c ∈ LinearMap.range ((mvSmallComplex X U V).sc n).f.hom ↔
      ∃ b, b ∈ coverSmallChains X U V (n + 1) ∧ singularBoundaryFinsupp X n b = c.1 := by
  change c ∈ LinearMap.range ((mvSmallComplex X U V).d ((ComplexShape.down ℕ).prev n) n).hom ↔ _
  rw [ChainComplex.prev]
  simp only [mvSmallComplex, ChainComplex.of_d, LinearMap.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.1, b.2, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨⟨b, hb⟩, Subtype.ext h⟩



/-- The actual small-chain inclusion induces an isomorphism, using the previously
proved subdivision representative and small-filling theorems. -/
theorem mvSmallInclusion_homology_isIso (X : TopCat) (U V : Set X)
    (hUV : closure Uᶜ ⊆ interior V) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (mvSmallInclusion X U V) n) := by
  let S := (mvSmallComplex X U V).sc n
  let T := (mvAmbientComplex X).sc n
  let φ : S ⟶ T :=
    (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
      (mvSmallInclusion X U V)
  have hsurj : Function.Surjective (S.homologyMap φ) := by
    intro q
    obtain ⟨z, rfl⟩ := mvCycleClass_surjective T q
    have hz := (mvAmbient_cycle_iff X n z.1).mp z.2
    obtain ⟨w, hw, b, hb⟩ := absoluteCycle_has_small_representative X V Uᶜ hUV n z.1 hz
    let ws : LinearMap.ker S.g.hom :=
      ⟨⟨w, hw.1⟩, (mvSmall_cycle_iff X U V n ⟨w, hw.1⟩).mpr hw.2⟩
    let wa : LinearMap.ker T.g.hom := ⟨w, (mvAmbient_cycle_iff X n w).mpr hw.2⟩
    refine ⟨mvCycleClass S ws, ?_⟩
    rw [mvCycleClass_map φ ws wa rfl]
    apply (mvCycleClass_eq T wa z).mpr
    exact (mvAmbient_boundary_iff X n (wa.1 - z.1)).mpr ⟨b, hb.symm⟩
  have hinj : Function.Injective (S.homologyMap φ) := by
    apply (injective_iff_map_eq_zero (S.homologyMap φ).hom).mpr
    intro q hq
    obtain ⟨z, rfl⟩ := mvCycleClass_surjective S q
    have hz := (mvSmall_cycle_iff X U V n z.1).mp z.2
    let za : LinearMap.ker T.g.hom :=
      ⟨z.1.1, (mvAmbient_cycle_iff X n z.1.1).mpr hz⟩
    rw [mvCycleClass_map φ z za rfl] at hq
    have hb := (mvCycleClass_eq_zero T za).mp hq
    obtain ⟨b, hb⟩ := (mvAmbient_boundary_iff X n z.1.1).mp hb
    obtain ⟨b', hsmall, hfill⟩ := smallCycle_has_small_filling X V Uᶜ hUV n z.1.1
      ⟨z.1.2, hz⟩ b hb
    apply (mvCycleClass_eq_zero S z).mpr
    exact (mvSmall_boundary_iff X U V n z.1).mpr ⟨b', hsmall, hfill⟩
  letI : Mono (S.homologyMap φ) := (ModuleCat.mono_iff_injective _).mpr hinj
  letI : Epi (S.homologyMap φ) := (ModuleCat.epi_iff_surjective _).mpr hsurj
  exact isIso_of_mono_of_epi (S.homologyMap φ)

theorem mvOpenCover_excisionCondition (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    closure Uᶜ ⊆ interior V := by
  rw [hU.isClosed_compl.closure_eq, hV.interior_eq]
  intro x hx
  have h : x ∈ U ∪ V := hcover.symm ▸ Set.mem_univ x
  exact h.resolve_left hx

/-- Open covers identify small-chain homology with ambient singular homology,
through the actual inclusion map, in every nonnegative degree. -/
noncomputable def mvOpenCoverHomologyIso (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (mvSmallComplex X U V).homology n ≅ (mvAmbientComplex X).homology n := by
  letI := mvSmallInclusion_homology_isIso X U V
    (mvOpenCover_excisionCondition X U V hU hV hcover) n
  exact asIso (HomologicalComplex.homologyMap (mvSmallInclusion X U V) n)



noncomputable def mvAmbientHomologySum (X : TopCat) (U V : Set X) (n : ℕ) :
    (mvPairComplex X U V).homology n ⟶ (mvAmbientComplex X).homology n :=
  mvHomologySum X U V n ≫ HomologicalComplex.homologyMap (mvSmallInclusion X U V) n

noncomputable def mvAmbientConnecting (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (mvAmbientComplex X).homology (n + 1) ⟶
      (mvOrdinaryComplex X (U ∩ V)).homology n :=
  (mvOpenCoverHomologyIso X U V hU hV hcover (n + 1)).inv ≫ mvConnecting X U V n

theorem mvAmbientConnecting_difference (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    mvAmbientConnecting X U V hU hV hcover n ≫ mvHomologyDifference X U V n = 0 := by
  simp [mvAmbientConnecting, Category.assoc, mvConnecting_difference]

theorem mvAmbientSum_connecting (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    mvAmbientHomologySum X U V (n + 1) ≫ mvAmbientConnecting X U V hU hV hcover n = 0 := by
  change (mvHomologySum X U V (n + 1) ≫
    (mvOpenCoverHomologyIso X U V hU hV hcover (n + 1)).hom) ≫
      ((mvOpenCoverHomologyIso X U V hU hV hcover (n + 1)).inv ≫ mvConnecting X U V n) = 0
  simp [Category.assoc, mvSum_connecting]

theorem mvHomologyDifference_ambientSum (X : TopCat) (U V : Set X) (n : ℕ) :
    mvHomologyDifference X U V n ≫ mvAmbientHomologySum X U V n = 0 := by
  rw [mvAmbientHomologySum, ← Category.assoc, mvHomologyDifference_sum, zero_comp]

/-- Mayer–Vietoris exactness at the intersection homology, derived from the
short exact chain sequence and the proved small-chain comparison. -/
theorem mvAmbient_exact_intersection (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (ShortComplex.mk (mvAmbientConnecting X U V hU hV hcover n)
      (mvHomologyDifference X U V n) (mvAmbientConnecting_difference X U V hU hV hcover n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mvHomology_exact_intersection X U V n)
  refine ShortComplex.isoMk (mvOpenCoverHomologyIso X U V hU hV hcover (n + 1))
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp [mvAmbientConnecting]
  · simp

theorem mvAmbient_exact_pair (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (ShortComplex.mk (mvHomologyDifference X U V n) (mvAmbientHomologySum X U V n)
      (mvHomologyDifference_ambientSum X U V n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mvHomology_exact_pair X U V n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (mvOpenCoverHomologyIso X U V hU hV hcover n) ?_ ?_
  · simp
  · simp [mvAmbientHomologySum, mvOpenCoverHomologyIso]

theorem mvAmbient_exact_ambient (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (ShortComplex.mk (mvAmbientHomologySum X U V (n + 1))
      (mvAmbientConnecting X U V hU hV hcover n)
      (mvAmbientSum_connecting X U V hU hV hcover n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mvHomology_exact_small X U V n)
  refine ShortComplex.isoMk (Iso.refl _)
    (mvOpenCoverHomologyIso X U V hU hV hcover (n + 1)) (Iso.refl _) ?_ ?_
  · simp [mvAmbientHomologySum, mvOpenCoverHomologyIso]
  · simp [mvAmbientConnecting]

/-- The non-augmented sequence ends surjectively in degree zero. -/
theorem mvHomologySum_zero_epi (X : TopCat) (U V : Set X) :
    Epi (mvHomologySum X U V 0) := by
  letI : Epi (mvSum X U V) := (mvShortExact X U V).epi_g
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel (mvSum X U V) 0 (by simp)

theorem mvAmbientHomologySum_zero_epi (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    Epi (mvAmbientHomologySum X U V 0) := by
  letI := mvHomologySum_zero_epi X U V
  letI := mvSmallInclusion_homology_isIso X U V
    (mvOpenCover_excisionCondition X U V hU hV hcover) 0
  dsimp only [mvAmbientHomologySum]
  infer_instance



theorem mvPair_inl_fst (X : TopCat) (U V : Set X) :
    mvPairInl X U V ≫ mvPairFst X U V = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  rfl

theorem mvPair_inr_snd (X : TopCat) (U V : Set X) :
    mvPairInr X U V ≫ mvPairSnd X U V = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  rfl

theorem mvPair_inl_snd (X : TopCat) (U V : Set X) :
    mvPairInl X U V ≫ mvPairSnd X U V = 0 := by
  apply HomologicalComplex.Hom.ext
  rfl

theorem mvPair_inr_fst (X : TopCat) (U V : Set X) :
    mvPairInr X U V ≫ mvPairFst X U V = 0 := by
  apply HomologicalComplex.Hom.ext
  rfl

theorem mvPair_split (X : TopCat) (U V : Set X) :
    mvPairFst X U V ≫ mvPairInl X U V + mvPairSnd X U V ≫ mvPairInr X U V = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact Prod.ext (add_zero c.1) (zero_add c.2)

/-- Homology of the chain pair is the binary direct sum of the two homology modules. -/
noncomputable def mvPairHomologyEquiv (X : TopCat) (U V : Set X) (n : ℕ) :
    (mvPairComplex X U V).homology n ≃ₗ[ℤ]
      ((mvOrdinaryComplex X U).homology n × (mvOrdinaryComplex X V).homology n) :=
  AddEquiv.toIntLinearEquiv {
  toFun q := (HomologicalComplex.homologyMap (mvPairFst X U V) n q,
    HomologicalComplex.homologyMap (mvPairSnd X U V) n q)
  invFun q := HomologicalComplex.homologyMap (mvPairInl X U V) n q.1 +
    HomologicalComplex.homologyMap (mvPairInr X U V) n q.2
  left_inv q := by
    have h := congrArg (fun f => HomologicalComplex.homologyMap f n) (mvPair_split X U V)
    rw [HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at h
    exact congrArg (fun f => f q) h
  right_inv q := by
    have h11 := congrArg (fun f => HomologicalComplex.homologyMap f n) (mvPair_inl_fst X U V)
    have h12 := congrArg (fun f => HomologicalComplex.homologyMap f n) (mvPair_inl_snd X U V)
    have h21 := congrArg (fun f => HomologicalComplex.homologyMap f n) (mvPair_inr_fst X U V)
    have h22 := congrArg (fun f => HomologicalComplex.homologyMap f n) (mvPair_inr_snd X U V)
    simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id,
      HomologicalComplex.homologyMap_zero] at h11 h12 h21 h22
    apply Prod.ext
    · have a := congrArg (fun f => f q.1) h11
      have b := congrArg (fun f => f q.2) h21
      change HomologicalComplex.homologyMap (mvPairFst X U V) n
        (HomologicalComplex.homologyMap (mvPairInl X U V) n q.1 +
          HomologicalComplex.homologyMap (mvPairInr X U V) n q.2) = q.1
      rw [map_add]
      rw [show HomologicalComplex.homologyMap (mvPairFst X U V) n
        (HomologicalComplex.homologyMap (mvPairInl X U V) n q.1) = q.1 from a,
        show HomologicalComplex.homologyMap (mvPairFst X U V) n
        (HomologicalComplex.homologyMap (mvPairInr X U V) n q.2) = 0 from b, add_zero]
    · have a := congrArg (fun f => f q.1) h12
      have b := congrArg (fun f => f q.2) h22
      change HomologicalComplex.homologyMap (mvPairSnd X U V) n
        (HomologicalComplex.homologyMap (mvPairInl X U V) n q.1 +
          HomologicalComplex.homologyMap (mvPairInr X U V) n q.2) = q.2
      rw [map_add]
      rw [show HomologicalComplex.homologyMap (mvPairSnd X U V) n
        (HomologicalComplex.homologyMap (mvPairInl X U V) n q.1) = 0 from a,
        show HomologicalComplex.homologyMap (mvPairSnd X U V) n
        (HomologicalComplex.homologyMap (mvPairInr X U V) n q.2) = q.2 from b, zero_add]
  map_add' a b := Prod.ext
    ((HomologicalComplex.homologyMap (mvPairFst X U V) n).hom.map_add a b)
    ((HomologicalComplex.homologyMap (mvPairSnd X U V) n).hom.map_add a b)
  }

@[simp]
theorem mvOpenCoverHomologyIso_hom (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (mvOpenCoverHomologyIso X U V hU hV hcover n).hom =
      HomologicalComplex.homologyMap (mvSmallInclusion X U V) n := rfl

theorem mvAmbientConnecting_comparison (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (mvOpenCoverHomologyIso X U V hU hV hcover (n + 1)).hom ≫
      mvAmbientConnecting X U V hU hV hcover n = mvConnecting X U V n := by
  simp only [mvAmbientConnecting, Iso.hom_inv_id_assoc]

end CurveComplexGenusTwo.CWHurewicz
