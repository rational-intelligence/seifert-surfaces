import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Topology.CWComplex.Classical.Basic

/-!
Topology interfaces for Sections 6, 7, and 11 of
`references/curve-complex-genus-two.pdf`.

These proved generic interfaces still require source-specific instantiations.
Their use for the curve complex requires the
genuine geometric realization and the source-specific interfaces in
`INTERFACE.md`. In particular no finite-complex assumption is made.
-/

namespace CurveComplexGenusTwo.Topology

open Set
open CategoryTheory Limits AlgebraicTopology

abbrev Interval := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}

def timeZero : Interval := ⟨0, by norm_num⟩
def timeOne : Interval := ⟨1, by norm_num⟩

/-- A homotopy of the identity fixing `A` pointwise, ending inside `A`. -/
def IsStrongDeformationRetract {X : Type*} [TopologicalSpace X]
    (A : Set X) : Prop :=
  ∃ H : C(X × Interval, X),
    (∀ x : X, H (x, timeZero) = x) ∧
    (∀ x : X, H (x, timeOne) ∈ A) ∧
    (∀ x ∈ A, ∀ t : Interval, H (x, t) = x)

/-- The weak topology of an arbitrary cover by subspaces. The index type may
be infinite; this is the condition needed for the simultaneous deletion in 6.8. -/
def HasWeakTopologyFromCover {X : Type*} [tX : TopologicalSpace X]
    {I : Type*} (pieces : I → Set X) : Prop :=
  (⋃ i, pieces i = Set.univ) ∧
    tX = ⨆ i, TopologicalSpace.coinduced
      (fun x : pieces i => (x : X)) inferInstance

/-- Section 6.8: glue infinitely many local star homotopies with a fixed core.
All overlap agreement and the product weak-topology condition are explicit. -/
theorem strongDeformationRetract_of_weakStarCover
    {X I : Type*} [TopologicalSpace X]
    (core : Set X) (stars : I → Set X)
    (hcover : HasWeakTopologyFromCover (fun j : Option I =>
      match j with | none => core | some i => stars i))
    (hproduct : HasWeakTopologyFromCover (fun j : Option I =>
      match j with
      | none => {p : X × Interval | p.1 ∈ core}
      | some i => {p : X × Interval | p.1 ∈ stars i}))
    (H : ∀ i, C((stars i) × Interval, X))
    (hzero : ∀ i (x : stars i), H i (x, timeZero) = (x : X))
    (hend : ∀ i x, H i (x, timeOne) ∈ core)
    (hfix : ∀ i (x : stars i), (x : X) ∈ core →
      ∀ t : Interval, H i (x, t) = (x : X))
    (hoverlap : ∀ i j (x : X) (hi : x ∈ stars i) (hj : x ∈ stars j),
      ∀ t : Interval,
        H i (⟨x, hi⟩, t) = H j (⟨x, hj⟩, t)) :
    IsStrongDeformationRetract core := by
  classical
  have hstar (x : X) (hx : x ∉ core) : ∃ i, x ∈ stars i := by
    have hc : x ∈ ⋃ j : Option I, (match j with | none => core | some i => stars i) := by
      rw [hcover.1]
      trivial
    rcases Set.mem_iUnion.mp hc with ⟨j, hj⟩
    cases j with
    | none => exact False.elim (hx hj)
    | some i => exact ⟨i, hj⟩
  let F : X × Interval → X := fun p =>
    if hc : p.1 ∈ core then p.1
    else H (Classical.choose (hstar p.1 hc))
      (⟨p.1, Classical.choose_spec (hstar p.1 hc)⟩, p.2)
  have hcore (p : X × Interval) (hc : p.1 ∈ core) : F p = p.1 := by
    simp [F, hc]
  have hpiece (i : I) (p : X × Interval) (hp : p.1 ∈ stars i) :
      F p = H i (⟨p.1, hp⟩, p.2) := by
    by_cases hc : p.1 ∈ core
    · rw [hcore p hc]
      exact (hfix i ⟨p.1, hp⟩ hc p.2).symm
    · simp only [F, dif_neg hc]
      exact hoverlap _ i p.1 (Classical.choose_spec (hstar p.1 hc)) hp p.2
  have hcontinuous : Continuous F := by
    rw [hproduct.2]
    rw [continuous_iSup_dom]
    intro j
    rw [continuous_coinduced_dom]
    cases j with
    | none =>
      have heq : F ∘ (fun p : {p : X × Interval | p.1 ∈ core} => (p : X × Interval)) =
          fun p : {p : X × Interval | p.1 ∈ core} => (p : X × Interval).1 := by
        funext p
        exact hcore p p.property
      rw [heq]
      exact continuous_fst.comp continuous_subtype_val
    | some i =>
      have hfirst : Continuous (fun p : {p : X × Interval | p.1 ∈ stars i} =>
          (⟨(p : X × Interval).1, p.property⟩ : stars i)) := by
        exact Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _
      have hsecond : Continuous (fun p : {p : X × Interval | p.1 ∈ stars i} =>
          (p : X × Interval).2) :=
        continuous_snd.comp continuous_subtype_val
      have heq : F ∘ (fun p : {p : X × Interval | p.1 ∈ stars i} => (p : X × Interval)) =
          fun p : {p : X × Interval | p.1 ∈ stars i} =>
            H i (⟨(p : X × Interval).1, p.property⟩, (p : X × Interval).2) := by
        funext p
        exact hpiece i p p.property
      rw [heq]
      exact (H i).continuous.comp (hfirst.prodMk hsecond)
  refine ⟨⟨F, hcontinuous⟩, ?_, ?_, ?_⟩
  · intro x
    dsimp
    by_cases hc : x ∈ core
    · exact hcore (x, timeZero) hc
    · rw [hpiece (Classical.choose (hstar x hc)) (x, timeZero)
        (Classical.choose_spec (hstar x hc))]
      exact hzero _ _
  · intro x
    dsimp
    by_cases hc : x ∈ core
    · rw [hcore (x, timeOne) hc]
      exact hc
    · rw [hpiece (Classical.choose (hstar x hc)) (x, timeOne)
        (Classical.choose_spec (hstar x hc))]
      exact hend _ _
  · intro x hx t
    dsimp
    exact hcore (x, t) hx

/-- The core of the deletion argument: there may be infinitely many stars,
but no simplex contains two deleted vertices. This is the topological result
claimed by Theorem 6.8 once its combinatorial and CW hypotheses are built. -/
theorem simultaneousStarDeletion
    {X I : Type*} [TopologicalSpace X]
    (core : Set X) (stars links : I → Set X)
    (hcover : HasWeakTopologyFromCover (fun j : Option I =>
      match j with | none => core | some i => stars i))
    (hstarCore : ∀ i, stars i ∩ core = links i)
    (hstarStar : ∀ i j, i ≠ j → stars i ∩ stars j ⊆ core)
    (hlocal : ∀ i, IsStrongDeformationRetract
      {x : stars i | (x : X) ∈ links i})
    (hproduct : HasWeakTopologyFromCover (fun j : Option I =>
      match j with
      | none => {p : X × Interval | p.1 ∈ core}
      | some i => {p : X × Interval | p.1 ∈ stars i})) :
    IsStrongDeformationRetract core := by
  classical
  let L (i : I) := Classical.choose (hlocal i)
  have hL (i : I) := Classical.choose_spec (hlocal i)
  let H (i : I) : C((stars i) × Interval, X) :=
    ⟨fun p => ((L i p : stars i) : X), continuous_subtype_val.comp (L i).continuous⟩
  apply strongDeformationRetract_of_weakStarCover core stars hcover hproduct H
  · intro i x
    exact congrArg Subtype.val ((hL i).1 x)
  · intro i x
    have hx : ((L i (x, timeOne) : stars i) : X) ∈ links i := (hL i).2.1 x
    rw [← hstarCore i] at hx
    exact hx.2
  · intro i x hx t
    have hlink : (x : X) ∈ links i := by
      rw [← hstarCore i]
      exact ⟨x.property, hx⟩
    exact congrArg Subtype.val ((hL i).2.2 x hlink t)
  · intro i j x hi hj t
    by_cases hij : i = j
    · subst j
      rfl
    · have hc : x ∈ core := hstarStar i j hij ⟨hi, hj⟩
      calc
        H i (⟨x, hi⟩, t) = x := by
          have hlink : x ∈ links i := by
            rw [← hstarCore i]
            exact ⟨hi, hc⟩
          exact congrArg Subtype.val ((hL i).2.2 ⟨x, hi⟩ hlink t)
        _ = H j (⟨x, hj⟩, t) := by
          symm
          have hlink : x ∈ links j := by
            rw [← hstarCore j]
            exact ⟨hj, hc⟩
          exact congrArg Subtype.val ((hL j).2.2 ⟨x, hj⟩ hlink t)

/-- Section 7.7: the all-genus conclusion after Harer's theorem gives
simple connectivity of the zero-curve complex and edge filling gives π₁
surjectivity. This is independent of the genus-two arc dictionary. -/
theorem simplyConnected_of_pi1Surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] (f : C(X, Y))
    (hY : PathConnectedSpace Y)
    (hpi : ∀ x : X, Function.Surjective (FundamentalGroup.map f x)) :
    SimplyConnectedSpace Y := by
  letI : PathConnectedSpace Y := hY
  letI : PathConnectedSpace X := inferInstance
  let x : X := Classical.choice PathConnectedSpace.nonempty
  have hbase : ∀ a b : FundamentalGroup Y (f x), a = b := by
    intro a b
    obtain ⟨a', rfl⟩ := hpi x a
    obtain ⟨b', rfl⟩ := hpi x b
    congr 1
    exact Subsingleton.elim a' b'
  have hall (y : Y) : ∀ a b : FundamentalGroup Y y, a = b := by
    let e := FundamentalGroup.fundamentalGroupMulEquivOfPath
      (PathConnectedSpace.somePath (f x) y)
    intro a b
    calc
      a = e (e.symm a) := (e.apply_symm_apply a).symm
      _ = e (e.symm b) := congrArg e (hbase (e.symm a) (e.symm b))
      _ = b := e.apply_symm_apply b
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨hY, ?_⟩
  intro y γ
  exact Quotient.eq.mp (hall y (⟦γ⟧ : FundamentalGroup Y y) 1)

/-- A supplementary interface for Souto's Proposition 7.8: factoring an
inclusion through a contractible arc-and-curve complex makes it nullhomotopic. -/
theorem nullhomotopic_of_factors_through_contractible
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [ContractibleSpace Z]
    (u : C(X, Z)) (v : C(Z, Y)) :
    ∃ y : Y, ContinuousMap.Homotopic (v.comp u) (ContinuousMap.const X y) := by
  exact (id_nullhomotopic Z).comp_right v |>.comp_left u

set_option synthInstance.maxHeartbeats 1000000

/-- Vanishing reduced integral singular homology: positive-degree homology
vanishes and degree-zero augmentation is an isomorphism. -/
def IsAcyclicIntegral (X : Type) [TopologicalSpace X] : Prop :=
  let Y := TopCat.of X
  let R := ModuleCat.of ℤ ℤ
  (∀ n : ℕ, 0 < n →
    CategoryTheory.Limits.IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj R).obj Y)) ∧
  CategoryTheory.IsIso (Y.singularHomology₀ε R)

/-- Theorem 11.2 transfer from the arc model `X` to the whole 1-curve
complex via the homotopy equivalence of Theorem 6.8. -/
theorem acyclic_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (hX : IsAcyclicIntegral X) :
    IsAcyclicIntegral Y := by
  classical
  change (∀ n : ℕ, 0 < n →
    CategoryTheory.Limits.IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))) ∧
    CategoryTheory.IsIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ)) at hX
  change (∀ n : ℕ, 0 < n →
    CategoryTheory.Limits.IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y))) ∧
    CategoryTheory.IsIso ((TopCat.of Y).singularHomology₀ε (ModuleCat.of ℤ ℤ))
  constructor
  · intro n hn
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)
    let f := TopCat.ofHom e.toFun
    let g := TopCat.ofHom e.invFun
    let hIso : F.obj (TopCat.of X) ≅ F.obj (TopCat.of Y) := by
      refine ⟨F.map f, F.map g, ?_, ?_⟩
      · rw [← F.map_comp, ← F.map_id]
        exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
          e.left_inv.some (ModuleCat.of ℤ ℤ) n
      · rw [← F.map_comp, ← F.map_id]
        exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
          e.right_inv.some (ModuleCat.of ℤ ℤ) n
    exact hIso.isZero_iff.mp (hX.1 n hn)
  · let R := ModuleCat.of ℤ ℤ
    let F := (singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj R
    have hNatSSet {U V : SSet} (f : U ⟶ V) :
        SSet.homologyMap f R 0 ≫ V.homology₀ε R = U.homology₀ε R := by
      let K := U.chainComplex R
      let q : K.X 0 ⟶ U.homology R 0 := K.cycles₀Iso.inv ≫ K.homologyπ 0
      let L := V.chainComplex R
      let φ := SSet.chainComplexMap f R
      have hnat : K.cycles₀Iso.inv ≫ HomologicalComplex.cyclesMap φ 0 =
          φ.f 0 ≫ L.cycles₀Iso.inv := by
        have hK : K.cycles₀Iso.inv ≫ K.iCycles 0 = 𝟙 _ := by
          exact K.iCyclesIso_inv_hom_id 0 0 (by simp) (by simp)
        rw [← cancel_mono (L.iCycles 0)]
        simp only [Category.assoc]
        rw [HomologicalComplex.cyclesMap_i]
        change (K.cycles₀Iso.inv ≫ K.iCycles 0) ≫ φ.f 0 =
          (φ.f 0 ≫ L.cycles₀Iso.inv) ≫ L.iCycles 0
        rw [hK, Category.id_comp, Category.assoc]
        rw [L.iCyclesIso_inv_hom_id 0 0 (by simp) (by simp), Category.comp_id]
      haveI : Epi q := inferInstance
      rw [← cancel_epi q]
      apply Limits.Sigma.hom_ext
      intro x
      have hliftU : U.ιChainComplex x ≫ K.cycles₀Iso.inv =
          K.liftCycles (U.ιChainComplex x) 0 (by simp) (by simp) := by
        rw [← cancel_mono (K.iCycles 0)]
        rw [Category.assoc, K.iCyclesIso_inv_hom_id 0 0 (by simp) (by simp)]
        rw [K.liftCycles_i]
        exact Category.comp_id _
      have haugU : U.ιChainComplex x ≫ K.cycles₀Iso.inv ≫
          K.homologyπ 0 ≫ U.homology₀ε R = 𝟙 R := by
        simp only [← Category.assoc]
        rw [hliftU]
        exact U.liftCycles_ιChainComplex_homologyπ_homology₀ε R x
      have hliftV : V.ιChainComplex (f.app _ x) ≫ L.cycles₀Iso.inv =
          L.liftCycles (V.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) := by
        rw [← cancel_mono (L.iCycles 0)]
        rw [Category.assoc, L.iCyclesIso_inv_hom_id 0 0 (by simp) (by simp)]
        rw [L.liftCycles_i]
        exact Category.comp_id _
      have haugV : V.ιChainComplex (f.app _ x) ≫ L.cycles₀Iso.inv ≫
          L.homologyπ 0 ≫ V.homology₀ε R = 𝟙 R := by
        simp only [← Category.assoc]
        rw [hliftV]
        exact V.liftCycles_ιChainComplex_homologyπ_homology₀ε R (f.app _ x)
      calc
        _ = U.ιChainComplex x ≫
          (K.cycles₀Iso.inv ≫ HomologicalComplex.cyclesMap φ 0) ≫
          L.homologyπ 0 ≫ V.homology₀ε R := by
            have hh := congrArg
              (fun z => U.ιChainComplex x ≫ K.cycles₀Iso.inv ≫ z ≫ V.homology₀ε R)
              (HomologicalComplex.homologyπ_naturality (φ := φ) (i := 0))
            simpa only [q, SSet.homologyMap, SSet.ιChainComplex, Category.assoc] using hh
        _ = U.ιChainComplex x ≫ (φ.f 0 ≫ L.cycles₀Iso.inv) ≫
          L.homologyπ 0 ≫ V.homology₀ε R := by rw [hnat]
        _ = U.ιChainComplex x ≫ K.cycles₀Iso.inv ≫
          K.homologyπ 0 ≫ U.homology₀ε R := by
          simp only [← Category.assoc]
          rw [SSet.ι_chainComplexMap_f]
          exact haugV.trans haugU.symm
    have hNat (f : C(Y, X)) :
        F.map (TopCat.ofHom f) ≫ (TopCat.of X).singularHomology₀ε R =
          (TopCat.of Y).singularHomology₀ε R := by
      change SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom f)) R 0 ≫
          (TopCat.toSSet.obj (TopCat.of X)).homology₀ε R =
        (TopCat.toSSet.obj (TopCat.of Y)).homology₀ε R
      exact hNatSSet _
    let f := TopCat.ofHom e.toFun
    let g := TopCat.ofHom e.invFun
    haveI : IsIso (F.map g) := by
      refine ⟨⟨F.map f, ?_, ?_⟩⟩
      · rw [← F.map_comp, ← F.map_id]
        exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
          e.right_inv.some R 0
      · rw [← F.map_comp, ← F.map_id]
        exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
          e.left_inv.some R 0
    letI : IsIso ((TopCat.of X).singularHomology₀ε R) := hX.2
    rw [← hNat e.invFun]
    infer_instance

/-- Corollary 11.3: the nonseparating complex is contractible because it is
homotopy equivalent to the whole complex. -/
theorem contractible_of_homotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) [ContractibleSpace Y] :
    ContractibleSpace X := by
  exact e.contractibleSpace

end CurveComplexGenusTwo.Topology
