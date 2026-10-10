import CurveComplexGenusTwo.CWHurewicz.CWRelativeClean

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology

private noncomputable abbrev chainFunctor :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)

private noncomputable abbrev homologyFunctor (n : ℕ) :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)

/-- Restriction of a continuous map of topological pairs to the subspaces. -/
def pairMapOnSubspace {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) : TopCat.of ↥A ⟶ TopCat.of ↥B :=
  TopCat.ofHom ⟨fun x => ⟨f x.val, h x.val x.property⟩, by fun_prop⟩

/-- A map of pairs gives a commutative square of underlying spaces. -/
theorem pairMap_square {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) :
    pairInclusion X A ≫ TopCat.ofHom f =
      pairMapOnSubspace A B f h ≫ pairInclusion Y B := by
  ext x
  rfl

/-- Naturality of the inclusion map on absolute singular homology. -/
theorem pairHomologyInclusion_commutes
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ) :
    homologyInclusion X A n ≫ (homologyFunctor n).map (TopCat.ofHom f) =
      (homologyFunctor n).map (pairMapOnSubspace A B f h) ≫
        homologyInclusion Y B n := by
  change (homologyFunctor n).map (pairInclusion X A) ≫
      (homologyFunctor n).map (TopCat.ofHom f) =
    (homologyFunctor n).map (pairMapOnSubspace A B f h) ≫
      (homologyFunctor n).map (pairInclusion Y B)
  rw [← Functor.map_comp, pairMap_square A B f h, Functor.map_comp]

/-- The chain map on ambient spaces descends through the singular-chain quotient. -/
theorem pairRelativeChainMap_condition
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) :
    chainFunctor.map (pairInclusion X A) ≫
      (chainFunctor.map (TopCat.ofHom f) ≫
        cokernel.π (chainFunctor.map (pairInclusion Y B))) = 0 := by
  rw [← Category.assoc, ← Functor.map_comp, pairMap_square A B f h,
    Functor.map_comp, Category.assoc, cokernel.condition, comp_zero]

/-- The map on relative singular chains induced by a continuous map of pairs. -/
noncomputable def pairRelativeChainMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) :
    relativeSingularChains X A ⟶ relativeSingularChains Y B :=
  cokernel.desc (chainFunctor.map (pairInclusion X A))
    (chainFunctor.map (TopCat.ofHom f) ≫
      cokernel.π (chainFunctor.map (pairInclusion Y B)))
    (pairRelativeChainMap_condition A B f h)

/-- Naturality of the quotient map at the chain-complex level. -/
theorem pairRelativeChainMap_π
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) :
    cokernel.π (chainFunctor.map (pairInclusion X A)) ≫
        pairRelativeChainMap A B f h =
      chainFunctor.map (TopCat.ofHom f) ≫
        cokernel.π (chainFunctor.map (pairInclusion Y B)) := by
  exact cokernel.π_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The relative chain map induced by the identity pair map is the identity. -/
theorem pairRelativeChainMap_id {X : Type} [TopologicalSpace X]
    (A : Set X) :
    pairRelativeChainMap A A (ContinuousMap.id X) (fun _ hx => hx) =
      𝟙 (relativeSingularChains X A) := by
  change pairRelativeChainMap A A (ContinuousMap.id X) (fun _ hx => hx) =
    𝟙 (cokernel (chainFunctor.map (pairInclusion X A)))
  apply (cancel_epi (cokernel.π (chainFunctor.map (pairInclusion X A)))).1
  simp only [pairRelativeChainMap, cokernel.π_desc, Category.comp_id]
  change chainFunctor.map (𝟙 (TopCat.of X)) ≫
      cokernel.π (chainFunctor.map (pairInclusion X A)) =
    cokernel.π (chainFunctor.map (pairInclusion X A))
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Relative chain maps respect composition of maps of pairs. -/
theorem pairRelativeChainMap_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set X) (B : Set Y) (D : Set Z)
    (f : C(X, Y)) (g : C(Y, Z))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ y ∈ B, g y ∈ D) :
    pairRelativeChainMap A D (g.comp f)
        (fun x hx => hg (f x) (hf x hx)) =
      pairRelativeChainMap A B f hf ≫ pairRelativeChainMap B D g hg := by
  apply (cancel_epi (cokernel.π (chainFunctor.map (pairInclusion X A)))).1
  rw [pairRelativeChainMap_π]
  change chainFunctor.map (TopCat.ofHom (g.comp f)) ≫
      cokernel.π (chainFunctor.map (pairInclusion Z D)) =
    (cokernel.π (chainFunctor.map (pairInclusion X A)) ≫
      pairRelativeChainMap A B f hf) ≫ pairRelativeChainMap B D g hg
  calc
    _ = chainFunctor.map (TopCat.ofHom f) ≫
        (chainFunctor.map (TopCat.ofHom g) ≫
          cokernel.π (chainFunctor.map (pairInclusion Z D))) := by
      change chainFunctor.map (TopCat.ofHom f ≫ TopCat.ofHom g) ≫
          cokernel.π (chainFunctor.map (pairInclusion Z D)) = _
      rw [Functor.map_comp, Category.assoc]
    _ = chainFunctor.map (TopCat.ofHom f) ≫
        (cokernel.π (chainFunctor.map (pairInclusion Y B)) ≫
          pairRelativeChainMap B D g hg) := by
      rw [← pairRelativeChainMap_π]
    _ = (chainFunctor.map (TopCat.ofHom f) ≫
        cokernel.π (chainFunctor.map (pairInclusion Y B))) ≫
          pairRelativeChainMap B D g hg := by rw [Category.assoc]
    _ = _ := by rw [← pairRelativeChainMap_π]

/-- The induced map in relative integral singular homology. -/
noncomputable def pairRelativeHomologyMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ) :
    relativeHomology X A n ⟶ relativeHomology Y B n :=
  HomologicalComplex.homologyMap (pairRelativeChainMap A B f h) n

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the canonical map from absolute to relative homology. -/
theorem pairRelativeHomologyMap_commutes
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ) :
    homologyToRelative X A n ≫ pairRelativeHomologyMap A B f h n =
      HomologicalComplex.homologyMap
        (chainFunctor.map (TopCat.ofHom f)) n ≫
        homologyToRelative Y B n := by
  dsimp only [homologyToRelative, pairRelativeHomologyMap]
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun q => HomologicalComplex.homologyMap q n)
      (pairRelativeChainMap_π A B f h)

/-- Relative homology maps respect composition of maps of pairs. -/
theorem pairRelativeHomologyMap_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set X) (B : Set Y) (D : Set Z)
    (f : C(X, Y)) (g : C(Y, Z))
    (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ y ∈ B, g y ∈ D) (n : ℕ) :
    pairRelativeHomologyMap A D (g.comp f)
        (fun x hx => hg (f x) (hf x hx)) n =
      pairRelativeHomologyMap A B f hf n ≫
        pairRelativeHomologyMap B D g hg n := by
  dsimp only [pairRelativeHomologyMap]
  rw [← HomologicalComplex.homologyMap_comp, pairRelativeChainMap_comp]

theorem pairRelativeHomologyMap_id {X : Type} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    pairRelativeHomologyMap A A (ContinuousMap.id X) (fun _ hx => hx) n =
      𝟙 (relativeHomology X A n) := by
  dsimp only [pairRelativeHomologyMap]
  rw [pairRelativeChainMap_id]
  simp

#print axioms pairMap_square
#print axioms pairHomologyInclusion_commutes
#print axioms pairRelativeChainMap_condition
#print axioms pairRelativeChainMap
#print axioms pairRelativeChainMap_π
#print axioms pairRelativeChainMap_id
#print axioms pairRelativeChainMap_comp
#print axioms pairRelativeHomologyMap_commutes
#print axioms pairRelativeHomologyMap
#print axioms pairRelativeHomologyMap_comp
#print axioms pairRelativeHomologyMap_id

end CurveComplexGenusTwo.CWHurewicz
