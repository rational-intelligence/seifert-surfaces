import CurveComplexGenusTwo.CWHurewicz.DegreeOneRelative
import CurveComplexGenusTwo.CWHurewicz.WedgeGeometry
import CurveComplexGenusTwo.CWHurewicz.ExcisionDifferentialTransport
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Topology.Category.TopCat.EpiMono
import CurveComplexGenusTwo.CWHurewicz.CapGeometry
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Topology.Category.TopCat.EpiMono
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface

/-!
The geometric Hurewicz map: collapse the boundary of a based cube to a point,
then send its integral fundamental class through singular homology. Choosing
an orientation changes the map by sign but not its isomorphism property.
-/

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Topology unitInterval OnePoint

/-- A concrete topological `n`-sphere (unchanged reviewed recovery definition). -/
abbrev SphereSpace (n : ℕ) :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- All boundary points of the unit cube represent one point of its sphere
quotient. Interior points remain distinct. -/
def cubeBoundarySetoid (n : ℕ) : Setoid (Fin n → I) where
  r a b := a = b ∨
    (a ∈ Cube.boundary (Fin n) ∧ b ∈ Cube.boundary (Fin n))
  iseqv := by
    constructor
    · intro a
      exact Or.inl rfl
    · intro a b h
      rcases h with h | ⟨ha, hb⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hb, ha⟩
    · intro a b c hab hbc
      rcases hab with hab | ⟨ha, hb⟩
      · simpa [hab] using hbc
      · rcases hbc with hbc | ⟨hb', hc⟩
        · exact Or.inr ⟨ha, hbc ▸ hb⟩
        · exact Or.inr ⟨ha, hc⟩

abbrev CubeSphere (n : ℕ) := Quotient (cubeBoundarySetoid n)

instance cubeSphereTopology (n : ℕ) : TopologicalSpace (CubeSphere n) :=
  TopologicalSpace.coinduced (Quotient.mk (cubeBoundarySetoid n)) inferInstance

private theorem cubeBoundary_isClosed (n : ℕ) :
    IsClosed (Cube.boundary (Fin n) : Set (Fin n → I)) := by
  have h : (Cube.boundary (Fin n) : Set (Fin n → I)) =
      ⋃ i : Fin n, ({a | a i = 0} ∪ {a | a i = 1}) := by
    ext a
    simp only [Cube.boundary, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union]
  rw [h]
  apply isClosed_iUnion_of_finite
  intro i
  exact ((isClosed_singleton.preimage (continuous_apply i)).union
    (isClosed_singleton.preimage (continuous_apply i)))

private def cubeInterior (n : ℕ) : Set (Fin n → I) :=
  (Cube.boundary (Fin n))ᶜ

private theorem cubeInterior_isOpen (n : ℕ) : IsOpen (cubeInterior n) := by
  have h : (Cube.boundary (Fin n) : Set (Fin n → I)) =
      ⋃ i : Fin n, ({a | a i = 0} ∪ {a | a i = 1}) := by
    ext a
    simp only [Cube.boundary, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union]
  exact (h ▸ isClosed_iUnion_of_finite (fun i =>
    ((isClosed_singleton.preimage (continuous_apply i)).union
      (isClosed_singleton.preimage (continuous_apply i))))).isOpen_compl

private noncomputable def cubeCollapse (n : ℕ) (a : Fin n → I) :
    OnePoint (cubeInterior n) := by
  classical
  exact if h : a ∈ Cube.boundary (Fin n) then ∞
    else (⟨a, h⟩ : cubeInterior n)

private theorem cubeCollapse_boundary (n : ℕ) {a : Fin n → I}
    (ha : a ∈ Cube.boundary (Fin n)) : cubeCollapse n a = ∞ := by
  simp [cubeCollapse, ha]

private theorem cubeCollapse_interior (n : ℕ) {a : Fin n → I}
    (ha : a ∉ Cube.boundary (Fin n)) :
    cubeCollapse n a = (⟨a, ha⟩ : cubeInterior n) := by
  simp [cubeCollapse, ha]

private theorem cubeCollapse_continuous (n : ℕ) : Continuous (cubeCollapse n) := by
  rw [continuous_def]
  intro s hs
  let U := cubeInterior n
  let A : Set U := ((↑) : U → OnePoint U) ⁻¹' s
  have himage (B : Set U) (a : Fin n → I)
      (ha : a ∉ Cube.boundary (Fin n)) :
      a ∈ Subtype.val '' B ↔ (⟨a, ha⟩ : U) ∈ B := by
    constructor
    · rintro ⟨u, hu, heq⟩
      have he : u = (⟨a, ha⟩ : U) := Subtype.ext heq
      simpa [he] using hu
    · intro hu
      exact ⟨⟨a, ha⟩, hu, rfl⟩
  have hnoimage (B : Set U) (a : Fin n → I)
      (ha : a ∈ Cube.boundary (Fin n)) :
      a ∉ Subtype.val '' B := by
    rintro ⟨u, _, heq⟩
    exact u.property (heq ▸ ha)
  by_cases hInf : (∞ : OnePoint U) ∈ s
  · have hA : IsCompact Aᶜ := ((OnePoint.isOpen_iff_of_mem hInf).mp hs).2
    have heq : cubeCollapse n ⁻¹' s = (Subtype.val '' Aᶜ)ᶜ := by
      ext a
      by_cases ha : a ∈ Cube.boundary (Fin n)
      · have hau : a ∉ U := by simpa [U, cubeInterior] using ha
        simp [cubeCollapse_boundary n ha, hInf, hau]
      · change cubeCollapse n a ∈ s ↔ a ∉ Subtype.val '' Aᶜ
        rw [cubeCollapse_interior n ha, himage Aᶜ a ha]
        simp [A]
    rw [heq]
    exact (hA.image continuous_subtype_val).isClosed.isOpen_compl
  · have hA : IsOpen A := (OnePoint.isOpen_iff_of_notMem hInf).mp hs
    have heq : cubeCollapse n ⁻¹' s = Subtype.val '' A := by
      ext a
      by_cases ha : a ∈ Cube.boundary (Fin n)
      · simp [cubeCollapse_boundary n ha, hInf, hnoimage A a ha]
      · change cubeCollapse n a ∈ s ↔ a ∈ Subtype.val '' A
        rw [cubeCollapse_interior n ha, himage A a ha]
        rfl
    rw [heq]
    exact (cubeInterior_isOpen n).isOpenMap_subtype_val A hA

private noncomputable def cubeQuotientToOnePoint (n : ℕ) :
    CubeSphere n → OnePoint (cubeInterior n) :=
  Quotient.lift (cubeCollapse n) (by
    intro a b hab
    rcases hab with hab | ⟨ha, hb⟩
    · exact congrArg (cubeCollapse n) hab
    · rw [cubeCollapse_boundary n ha, cubeCollapse_boundary n hb])

private theorem cubeQuotientToOnePoint_continuous (n : ℕ) :
    Continuous (cubeQuotientToOnePoint n) := by
  apply continuous_coinduced_dom.mpr
  exact cubeCollapse_continuous n

private theorem cubeQuotientToOnePoint_surjective (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (cubeQuotientToOnePoint n) := by
  intro z
  induction z using OnePoint.rec with
  | infty =>
      let a : Fin n → I := fun _ => 0
      have ha : a ∈ Cube.boundary (Fin n) :=
        ⟨⟨0, by omega⟩, Or.inl rfl⟩
      exact ⟨Quotient.mk (cubeBoundarySetoid n) a,
        cubeCollapse_boundary n ha⟩
  | coe u =>
      exact ⟨Quotient.mk (cubeBoundarySetoid n) u.val,
        cubeCollapse_interior n u.property⟩

private theorem cubeQuotientToOnePoint_injective (n : ℕ) :
    Function.Injective (cubeQuotientToOnePoint n) := by
  intro z w h
  induction z using Quotient.inductionOn with
  | _ a =>
    induction w using Quotient.inductionOn with
    | _ b =>
      change cubeCollapse n a = cubeCollapse n b at h
      by_cases ha : a ∈ Cube.boundary (Fin n)
      · by_cases hb : b ∈ Cube.boundary (Fin n)
        · exact Quotient.sound (Or.inr ⟨ha, hb⟩)
        · rw [cubeCollapse_boundary n ha, cubeCollapse_interior n hb] at h
          exact False.elim (OnePoint.infty_ne_coe _ h)
      · by_cases hb : b ∈ Cube.boundary (Fin n)
        · rw [cubeCollapse_interior n ha, cubeCollapse_boundary n hb] at h
          exact False.elim (OnePoint.coe_ne_infty _ h)
        · rw [cubeCollapse_interior n ha, cubeCollapse_interior n hb] at h
          have hab : a = b := congrArg Subtype.val (OnePoint.coe_injective h)
          exact Quotient.sound (Or.inl hab)

private noncomputable def cubeQuotientOnePointHomeo (n : ℕ) (hn : 1 ≤ n) :
    CubeSphere n ≃ₜ OnePoint (cubeInterior n) := by
  letI : CompactSpace (CubeSphere n) := Quotient.compactSpace
  letI : LocallyCompactSpace (cubeInterior n) :=
    (cubeInterior_isOpen n).locallyCompactSpace
  let e := Equiv.ofBijective (cubeQuotientToOnePoint n)
    ⟨cubeQuotientToOnePoint_injective n, cubeQuotientToOnePoint_surjective n hn⟩
  exact Continuous.homeoOfEquivCompactToT2 (show Continuous e from
    cubeQuotientToOnePoint_continuous n)

private noncomputable def cubeInteriorPiHomeo (n : ℕ) :
    cubeInterior n ≃ₜ (Fin n → ↥(Ioo (0 : I) 1)) where
  toFun a i := ⟨a.val i, by
    have ha0 : a.val i ≠ 0 := by
      intro hi
      exact a.property ⟨i, Or.inl hi⟩
    have ha1 : a.val i ≠ 1 := by
      intro hi
      exact a.property ⟨i, Or.inr hi⟩
    exact ⟨lt_of_le_of_ne bot_le ha0.symm, lt_of_le_of_ne le_top ha1⟩⟩
  invFun b := ⟨fun i => b i, by
    intro h
    rcases h with ⟨i, hi | hi⟩
    · exact (ne_of_gt (b i).property.1) hi
    · exact (ne_of_lt (b i).property.2) hi⟩
  left_inv a := by ext i; rfl
  right_inv b := by ext i; rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by fun_prop

private noncomputable def realOpenIntervalHomeo : ℝ ≃ₜ ↥(Ioo (0 : I) 1) :=
  Topology.isEmbedding_sigmoid.toHomeomorph.trans
    (Homeomorph.setCongr unitInterval.range_sigmoid)

private noncomputable def cubeInteriorRealHomeo (n : ℕ) :
    cubeInterior n ≃ₜ (Fin n → ℝ) :=
  (cubeInteriorPiHomeo n).trans
    (Homeomorph.piCongrRight (fun _ : Fin n => realOpenIntervalHomeo.symm))

private noncomputable def cubeSphereChart (n : ℕ) (hn : 1 ≤ n) :
    CubeSphere n ≃ₜ SphereSpace n := by
  let h := cubeQuotientOnePointHomeo n hn
  let g := (cubeInteriorRealHomeo n).onePointCongr
  let k := onePointEquivSphereOfFinrankEq (ι := Fin (n + 1))
    (V := Fin n → ℝ) (by simp)
  exact h.trans (g.trans k)

/-- The quotient sphere agrees topologically with the standard sphere.
This bridge must be proved; it is not a definition by a hidden constant. -/
theorem cubeSphereHomeomorphic (n : ℕ) (_hn : 1 ≤ n) :
    Nonempty (CubeSphere n ≃ₜ SphereSpace n) :=
  ⟨cubeSphereChart n _hn⟩

/-- A based cube map is constant on its boundary, so it descends to the
quotient sphere. -/
noncomputable def loopSphereMap {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X) (f : GenLoop (Fin n) X x) :
    C(CubeSphere n, X) :=
  ⟨Quotient.lift (fun a => f a) (by
      intro a b hab
      rcases hab with hab | ⟨ha, hb⟩
      · exact congrArg (fun y => f y) hab
      · exact (GenLoop.boundary f a ha).trans (GenLoop.boundary f b hb).symm),
    by
      apply continuous_coinduced_dom.mpr
      exact f.1.continuous⟩

private noncomputable def cubeSphereBasepoint (n : ℕ) : CubeSphere n :=
  Quotient.mk (cubeBoundarySetoid n) (fun _ => 0)

private noncomputable def cubeSphereIdentityLoop (n : ℕ) (hn : 1 ≤ n) :
    GenLoop (Fin n) (CubeSphere n) (cubeSphereBasepoint n) := by
  refine ⟨⟨Quotient.mk (cubeBoundarySetoid n), ?_⟩, ?_⟩
  · exact continuous_coinduced_rng
  · intro a ha
    apply Quotient.sound
    exact Or.inr ⟨ha, ⟨⟨0, by omega⟩, Or.inl rfl⟩⟩

/-- The two folds of the cubical pinch, expressed as continuous maps from
the boundary quotient. The two halves are the `transAt` maps in Mathlib. -/
private noncomputable def cubePinchFold (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    C(CubeSphere n, CubeSphere n × CubeSphere n) :=
  let e := cubeSphereIdentityLoop n hn
  let c : GenLoop (Fin n) (CubeSphere n) (cubeSphereBasepoint n) := GenLoop.const
  ⟨fun z => (loopSphereMap n (cubeSphereBasepoint n) (GenLoop.transAt i e c) z,
    loopSphereMap n (cubeSphereBasepoint n) (GenLoop.transAt i c e) z),
    (loopSphereMap n (cubeSphereBasepoint n) (GenLoop.transAt i e c)).continuous.prodMk
      (loopSphereMap n (cubeSphereBasepoint n) (GenLoop.transAt i c e)).continuous⟩

private theorem cubePinchFold_mem_wedge (n : ℕ) (hn : 1 ≤ n)
    (i : Fin n) (z : CubeSphere n) :
    (cubePinchFold n hn i z).1 = cubeSphereBasepoint n ∨
      (cubePinchFold n hn i z).2 = cubeSphereBasepoint n := by
  induction z using Quotient.inductionOn with
  | _ a =>
    change (GenLoop.transAt i (cubeSphereIdentityLoop n hn) GenLoop.const) a = _ ∨
      (GenLoop.transAt i GenLoop.const (cubeSphereIdentityLoop n hn)) a = _
    by_cases h : (a i : ℝ) ≤ 2⁻¹
    · right
      simp only [GenLoop.transAt, GenLoop.coe_copy]
      change (if (a i : ℝ) ≤ 1 / 2 then
        (GenLoop.const : GenLoop (Fin n) (CubeSphere n) (cubeSphereBasepoint n))
          (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i)))
        else (cubeSphereIdentityLoop n hn)
          (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i - 1)))) = _
      simp [h]
    · left
      simp only [GenLoop.transAt, GenLoop.coe_copy]
      change (if (a i : ℝ) ≤ 1 / 2 then
        (cubeSphereIdentityLoop n hn)
          (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i)))
        else (GenLoop.const : GenLoop (Fin n) (CubeSphere n) (cubeSphereBasepoint n))
          (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i - 1)))) = _
      simp [h]

private def cubeSphereWedge (n : ℕ) : Set (CubeSphere n × CubeSphere n) :=
  {p | p.1 = cubeSphereBasepoint n ∨ p.2 = cubeSphereBasepoint n}

private noncomputable def cubePinch (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    C(CubeSphere n, cubeSphereWedge n) :=
  ⟨fun z => ⟨cubePinchFold n hn i z, cubePinchFold_mem_wedge n hn i z⟩,
    (cubePinchFold n hn i).continuous.subtype_mk _⟩

private noncomputable def cubeWedgeFst (n : ℕ) :
    C(cubeSphereWedge n, CubeSphere n) :=
  ⟨fun z => z.1.1, continuous_fst.comp continuous_subtype_val⟩

private noncomputable def cubeWedgeSnd (n : ℕ) :
    C(cubeSphereWedge n, CubeSphere n) :=
  ⟨fun z => z.1.2, continuous_snd.comp continuous_subtype_val⟩

private theorem cubeWedgeFst_pinch (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    ∀ z, ((cubeWedgeFst n).comp (cubePinch n hn i)) z =
      (cubePinchFold n hn i z).1 := by
  intro z
  rfl

private theorem cubeWedgeSnd_pinch (n : ℕ) (hn : 1 ≤ n) (i : Fin n) :
    ∀ z, ((cubeWedgeSnd n).comp (cubePinch n hn i)) z =
      (cubePinchFold n hn i z).2 := by
  intro z
  rfl

private noncomputable def cubeWedgeInl (n : ℕ) :
    C(CubeSphere n, cubeSphereWedge n) :=
  ⟨fun z => ⟨(z, cubeSphereBasepoint n), Or.inr rfl⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩

private noncomputable def cubeWedgeInr (n : ℕ) :
    C(CubeSphere n, cubeSphereWedge n) :=
  ⟨fun z => ⟨(cubeSphereBasepoint n, z), Or.inl rfl⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

private theorem cubeWedgeFst_inl (n : ℕ) :
    (cubeWedgeFst n).comp (cubeWedgeInl n) = ContinuousMap.id _ := by
  ext z
  rfl

private theorem cubeWedgeSnd_inr (n : ℕ) :
    (cubeWedgeSnd n).comp (cubeWedgeInr n) = ContinuousMap.id _ := by
  ext z
  rfl

private theorem cubeWedgeFst_inr (n : ℕ) :
    (cubeWedgeFst n).comp (cubeWedgeInr n) =
      ContinuousMap.const _ (cubeSphereBasepoint n) := by
  ext z
  rfl

private theorem cubeWedgeSnd_inl (n : ℕ) :
    (cubeWedgeSnd n).comp (cubeWedgeInl n) =
      ContinuousMap.const _ (cubeSphereBasepoint n) := by
  ext z
  rfl

private theorem loopSphereMap_basepoint {X : Type} [TopologicalSpace X]
    (n : ℕ) (hn : 1 ≤ n) (x : X) (f : GenLoop (Fin n) X x) :
    loopSphereMap n x f (cubeSphereBasepoint n) = x := by
  change f (fun _ => 0) = x
  exact GenLoop.boundary f _ ⟨⟨0, by omega⟩, Or.inl rfl⟩

private noncomputable def cubeWedgeFold {X : Type} [TopologicalSpace X]
    (n : ℕ) (hn : 1 ≤ n) (x : X)
    (f g : GenLoop (Fin n) X x) : C(cubeSphereWedge n, X) := by
  classical
  letI : T2Space (CubeSphere n) := (cubeSphereChart n hn).symm.t2Space
  let A : Set (cubeSphereWedge n) :=
    {z | z.val.1 = cubeSphereBasepoint n}
  let B : Set (cubeSphereWedge n) :=
    {z | z.val.2 = cubeSphereBasepoint n}
  let F : cubeSphereWedge n → X := fun z =>
    if z.val.1 = cubeSphereBasepoint n then loopSphereMap n x g z.val.2
    else loopSphereMap n x f z.val.1
  have hA : IsClosed A := by
    exact isClosed_singleton.preimage
      (continuous_fst.comp continuous_subtype_val)
  have hB : IsClosed B := by
    exact isClosed_singleton.preimage
      (continuous_snd.comp continuous_subtype_val)
  have hcover : A ∪ B = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact z.property
  have hfa : ContinuousOn F A := by
    have hcont : ContinuousOn (fun z : cubeSphereWedge n =>
        loopSphereMap n x g z.val.2) A :=
      ((loopSphereMap n x g).continuous.comp
        (continuous_snd.comp continuous_subtype_val)).continuousOn
    apply hcont.congr
    intro z hz
    change z.val.1 = cubeSphereBasepoint n at hz
    simp [F, hz]
  have hfb : ContinuousOn F B := by
    have hcont : ContinuousOn (fun z : cubeSphereWedge n =>
        loopSphereMap n x f z.val.1) B :=
      ((loopSphereMap n x f).continuous.comp
        (continuous_fst.comp continuous_subtype_val)).continuousOn
    apply hcont.congr
    intro z hz
    by_cases h : z.val.1 = cubeSphereBasepoint n
    · simp [F, h, B] at hz ⊢
      rw [hz, loopSphereMap_basepoint n hn x g]
      exact (loopSphereMap_basepoint n hn x f).symm
    · simp [F, h]
  refine ⟨F, ?_⟩
  exact continuousOn_univ.mp (hcover ▸ hfa.union_of_isClosed hfb hA hB)

private theorem cubeWedgeFold_inl {X : Type} [TopologicalSpace X]
    (n : ℕ) (hn : 1 ≤ n) (x : X) (f g : GenLoop (Fin n) X x) :
    (cubeWedgeFold n hn x f g).comp (cubeWedgeInl n) = loopSphereMap n x f := by
  ext z
  by_cases h : z = cubeSphereBasepoint n
  · subst z
    simp [cubeWedgeFold, cubeWedgeInl,
      loopSphereMap_basepoint n hn x f, loopSphereMap_basepoint n hn x g]
  · simp [cubeWedgeFold, cubeWedgeInl, h]

private theorem cubeWedgeFold_inr {X : Type} [TopologicalSpace X]
    (n : ℕ) (hn : 1 ≤ n) (x : X) (f g : GenLoop (Fin n) X x) :
    (cubeWedgeFold n hn x f g).comp (cubeWedgeInr n) = loopSphereMap n x g := by
  ext z
  simp [cubeWedgeFold, cubeWedgeInr]

private theorem loopSphereMap_transAt_factor {X : Type} [TopologicalSpace X]
    (n : ℕ) (hn : 1 ≤ n) (x : X)
    (f g : GenLoop (Fin n) X x) (i : Fin n) :
    loopSphereMap n x (GenLoop.transAt i f g) =
      (cubeWedgeFold n hn x f g).comp (cubePinch n hn i) := by
  ext z
  induction z using Quotient.inductionOn with
  | _ a =>
    by_cases h : (a i : ℝ) ≤ 1 / 2
    · have hsecond : (cubePinch n hn i (Quotient.mk _ a)).val.2 =
          cubeSphereBasepoint n := by
        change (GenLoop.transAt i GenLoop.const
          (cubeSphereIdentityLoop n hn)) a = cubeSphereBasepoint n
        simp only [GenLoop.transAt, GenLoop.coe_copy]
        change (if (a i : ℝ) ≤ 1 / 2 then
          (GenLoop.const : GenLoop (Fin n) (CubeSphere n) (cubeSphereBasepoint n))
            (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i)))
          else (cubeSphereIdentityLoop n hn)
            (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i - 1)))) = _
        rw [if_pos h]
        rfl
      have hp : cubePinch n hn i (Quotient.mk _ a) =
          cubeWedgeInl n ((cubePinch n hn i (Quotient.mk _ a)).val.1) := by
        apply Subtype.ext
        exact Prod.ext rfl hsecond
      change (GenLoop.transAt i f g) a =
        cubeWedgeFold n hn x f g (cubePinch n hn i (Quotient.mk _ a))
      rw [hp]
      rw [← ContinuousMap.comp_apply, cubeWedgeFold_inl]
      have hfirst_eval : (cubePinch n hn i (Quotient.mk _ a)).val.1 =
          Quotient.mk (cubeBoundarySetoid n)
            (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i))) := by
        change (GenLoop.transAt i (cubeSphereIdentityLoop n hn) GenLoop.const) a = _
        simp only [GenLoop.transAt, GenLoop.coe_copy]
        change (if (a i : ℝ) ≤ 1 / 2 then
          (cubeSphereIdentityLoop n hn)
            (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i)))
          else (GenLoop.const : GenLoop (Fin n) (CubeSphere n) (cubeSphereBasepoint n))
            (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i - 1)))) = _
        rw [if_pos h]
        rfl
      rw [hfirst_eval]
      change (GenLoop.transAt i f g) a = f
        (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i)))
      simp only [GenLoop.transAt, GenLoop.coe_copy]
      change (if (a i : ℝ) ≤ 1 / 2 then
        f (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i)))
        else g (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i - 1)))) = _
      rw [if_pos h]
    · have hfirst : (cubePinch n hn i (Quotient.mk _ a)).val.1 =
          cubeSphereBasepoint n := by
        change (GenLoop.transAt i (cubeSphereIdentityLoop n hn)
          GenLoop.const) a = cubeSphereBasepoint n
        simp only [GenLoop.transAt, GenLoop.coe_copy]
        change (if (a i : ℝ) ≤ 1 / 2 then
          (cubeSphereIdentityLoop n hn)
            (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i)))
          else (GenLoop.const : GenLoop (Fin n) (CubeSphere n) (cubeSphereBasepoint n))
            (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i - 1)))) = _
        rw [if_neg h]
        rfl
      have hp : cubePinch n hn i (Quotient.mk _ a) =
          cubeWedgeInr n ((cubePinch n hn i (Quotient.mk _ a)).val.2) := by
        apply Subtype.ext
        exact Prod.ext hfirst rfl
      change (GenLoop.transAt i f g) a =
        cubeWedgeFold n hn x f g (cubePinch n hn i (Quotient.mk _ a))
      rw [hp]
      rw [← ContinuousMap.comp_apply, cubeWedgeFold_inr]
      have hsecond_eval : (cubePinch n hn i (Quotient.mk _ a)).val.2 =
          Quotient.mk (cubeBoundarySetoid n)
            (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i - 1))) := by
        change (GenLoop.transAt i GenLoop.const (cubeSphereIdentityLoop n hn)) a = _
        simp only [GenLoop.transAt, GenLoop.coe_copy]
        change (if (a i : ℝ) ≤ 1 / 2 then
          (GenLoop.const : GenLoop (Fin n) (CubeSphere n) (cubeSphereBasepoint n))
            (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i)))
          else (cubeSphereIdentityLoop n hn)
            (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i - 1)))) = _
        rw [if_neg h]
        rfl
      rw [hsecond_eval]
      change (GenLoop.transAt i f g) a = g
        (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i - 1)))
      simp only [GenLoop.transAt, GenLoop.coe_copy]
      change (if (a i : ℝ) ≤ 1 / 2 then
        f (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i)))
        else g (Function.update a i (Set.projIcc 0 1 zero_le_one (2 * a i - 1)))) = _
      rw [if_neg h]

private def cubeWedgeFirstAxis (n : ℕ) : Set (cubeSphereWedge n) :=
  {z | z.val.2 = cubeSphereBasepoint n}

private noncomputable def cubeWedgeFirstDistance (n : ℕ) (hn : 1 ≤ n) :
    cubeSphereWedge n → ℝ := fun z =>
  dist ((cubeSphereChart n hn) z.val.1)
    ((cubeSphereChart n hn) (cubeSphereBasepoint n))

private theorem cubeWedgeFirstDistance_continuous (n : ℕ) (hn : 1 ≤ n) :
    Continuous (cubeWedgeFirstDistance n hn) := by
  unfold cubeWedgeFirstDistance
  exact continuous_dist.comp
    (((cubeSphereChart n hn).continuous.comp
      (continuous_fst.comp continuous_subtype_val)).prodMk continuous_const)

private def cubeWedgeExciseFirst (n : ℕ) (hn : 1 ≤ n) :
    Set (cubeSphereWedge n) :=
  {z | (1 : ℝ) < cubeWedgeFirstDistance n hn z}

private theorem cubeWedgeExciseFirst_open (n : ℕ) (hn : 1 ≤ n) :
    IsOpen (cubeWedgeExciseFirst n hn) := by
  exact isOpen_Ioi.preimage (cubeWedgeFirstDistance_continuous n hn)

private theorem cubeWedgeExciseFirst_closure (n : ℕ) (hn : 1 ≤ n) :
    closure (cubeWedgeExciseFirst n hn) ⊆ interior (cubeWedgeFirstAxis n) := by
  let d := cubeWedgeFirstDistance n hn
  have hc : IsClosed {z : cubeSphereWedge n | (1 : ℝ) ≤ d z} :=
    isClosed_Ici.preimage (cubeWedgeFirstDistance_continuous n hn)
  have hu : cubeWedgeExciseFirst n hn ⊆ {z | (1 : ℝ) ≤ d z} := by
    intro z hz
    change (1 : ℝ) < d z at hz
    exact le_of_lt hz
  have hcl : closure (cubeWedgeExciseFirst n hn) ⊆
      {z : cubeSphereWedge n | (1 : ℝ) ≤ d z} := closure_minimal hu hc
  have ho : IsOpen {z : cubeSphereWedge n | (0 : ℝ) < d z} :=
    isOpen_Ioi.preimage (cubeWedgeFirstDistance_continuous n hn)
  have hsubset : {z : cubeSphereWedge n | (0 : ℝ) < d z} ⊆
      cubeWedgeFirstAxis n := by
    intro z hz
    rcases z.property with hzfirst | hzsecond
    · have hdist : d z = 0 := by
        simp [d, cubeWedgeFirstDistance, hzfirst]
      exact False.elim ((ne_of_gt hz) hdist)
    · exact hzsecond
  intro z hz
  apply (interior_maximal hsubset ho)
  exact lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) (hcl hz)

private def cubeSphereCap (n : ℕ) (hn : 1 ≤ n) : Set (CubeSphere n) :=
  {z | dist ((cubeSphereChart n hn) z)
    ((cubeSphereChart n hn) (cubeSphereBasepoint n)) ≤ 1}

private theorem cubeSphereChartBase_norm (n : ℕ) (hn : 1 ≤ n) :
    ‖((cubeSphereChart n hn) (cubeSphereBasepoint n)).val‖ = 1 := by
  have h := ((cubeSphereChart n hn) (cubeSphereBasepoint n)).property
  simpa [SphereSpace, Metric.mem_sphere, dist_zero_right] using h

private noncomputable def cubeSphereCapHomeo (n : ℕ) (hn : 1 ≤ n) :
    cubeSphereCap n hn ≃ₜ
      unitCap (((cubeSphereChart n hn) (cubeSphereBasepoint n)).val) := by
  let e := cubeSphereChart n hn
  let v : EuclideanSpace ℝ (Fin (n + 1)) := (e (cubeSphereBasepoint n)).val
  have hv : ‖v‖ = 1 := cubeSphereChartBase_norm n hn
  refine {
    toFun := fun z => ⟨(e z.val).val, ⟨by
      simpa [SphereSpace, Metric.mem_sphere, dist_zero_right] using (e z.val).property,
      z.property⟩⟩
    invFun := fun z => ⟨e.symm ⟨z.val, by
      change dist z.val 0 = 1
      simpa [dist_zero_right] using z.property.1⟩, by
        change dist (e (e.symm ⟨z.val, by
          change dist z.val 0 = 1
          simpa [dist_zero_right] using z.property.1⟩))
          (e (cubeSphereBasepoint n)) ≤ 1
        rw [e.apply_symm_apply]
        exact z.property.2⟩
    left_inv := by intro z; apply Subtype.ext; exact e.symm_apply_apply z.val
    right_inv := by
      intro z
      apply Subtype.ext
      change (e (e.symm ⟨z.val, by
        change dist z.val 0 = 1
        simpa [dist_zero_right] using z.property.1⟩)).val = z.val
      rw [e.apply_symm_apply]
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp
        (e.continuous.comp continuous_subtype_val)
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact e.symm.continuous.comp
        (continuous_subtype_val.subtype_mk _) }

private theorem cubeSphereBasepoint_mem_cap (n : ℕ) (hn : 1 ≤ n) :
    cubeSphereBasepoint n ∈ cubeSphereCap n hn := by
  simp [cubeSphereCap]

private noncomputable def cubeSphereCapContraction (n : ℕ) (hn : 1 ≤ n) :
    I × cubeSphereCap n hn → cubeSphereCap n hn := fun p =>
  let e := cubeSphereCapHomeo n hn
  let v := ((cubeSphereChart n hn) (cubeSphereBasepoint n)).val
  e.symm (capContraction v (cubeSphereChartBase_norm n hn) (p.1, e p.2))

private theorem cubeSphereCapContraction_continuous (n : ℕ) (hn : 1 ≤ n) :
    Continuous (cubeSphereCapContraction n hn) := by
  let e := cubeSphereCapHomeo n hn
  let v := ((cubeSphereChart n hn) (cubeSphereBasepoint n)).val
  unfold cubeSphereCapContraction
  exact e.symm.continuous.comp
    ((capContraction_continuous v (cubeSphereChartBase_norm n hn)).comp
      (continuous_fst.prodMk (e.continuous.comp continuous_snd)))

private theorem cubeSphereCapContraction_zero (n : ℕ) (hn : 1 ≤ n)
    (z : cubeSphereCap n hn) :
    cubeSphereCapContraction n hn (0, z) = z := by
  unfold cubeSphereCapContraction
  simp [capContraction_zero]

private theorem cubeSphereCapContraction_one (n : ℕ) (hn : 1 ≤ n)
    (z : cubeSphereCap n hn) :
    (cubeSphereCapContraction n hn (1, z)).val = cubeSphereBasepoint n := by
  let e := cubeSphereCapHomeo n hn
  have h : e (cubeSphereCapContraction n hn (1, z)) =
      e ⟨cubeSphereBasepoint n, cubeSphereBasepoint_mem_cap n hn⟩ := by
    apply Subtype.ext
    change (e (e.symm (capContraction
      (((cubeSphereChart n hn) (cubeSphereBasepoint n)).val)
      (cubeSphereChartBase_norm n hn) (1, e z)))).val = _
    rw [e.apply_symm_apply]
    exact capContraction_one _ (cubeSphereChartBase_norm n hn) (e z)
  exact congrArg Subtype.val (e.injective h)

private theorem cubeSphereCapContraction_base (n : ℕ) (hn : 1 ≤ n) (t : I) :
    (cubeSphereCapContraction n hn
      (t, ⟨cubeSphereBasepoint n, cubeSphereBasepoint_mem_cap n hn⟩)).val =
        cubeSphereBasepoint n := by
  let e := cubeSphereCapHomeo n hn
  have h : e (cubeSphereCapContraction n hn
      (t, ⟨cubeSphereBasepoint n, cubeSphereBasepoint_mem_cap n hn⟩)) =
      e ⟨cubeSphereBasepoint n, cubeSphereBasepoint_mem_cap n hn⟩ := by
    apply Subtype.ext
    change (e (e.symm (capContraction
      (((cubeSphereChart n hn) (cubeSphereBasepoint n)).val)
      (cubeSphereChartBase_norm n hn)
      (t, e ⟨cubeSphereBasepoint n, cubeSphereBasepoint_mem_cap n hn⟩)))).val = _
    rw [e.apply_symm_apply]
    exact capContraction_base _ (cubeSphereChartBase_norm n hn) t
  exact congrArg Subtype.val (e.injective h)

private def cubeWedgeRetained (n : ℕ) (hn : 1 ≤ n) :
    Set (cubeSphereWedge n) := (cubeWedgeExciseFirst n hn)ᶜ

private def cubeWedgeRetainedFirstCap (n : ℕ) (hn : 1 ≤ n) :
    cubeWedgeRetained n hn → cubeSphereCap n hn := fun z =>
  ⟨z.val.val.1, by
    have hz : ¬(1 : ℝ) < cubeWedgeFirstDistance n hn z.val := z.property
    change dist ((cubeSphereChart n hn) z.val.val.1)
      ((cubeSphereChart n hn) (cubeSphereBasepoint n)) ≤ 1
    exact le_of_not_gt hz⟩

private theorem cubeWedgeRetainedFirstCap_continuous (n : ℕ) (hn : 1 ≤ n) :
    Continuous (cubeWedgeRetainedFirstCap n hn) := by
  exact (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

private noncomputable def cubeWedgeRetainedContraction (n : ℕ) (hn : 1 ≤ n) :
    I × cubeWedgeRetained n hn → cubeWedgeRetained n hn := fun p =>
  let a := cubeSphereCapContraction n hn
    (p.1, cubeWedgeRetainedFirstCap n hn p.2)
  ⟨⟨(a.val, p.2.val.val.2), by
      rcases p.2.val.property with hfirst | hsecond
      · left
        have ha : (cubeWedgeRetainedFirstCap n hn p.2).val = cubeSphereBasepoint n := hfirst
        have he : cubeWedgeRetainedFirstCap n hn p.2 =
            ⟨cubeSphereBasepoint n, cubeSphereBasepoint_mem_cap n hn⟩ := Subtype.ext ha
        have hc := cubeSphereCapContraction_base n hn p.1
        rw [← he] at hc
        exact hc
      · exact Or.inr hsecond⟩, by
    change ¬(1 : ℝ) < cubeWedgeFirstDistance n hn
      ⟨(a.val, p.2.val.val.2), by
        rcases p.2.val.property with hfirst | hsecond
        · left
          have ha : (cubeWedgeRetainedFirstCap n hn p.2).val = cubeSphereBasepoint n := hfirst
          have he : cubeWedgeRetainedFirstCap n hn p.2 =
              ⟨cubeSphereBasepoint n, cubeSphereBasepoint_mem_cap n hn⟩ := Subtype.ext ha
          have hc := cubeSphereCapContraction_base n hn p.1
          rw [← he] at hc
          exact hc
        · exact Or.inr hsecond⟩
    exact not_lt.mpr a.property⟩

private theorem cubeWedgeRetainedContraction_continuous
    (n : ℕ) (hn : 1 ≤ n) :
    Continuous (cubeWedgeRetainedContraction n hn) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hfirst : Continuous (fun p : I × cubeWedgeRetained n hn =>
      (cubeSphereCapContraction n hn
        (p.1, cubeWedgeRetainedFirstCap n hn p.2)).val) :=
    continuous_subtype_val.comp
      ((cubeSphereCapContraction_continuous n hn).comp
        (continuous_fst.prodMk
          ((cubeWedgeRetainedFirstCap_continuous n hn).comp continuous_snd)))
  have hsecond : Continuous (fun p : I × cubeWedgeRetained n hn => p.2.val.val.2) := by
    fun_prop
  exact hfirst.prodMk hsecond

private theorem cubeWedgeRetainedContraction_zero
    (n : ℕ) (hn : 1 ≤ n) (z : cubeWedgeRetained n hn) :
    cubeWedgeRetainedContraction n hn (0, z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val
      (cubeSphereCapContraction_zero n hn (cubeWedgeRetainedFirstCap n hn z))
  · rfl

private theorem cubeWedgeRetainedContraction_one_first
    (n : ℕ) (hn : 1 ≤ n) (z : cubeWedgeRetained n hn) :
    (cubeWedgeRetainedContraction n hn (1, z)).val.val.1 =
      cubeSphereBasepoint n := by
  exact cubeSphereCapContraction_one n hn (cubeWedgeRetainedFirstCap n hn z)

private theorem cubeWedgeRetainedContraction_fixes_second_axis
    (n : ℕ) (hn : 1 ≤ n) (t : I) (z : cubeWedgeRetained n hn)
    (hz : z.val.val.1 = cubeSphereBasepoint n) :
    cubeWedgeRetainedContraction n hn (t, z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have he : cubeWedgeRetainedFirstCap n hn z =
        ⟨cubeSphereBasepoint n, cubeSphereBasepoint_mem_cap n hn⟩ := Subtype.ext hz
    have hc := cubeSphereCapContraction_base n hn t
    rw [← he] at hc
    exact hc.trans hz.symm
  · rfl

private noncomputable def cubeWedgeRetainedInr (n : ℕ) (hn : 1 ≤ n) :
    C(CubeSphere n, cubeWedgeRetained n hn) :=
  ⟨fun z => ⟨cubeWedgeInr n z, by
      change ¬(1 : ℝ) < cubeWedgeFirstDistance n hn (cubeWedgeInr n z)
      simp [cubeWedgeFirstDistance, cubeWedgeInr]⟩,
    (cubeWedgeInr n).continuous.subtype_mk _⟩

private noncomputable def cubeWedgeRetainedSnd (n : ℕ) (hn : 1 ≤ n) :
    C(cubeWedgeRetained n hn, CubeSphere n) :=
  (cubeWedgeSnd n).comp ⟨Subtype.val, continuous_subtype_val⟩

private theorem cubeWedgeRetainedSnd_inr (n : ℕ) (hn : 1 ≤ n) :
    (cubeWedgeRetainedSnd n hn).comp (cubeWedgeRetainedInr n hn) =
      ContinuousMap.id _ := by
  ext z
  rfl

private noncomputable def cubeWedgeRetainedHomotopy (n : ℕ) (hn : 1 ≤ n) :
    TopCat.Homotopy
      (𝟙 (TopCat.of (cubeWedgeRetained n hn)))
      (TopCat.ofHom ((cubeWedgeRetainedInr n hn).comp
        (cubeWedgeRetainedSnd n hn))) :=
  { toContinuousMap :=
      ⟨cubeWedgeRetainedContraction n hn,
        cubeWedgeRetainedContraction_continuous n hn⟩
    map_zero_left := cubeWedgeRetainedContraction_zero n hn
    map_one_left := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact cubeWedgeRetainedContraction_one_first n hn z
      · rfl }

private theorem cubeWedgeRetainedSnd_homology_isIso
    (n k : ℕ) (hn : 1 ≤ n) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom (cubeWedgeRetainedSnd n hn))) := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
    (ModuleCat.of ℤ ℤ)
  let f := TopCat.ofHom (cubeWedgeRetainedSnd n hn)
  let g := TopCat.ofHom (cubeWedgeRetainedInr n hn)
  have hfg : g ≫ f = 𝟙 (TopCat.of (CubeSphere n)) := by
    exact congrArg TopCat.ofHom (cubeWedgeRetainedSnd_inr n hn)
  have hgf : F.map (𝟙 (TopCat.of (cubeWedgeRetained n hn))) =
      F.map (f ≫ g) := by
    exact (cubeWedgeRetainedHomotopy n hn).congr_homologyMap_singularChainComplexFunctor
      (ModuleCat.of ℤ ℤ) k
  refine ⟨⟨F.map g, ?_, ?_⟩⟩
  · rw [← F.map_comp, ← hgf, F.map_id]
  · rw [← F.map_comp, hfg, F.map_id]

private def cubeWedgeRetainedFirstAxis (n : ℕ) (hn : 1 ≤ n) :
    Set (cubeWedgeRetained n hn) :=
  {z | z.val.val.2 = cubeSphereBasepoint n}

private noncomputable def cubeWedgeRetainedFirstAxisContraction
    (n : ℕ) (hn : 1 ≤ n) :
    I × cubeWedgeRetainedFirstAxis n hn → cubeWedgeRetainedFirstAxis n hn :=
  fun p => ⟨cubeWedgeRetainedContraction n hn (p.1, p.2.val), by
    exact p.2.property⟩

private theorem cubeWedgeRetainedFirstAxisContraction_continuous
    (n : ℕ) (hn : 1 ≤ n) :
    Continuous (cubeWedgeRetainedFirstAxisContraction n hn) := by
  apply Continuous.subtype_mk
  exact (cubeWedgeRetainedContraction_continuous n hn).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private noncomputable def cubeWedgeRetainedFirstAxisBase (n : ℕ) (hn : 1 ≤ n) :
    cubeWedgeRetainedFirstAxis n hn :=
  ⟨⟨cubeWedgeInr n (cubeSphereBasepoint n), by
    change ¬(1 : ℝ) < cubeWedgeFirstDistance n hn
      (cubeWedgeInr n (cubeSphereBasepoint n))
    simp [cubeWedgeFirstDistance, cubeWedgeInr]⟩, rfl⟩

private theorem cubeWedgeRetainedFirstAxisContraction_zero
    (n : ℕ) (hn : 1 ≤ n) (z : cubeWedgeRetainedFirstAxis n hn) :
    cubeWedgeRetainedFirstAxisContraction n hn (0, z) = z := by
  exact Subtype.ext (cubeWedgeRetainedContraction_zero n hn z.val)

private theorem cubeWedgeRetainedFirstAxisContraction_one
    (n : ℕ) (hn : 1 ≤ n) (z : cubeWedgeRetainedFirstAxis n hn) :
    cubeWedgeRetainedFirstAxisContraction n hn (1, z) =
      cubeWedgeRetainedFirstAxisBase n hn := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact cubeWedgeRetainedContraction_one_first n hn z.val
  · exact z.property

private noncomputable def cubeWedgeRetainedFirstAxisHomotopy
    (n : ℕ) (hn : 1 ≤ n) :
    TopCat.Homotopy
      (𝟙 (TopCat.of (cubeWedgeRetainedFirstAxis n hn)))
      (TopCat.ofHom (ContinuousMap.const _
        (cubeWedgeRetainedFirstAxisBase n hn))) :=
  { toContinuousMap :=
      ⟨cubeWedgeRetainedFirstAxisContraction n hn,
        cubeWedgeRetainedFirstAxisContraction_continuous n hn⟩
    map_zero_left := cubeWedgeRetainedFirstAxisContraction_zero n hn
    map_one_left := cubeWedgeRetainedFirstAxisContraction_one n hn }

private theorem cubeWedgeRetainedFirstAxis_homology_isZero
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    IsZero (H (cubeWedgeRetainedFirstAxis n hn) k) := by
  let A := cubeWedgeRetainedFirstAxis n hn
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
    (ModuleCat.of ℤ ℤ)
  let q : TopCat.of A ⟶ TopCat.of PUnit :=
    TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let p : TopCat.of PUnit ⟶ TopCat.of A :=
    TopCat.ofHom ⟨fun _ => cubeWedgeRetainedFirstAxisBase n hn,
      continuous_const⟩
  have hcomp : q ≫ p =
      TopCat.ofHom (ContinuousMap.const A (cubeWedgeRetainedFirstAxisBase n hn)) := by
    apply TopCat.Hom.ext
    apply ContinuousMap.ext
    intro z
    rfl
  have heq : F.map (𝟙 (TopCat.of A)) = F.map (q ≫ p) := by
    have h := (cubeWedgeRetainedFirstAxisHomotopy n hn).congr_homologyMap_singularChainComplexFunctor
      (ModuleCat.of ℤ ℤ) k
    change F.map (𝟙 (TopCat.of A)) =
      F.map (TopCat.ofHom (ContinuousMap.const A
        (cubeWedgeRetainedFirstAxisBase n hn))) at h
    simpa only [hcomp] using h
  have hzero : IsZero (H PUnit k) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℤ) k (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) (by omega)
  have hsub : Subsingleton (H PUnit k) :=
    ModuleCat.subsingleton_of_isZero hzero
  haveI : Subsingleton (H A k) := by
    constructor
    intro x y
    have hx : x = 0 := by
      calc
        x = (F.map (𝟙 (TopCat.of A))) x := by simp
        _ = (F.map (q ≫ p)) x := congrArg (fun f => f x) heq
        _ = (F.map p) ((F.map q) x) := by rw [F.map_comp]; rfl
        _ = 0 := by
          have hz : (F.map q) x = 0 := hsub.elim _ _
          rw [hz]
          simp
    have hy : y = 0 := by
      calc
        y = (F.map (𝟙 (TopCat.of A))) y := by simp
        _ = (F.map (q ≫ p)) y := congrArg (fun f => f y) heq
        _ = (F.map p) ((F.map q) y) := by rw [F.map_comp]; rfl
        _ = 0 := by
          have hz : (F.map q) y = 0 := hsub.elim _ _
          rw [hz]
          simp
    exact hx.trans hy.symm
  exact ModuleCat.isZero_of_subsingleton _

private theorem singleton_homology_isZero {X : Type} [TopologicalSpace X]
    (x : X) (k : ℕ) (hk : 1 ≤ k) :
    IsZero (H (↥({x} : Set X)) k) := by
  haveI : Subsingleton (↥({x} : Set X)) := ⟨by
    intro a b
    apply Subtype.ext
    exact a.property.trans b.property.symm⟩
  exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) k (ModuleCat.of ℤ ℤ)
      (TopCat.of ↥({x} : Set X)) (by omega)

private noncomputable def pairShortComplexForMap (X : Type)
    [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) := by
  let C := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)
  exact ShortComplex.mk (C.map (pairInclusion X A))
    (cokernel.π (C.map (pairInclusion X A)))
    (cokernel.condition _)

private theorem pairShortComplexForMap_shortExact (X : Type)
    [TopologicalSpace X] (A : Set X) :
    (pairShortComplexForMap X A).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := by
    dsimp [pairShortComplexForMap]
    let C := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)
    haveI : Mono (pairInclusion X A) :=
      (TopCat.mono_iff_injective _).mpr Subtype.val_injective
    exact C.map_mono _
  epi_g := by
    dsimp [pairShortComplexForMap]
    infer_instance

private theorem homologyToRelative_isIso_of_subspace_zero_local
    (X : Type) [TopologicalSpace X] (A : Set X) (k : ℕ)
    (hnow : IsZero (H A (k + 1))) (hprev : IsZero (H A k)) :
    IsIso (homologyToRelative X A (k + 1)) := by
  let S := pairShortComplexForMap X A
  have hS : S.ShortExact := pairShortComplexForMap_shortExact X A
  have hmono : Mono (homologyToRelative X A (k + 1)) := by
    have h := (hS.homology_exact₂ (k + 1)).mono_g (hnow.eq_of_src _ _)
    exact h
  have hepi : Epi (homologyToRelative X A (k + 1)) := by
    have h := (hS.homology_exact₃ (k + 1) k (by simp)).epi_f
      (hprev.eq_of_tgt _ _)
    exact h
  exact isIso_of_mono_of_epi _

private theorem cubeWedgeRetained_toRelative_isIso
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    IsIso (homologyToRelative (cubeWedgeRetained n hn)
      (cubeWedgeRetainedFirstAxis n hn) (k + 1)) :=
  homologyToRelative_isIso_of_subspace_zero_local _ _ k
    (cubeWedgeRetainedFirstAxis_homology_isZero n (k + 1) hn (by omega))
    (cubeWedgeRetainedFirstAxis_homology_isZero n k hn hk)

private theorem cubeSphereBasepoint_toRelative_isIso
    (n k : ℕ) (hk : 1 ≤ k) :
    IsIso (homologyToRelative (CubeSphere n)
      ({cubeSphereBasepoint n} : Set (CubeSphere n)) (k + 1)) :=
  homologyToRelative_isIso_of_subspace_zero_local _ _ k
    (singleton_homology_isZero (cubeSphereBasepoint n) (k + 1) (by omega))
    (singleton_homology_isZero (cubeSphereBasepoint n) k hk)

private def pairMapOnSubspaceForMap {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) : TopCat.of ↥A ⟶ TopCat.of ↥B :=
  TopCat.ofHom ⟨fun x => ⟨f x.val, h x.val x.property⟩, by fun_prop⟩

private theorem pairMapOnSubspaceForMap_square {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) :
    pairInclusion X A ≫ TopCat.ofHom f =
      pairMapOnSubspaceForMap A B f h ≫ pairInclusion Y B := by
  ext x
  rfl

private noncomputable def pairRelativeChainMapForMap {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) :
    relativeSingularChains X A ⟶ relativeSingularChains Y B := by
  let C := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)
  apply cokernel.desc (C.map (pairInclusion X A))
    (C.map (TopCat.ofHom f) ≫ cokernel.π (C.map (pairInclusion Y B)))
  rw [← Category.assoc, ← Functor.map_comp,
    pairMapOnSubspaceForMap_square A B f h, Functor.map_comp,
    Category.assoc, cokernel.condition, comp_zero]

private noncomputable def pairRelativeHomologyMapForMap {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y))
    (h : ∀ x ∈ A, f x ∈ B) (k : ℕ) :
    relativeHomology X A k ⟶ relativeHomology Y B k :=
  HomologicalComplex.homologyMap (pairRelativeChainMapForMap A B f h) k


private theorem loopSphereMap_homotopic {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X) (f g : GenLoop (Fin n) X x)
    (h : GenLoop.Homotopic f g) :
    Nonempty (TopCat.Homotopy (TopCat.ofHom (loopSphereMap n x f))
      (TopCat.ofHom (loopSphereMap n x g))) := by
  rcases h with ⟨K⟩
  let q : (Fin n → I) → CubeSphere n := Quotient.mk (cubeBoundarySetoid n)
  have hq : IsQuotientMap q := ⟨⟨rfl⟩, Quotient.mk_surjective⟩
  let L : I × CubeSphere n → X := fun p =>
    Quotient.lift (fun a => K (p.1, a)) (by
      intro a b hab
      rcases hab with hab | ⟨ha, hb⟩
      · exact congrArg (fun a => K (p.1, a)) hab
      · exact (K.eq_fst p.1 ha).trans
          ((GenLoop.boundary f a ha).trans (GenLoop.boundary f b hb).symm) |>.trans
          (K.eq_fst p.1 hb).symm) p.2
  have hL : Continuous L := by
    apply hq.continuous_lift_prod_right
    exact K.continuous
  refine ⟨{
    toContinuousMap := ⟨L, hL⟩
    map_zero_left := by
      intro z
      induction z using Quotient.inductionOn with
      | _ a => exact K.apply_zero a
    map_one_left := by
      intro z
      induction z using Quotient.inductionOn with
      | _ a => exact K.apply_one a }⟩


private theorem homology_constant_map_zero {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (n : ℕ) (hn : 1 ≤ n) (b : B) (u : H A n) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom (ContinuousMap.const A b))) u = 0 := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)
  let q : TopCat.of A ⟶ TopCat.of PUnit :=
    TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let p : TopCat.of PUnit ⟶ TopCat.of B :=
    TopCat.ofHom ⟨fun _ => b, continuous_const⟩
  have hf : TopCat.ofHom (ContinuousMap.const A b) = q ≫ p := by
    ext a
    rfl
  have hzero : IsZero (H PUnit n) := by
    exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) (by omega)
  haveI : Subsingleton (H PUnit n) := homology_subsingleton_of_isZero n hzero
  have hz : (F.map q) u = 0 := Subsingleton.elim _ _
  change (F.map (TopCat.ofHom (ContinuousMap.const A b))) u = 0
  rw [hf, F.map_comp]
  change (F.map p) ((F.map q) u) = 0
  rw [hz]
  simp

private noncomputable def cubeWedgeClass (n : ℕ)
    (u v : H (CubeSphere n) n) : H (cubeSphereWedge n) n :=
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)
  (F.map (TopCat.ofHom (cubeWedgeInl n))) u +
    (F.map (TopCat.ofHom (cubeWedgeInr n))) v

private theorem cubeWedgeClass_fst (n : ℕ) (hn : 1 ≤ n)
    (u v : H (CubeSphere n) n) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (cubeWedgeFst n)))
      (cubeWedgeClass n u v) = u := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)
  have hleft : (F.map (TopCat.ofHom (cubeWedgeFst n)))
      ((F.map (TopCat.ofHom (cubeWedgeInl n))) u) = u := by
    have hcomp : TopCat.ofHom (cubeWedgeInl n) ≫ TopCat.ofHom (cubeWedgeFst n) =
        𝟙 (TopCat.of (CubeSphere n)) := by
      ext z
      rfl
    change (F.map (TopCat.ofHom (cubeWedgeFst n)))
      ((F.map (TopCat.ofHom (cubeWedgeInl n))) u) = u
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, hcomp, F.map_id]
    rfl
  have hright : (F.map (TopCat.ofHom (cubeWedgeFst n)))
      ((F.map (TopCat.ofHom (cubeWedgeInr n))) v) = 0 := by
    have hcomp : TopCat.ofHom (cubeWedgeInr n) ≫ TopCat.ofHom (cubeWedgeFst n) =
        TopCat.ofHom (ContinuousMap.const (CubeSphere n) (cubeSphereBasepoint n)) := by
      ext z
      rfl
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, hcomp]
    exact homology_constant_map_zero n hn (cubeSphereBasepoint n) v
  change (F.map (TopCat.ofHom (cubeWedgeFst n)))
    ((F.map (TopCat.ofHom (cubeWedgeInl n))) u +
      (F.map (TopCat.ofHom (cubeWedgeInr n))) v) = u
  rw [map_add, hleft, hright, add_zero]

private theorem cubeWedgeClass_snd (n : ℕ) (hn : 1 ≤ n)
    (u v : H (CubeSphere n) n) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (cubeWedgeSnd n)))
      (cubeWedgeClass n u v) = v := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)
  have hleft : (F.map (TopCat.ofHom (cubeWedgeSnd n)))
      ((F.map (TopCat.ofHom (cubeWedgeInl n))) u) = 0 := by
    have hcomp : TopCat.ofHom (cubeWedgeInl n) ≫ TopCat.ofHom (cubeWedgeSnd n) =
        TopCat.ofHom (ContinuousMap.const (CubeSphere n) (cubeSphereBasepoint n)) := by
      ext z
      rfl
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, hcomp]
    exact homology_constant_map_zero n hn (cubeSphereBasepoint n) u
  have hright : (F.map (TopCat.ofHom (cubeWedgeSnd n)))
      ((F.map (TopCat.ofHom (cubeWedgeInr n))) v) = v := by
    have hcomp : TopCat.ofHom (cubeWedgeInr n) ≫ TopCat.ofHom (cubeWedgeSnd n) =
        𝟙 (TopCat.of (CubeSphere n)) := by
      ext z
      rfl
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, hcomp, F.map_id]
    rfl
  change (F.map (TopCat.ofHom (cubeWedgeSnd n)))
    ((F.map (TopCat.ofHom (cubeWedgeInl n))) u +
      (F.map (TopCat.ofHom (cubeWedgeInr n))) v) = v
  rw [map_add, hleft, hright, zero_add]


theorem cubeWedgeRetained_toRelative_one_isIso
    (n : ℕ) (hn : 1 ≤ n) :
    IsIso (homologyToRelative (cubeWedgeRetained n hn)
      (cubeWedgeRetainedFirstAxis n hn) 1) := by
  let r : TopCat.of (cubeWedgeRetained n hn) ⟶
      TopCat.of ↥(cubeWedgeRetainedFirstAxis n hn) :=
    TopCat.ofHom ⟨fun z =>
      ⟨⟨cubeWedgeInl n z.val.val.1, z.property⟩, rfl⟩, by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact (cubeWedgeInl n).continuous.comp
          (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))⟩
  have hr : pairInclusion (cubeWedgeRetained n hn)
      (cubeWedgeRetainedFirstAxis n hn) ≫ r = 𝟙 _ := by
    apply TopCat.Hom.ext
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact z.property.symm
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj
    (ModuleCat.of ℤ ℤ)
  have hF : homologyInclusion (cubeWedgeRetained n hn)
      (cubeWedgeRetainedFirstAxis n hn) 0 ≫ F.map r = 𝟙 _ := by
    change F.map (pairInclusion _ _) ≫ F.map r = 𝟙 _
    rw [← F.map_comp, hr, F.map_id]
  have : Mono (homologyInclusion (cubeWedgeRetained n hn)
      (cubeWedgeRetainedFirstAxis n hn) 0 ≫ F.map r) := by
    rw [hF]
    infer_instance
  have : Mono (homologyInclusion (cubeWedgeRetained n hn)
      (cubeWedgeRetainedFirstAxis n hn) 0) := mono_of_mono _ (F.map r)
  have hepi : Epi (homologyToRelative (cubeWedgeRetained n hn)
      (cubeWedgeRetainedFirstAxis n hn) 1) := by
    obtain ⟨hcomp, _⟩ := pairHomology_exact_at_subspace
      (cubeWedgeRetained n hn) (cubeWedgeRetainedFirstAxis n hn) 0
    have hδ : relativeConnecting (cubeWedgeRetained n hn)
        (cubeWedgeRetainedFirstAxis n hn) 0 = 0 := by
      apply (cancel_mono (homologyInclusion (cubeWedgeRetained n hn)
        (cubeWedgeRetainedFirstAxis n hn) 0)).mp
      simpa using hcomp
    obtain ⟨_, hexact⟩ := pairHomology_exact_at_relative
      (cubeWedgeRetained n hn) (cubeWedgeRetainedFirstAxis n hn) 0
    exact hexact.epi_f hδ
  have hmono : Mono (homologyToRelative (cubeWedgeRetained n hn)
      (cubeWedgeRetainedFirstAxis n hn) 1) := by
    obtain ⟨_, hexact⟩ := pairHomology_exact_at_absolute
      (cubeWedgeRetained n hn) (cubeWedgeRetainedFirstAxis n hn) 1
    exact hexact.mono_g
      ((cubeWedgeRetainedFirstAxis_homology_isZero n 1 hn (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

set_option maxHeartbeats 1600000

/-- Review pending: the concrete retained projection on relative degree-one homology. -/
theorem cubeWedgeRetained_relativeProjection_one_isIso
    (n : ℕ) (hn : 1 ≤ n) :
    IsIso (geometricRelativeRetainedProjection (cubeSphereBasepoint n)
      (geometricChartDistance (cubeSphereChart n hn) (cubeSphereBasepoint n))) := by
  let s := cubeSphereBasepoint n
  let d := geometricChartDistance (cubeSphereChart n hn) s
  let qR := homologyToRelative (cubeWedgeRetained n hn)
    (cubeWedgeRetainedFirstAxis n hn) 1
  let qS := homologyToRelative (CubeSphere n) ({s} : Set (CubeSphere n)) 1
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)
  let p := F.map (TopCat.ofHom (cubeWedgeRetainedSnd n hn))
  let r := geometricRelativeRetainedProjection s d
  haveI : IsIso qR := cubeWedgeRetained_toRelative_one_isIso n hn
  haveI : IsIso qS := homologyToRelative_one_isIso_singleton _ s
  haveI : IsIso p := cubeWedgeRetainedSnd_homology_isIso n 1 hn
  have h : qR ≫ r = p ≫ qS := by
    exact pairRelativeHomologyMap_commutes _ _ _ _ 1
  haveI : IsIso (qR ≫ r) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left qR r

/-- Review pending: positive-degree projection injectivity with the actual
excision homology map as the only remaining producer. -/
theorem cubeWedge_projection_injective_of_excision
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hexc : IsIso (HomologicalComplex.homologyMap
      (excisionRelativeChainMap (cubeWedgeFirstAxis n)
        (cubeWedgeExciseFirst n hn)) k)) :
    Function.Injective (fun w : H (cubeSphereWedge n) k =>
      let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ ℤ)
      ((F.map (TopCat.ofHom (cubeWedgeFst n))) w,
        (F.map (TopCat.ofHom (cubeWedgeSnd n))) w)) := by
  let S := CubeSphere n
  let W := cubeSphereWedge n
  let R := cubeWedgeRetained n hn
  let A := cubeWedgeFirstAxis n
  let B := cubeWedgeRetainedFirstAxis n hn
  let D : Set S := {cubeSphereBasepoint n}
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
    (ModuleCat.of ℤ ℤ)
  let qR := homologyToRelative R B k
  let qS := homologyToRelative S D k
  let qW := homologyToRelative W A k
  let pR := cubeWedgeRetainedSnd n hn
  let pW := cubeWedgeSnd n
  have hpR : ∀ z ∈ B, pR z ∈ D := fun _ hz => hz
  have hpW : ∀ z ∈ A, pW z ∈ D := fun _ hz => hz
  let rR := pairRelativeHomologyMap B D pR hpR k
  let rW := pairRelativeHomologyMap A D pW hpW k
  let e := HomologicalComplex.homologyMap
    (excisionRelativeChainMap A (cubeWedgeExciseFirst n hn)) k
  haveI : IsIso e := by
    rcases k with _ | k
    · omega
    · exact canonicalExcisionHomologyMap_isIso W A (cubeWedgeExciseFirst n hn)
        (cubeWedgeExciseFirst_closure n hn) k
  haveI : IsIso qR := by
    rcases k with _ | k
    · omega
    rcases k with _ | k
    · exact cubeWedgeRetained_toRelative_one_isIso n hn
    · exact cubeWedgeRetained_toRelative_isIso n (k + 1) hn (by omega)
  haveI : IsIso qS := by
    rcases k with _ | k
    · omega
    rcases k with _ | k
    · exact homologyToRelative_one_isIso_singleton S (cubeSphereBasepoint n)
    · exact cubeSphereBasepoint_toRelative_isIso n (k + 1) (by omega)
  haveI : IsIso (F.map (TopCat.ofHom pR)) :=
    cubeWedgeRetainedSnd_homology_isIso n k hn
  have hR : qR ≫ rR = F.map (TopCat.ofHom pR) ≫ qS :=
    pairRelativeHomologyMap_commutes B D pR hpR k
  haveI : IsIso (qR ≫ rR) := by rw [hR]; infer_instance
  haveI hrr : IsIso rR := IsIso.of_isIso_comp_left qR rR
  have her : e ≫ rW = rR := by
    let inc : C(R, W) := ⟨Subtype.val, continuous_subtype_val⟩
    have hi : ∀ z ∈ B, inc z ∈ A := fun _ hz => hz
    change pairRelativeHomologyMap B A inc hi k ≫
      pairRelativeHomologyMap A D pW hpW k = rR
    rw [← pairRelativeHomologyMap_comp]
    rfl
  haveI : IsIso (e ≫ rW) := her.symm ▸ hrr
  haveI : IsIso rW := IsIso.of_isIso_comp_left e rW
  have hrW := (ModuleCat.mono_iff_injective rW).mp inferInstance
  have hW : qW ≫ rW = F.map (TopCat.ofHom pW) ≫ qS :=
    pairRelativeHomologyMap_commutes A D pW hpW k
  let j := homologyInclusion W A k
  let p₁ := F.map (TopCat.ofHom (cubeWedgeFst n))
  have hjp : j ≫ p₁ = F.map
      (TopCat.isoOfHomeo (geometricFirstAxisHomeo (cubeSphereBasepoint n))).hom := by
    change F.map (pairInclusion W A) ≫ F.map (TopCat.ofHom (cubeWedgeFst n)) = _
    rw [← F.map_comp]
    rfl
  haveI : IsIso (j ≫ p₁) := by rw [hjp]; infer_instance
  have hjinj := (ModuleCat.mono_iff_injective (j ≫ p₁)).mp inferInstance
  intro w w' hpair
  have h₁ : p₁ w = p₁ w' := congrArg Prod.fst hpair
  have h₂ : (F.map (TopCat.ofHom pW)) w =
      (F.map (TopCat.ofHom pW)) w' := congrArg Prod.snd hpair
  have hq : qW (w - w') = 0 := by
    apply hrW
    have hh := congrArg (fun t => t (w - w')) hW
    change rW (qW (w - w')) = qS ((F.map (TopCat.ofHom pW)) (w - w')) at hh
    simpa only [map_sub, h₂, sub_self, map_zero] using hh
  obtain ⟨_, hexact⟩ := pairHomology_exact_at_absolute W A k
  obtain ⟨a, ha⟩ := (ShortComplex.exact_iff_of_hasForget _).mp hexact (w - w') hq
  have hja : j a = w - w' := ha
  have ha0 : a = 0 := by
    apply hjinj
    change p₁ (j a) = p₁ (j 0)
    rw [hja, map_sub, h₁, sub_self, map_zero, map_zero]
  exact sub_eq_zero.mp (by simpa only [ha0, map_zero] using hja.symm)

/-- Review pending: joint injectivity from the actual cap-excision producer. -/
theorem cubeWedge_projection_one_injective_of_excision
    (n : ℕ) (hn : 1 ≤ n)
    (hexc : IsIso (geometricRelativeExcisionMap (cubeSphereBasepoint n)
      (geometricChartDistance (cubeSphereChart n hn) (cubeSphereBasepoint n)))) :
    Function.Injective (fun w : H (cubeSphereWedge n) 1 =>
      let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)
      ((F.map (TopCat.ofHom (cubeWedgeFst n))) w,
        (F.map (TopCat.ofHom (cubeWedgeSnd n))) w)) := by
  exact cubeWedge_projection_injective_of_excision n 1 hn (by omega) hexc

/-- Review pending: structural additivity for an arbitrary class, leaving no
sphere-generator assertion hidden in the choice of that class. -/
theorem loopSphereMap_transAt_homology_of_excision
    {X : Type} [TopologicalSpace X] (n : ℕ) (hn : 2 ≤ n) (x : X)
    (f g : GenLoop (Fin n) X x) (i : Fin n) (u : H (CubeSphere n) n)
    (hexc : IsIso (HomologicalComplex.homologyMap
      (excisionRelativeChainMap (cubeWedgeFirstAxis n)
        (cubeWedgeExciseFirst n (by omega))) n)) :
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)
    (F.map (TopCat.ofHom (loopSphereMap n x (GenLoop.transAt i f g)))) u =
      (F.map (TopCat.ofHom (loopSphereMap n x f))) u +
        (F.map (TopCat.ofHom (loopSphereMap n x g))) u := by
  classical
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)
  let s := cubeSphereBasepoint n
  let e := cubeSphereIdentityLoop n (by omega)
  let c : GenLoop (Fin n) (CubeSphere n) s := GenLoop.const
  have hunit (a : GenLoop (Fin n) (CubeSphere n) s)
      (ha : (⟦a⟧ : HomotopyGroup.Pi n (CubeSphere n) s) = ⟦e⟧) :
      F.map (TopCat.ofHom (loopSphereMap n s a)) = 𝟙 _ := by
    obtain ⟨K⟩ := loopSphereMap_homotopic n s a e (Quotient.exact ha)
    have heq := K.congr_homologyMap_singularChainComplexFunctor
      (ModuleCat.of ℤ ℤ) n
    change F.map (TopCat.ofHom (loopSphereMap n s a)) =
      F.map (TopCat.ofHom (loopSphereMap n s e)) at heq
    have hid : TopCat.ofHom (loopSphereMap n s e) =
        𝟙 (TopCat.of (CubeSphere n)) := by
      ext z
      induction z using Quotient.inductionOn with
      | _ a => rfl
    rw [heq, hid, F.map_id]
  have hfst : F.map (TopCat.ofHom (loopSphereMap n s (GenLoop.transAt i e c))) =
      𝟙 _ := by
    apply hunit
    rw [← HomotopyGroup.mul_spec (i := i) (p := c) (q := e)]
    exact one_mul (M := HomotopyGroup (Fin n) (CubeSphere n) s) ⟦e⟧
  have hsnd : F.map (TopCat.ofHom (loopSphereMap n s (GenLoop.transAt i c e))) =
      𝟙 _ := by
    apply hunit
    rw [← HomotopyGroup.mul_spec (i := i) (p := e) (q := c)]
    exact mul_one (M := HomotopyGroup (Fin n) (CubeSphere n) s) ⟦e⟧
  have hpinch : (F.map (TopCat.ofHom (cubePinch n (by omega) i))) u =
      cubeWedgeClass n u u := by
    apply cubeWedge_projection_injective_of_excision n n (by omega) (by omega) hexc
    apply Prod.ext
    · change (F.map (TopCat.ofHom (cubeWedgeFst n)))
        ((F.map (TopCat.ofHom (cubePinch n (by omega) i))) u) =
          (F.map (TopCat.ofHom (cubeWedgeFst n))) (cubeWedgeClass n u u)
      rw [cubeWedgeClass_fst n (by omega), ← ConcreteCategory.comp_apply, ← F.map_comp]
      have hc : TopCat.ofHom (cubePinch n (by omega) i) ≫
          TopCat.ofHom (cubeWedgeFst n) =
          TopCat.ofHom (loopSphereMap n s (GenLoop.transAt i e c)) := by
        ext z
        rfl
      rw [hc, hfst]
      rfl
    · change (F.map (TopCat.ofHom (cubeWedgeSnd n)))
        ((F.map (TopCat.ofHom (cubePinch n (by omega) i))) u) =
          (F.map (TopCat.ofHom (cubeWedgeSnd n))) (cubeWedgeClass n u u)
      rw [cubeWedgeClass_snd n (by omega), ← ConcreteCategory.comp_apply, ← F.map_comp]
      have hc : TopCat.ofHom (cubePinch n (by omega) i) ≫
          TopCat.ofHom (cubeWedgeSnd n) =
          TopCat.ofHom (loopSphereMap n s (GenLoop.transAt i c e)) := by
        ext z
        rfl
      rw [hc, hsnd]
      rfl
  let fold := cubeWedgeFold n (by omega) x f g
  have hfactor : TopCat.ofHom (loopSphereMap n x (GenLoop.transAt i f g)) =
      TopCat.ofHom (cubePinch n (by omega) i) ≫ TopCat.ofHom fold :=
    congrArg TopCat.ofHom (loopSphereMap_transAt_factor n (by omega) x f g i)
  have hleft : (F.map (TopCat.ofHom fold))
      ((F.map (TopCat.ofHom (cubeWedgeInl n))) u) =
        (F.map (TopCat.ofHom (loopSphereMap n x f))) u := by
    rw [← ConcreteCategory.comp_apply, ← F.map_comp]
    have hc : TopCat.ofHom (cubeWedgeInl n) ≫ TopCat.ofHom fold =
        TopCat.ofHom (loopSphereMap n x f) :=
      congrArg TopCat.ofHom (cubeWedgeFold_inl n (by omega) x f g)
    rw [hc]
  have hright : (F.map (TopCat.ofHom fold))
      ((F.map (TopCat.ofHom (cubeWedgeInr n))) u) =
        (F.map (TopCat.ofHom (loopSphereMap n x g))) u := by
    rw [← ConcreteCategory.comp_apply, ← F.map_comp]
    have hc : TopCat.ofHom (cubeWedgeInr n) ≫ TopCat.ofHom fold =
        TopCat.ofHom (loopSphereMap n x g) :=
      congrArg TopCat.ofHom (cubeWedgeFold_inr n (by omega) x f g)
    rw [hc]
  change (F.map (TopCat.ofHom (loopSphereMap n x (GenLoop.transAt i f g)))) u = _
  rw [hfactor, F.map_comp]
  change (F.map (TopCat.ofHom fold))
    ((F.map (TopCat.ofHom (cubePinch n (by omega) i))) u) = _
  rw [hpinch]
  change (F.map (TopCat.ofHom fold))
    ((F.map (TopCat.ofHom (cubeWedgeInl n))) u +
      (F.map (TopCat.ofHom (cubeWedgeInr n))) u) = _
  rw [map_add, hleft, hright]

/-- Intended public wrapper in CubeSphereGeometry, whose proof may access its
private wedge-closure producer. No excision hypothesis remains in the API. -/
theorem loopSphereMap_transAt_homology
    {X : Type} [TopologicalSpace X] (n : ℕ) (hn : 2 ≤ n) (x : X)
    (f g : GenLoop (Fin n) X x) (i : Fin n) (u : H (CubeSphere n) n) :
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)
    (F.map (TopCat.ofHom (loopSphereMap n x (GenLoop.transAt i f g)))) u =
      (F.map (TopCat.ofHom (loopSphereMap n x f))) u +
        (F.map (TopCat.ofHom (loopSphereMap n x g))) u := by
  apply loopSphereMap_transAt_homology_of_excision n hn x f g i u
  cases n with
  | zero => omega
  | succ m =>
    exact canonicalExcisionHomologyMap_isIso _ _ _
      (cubeWedgeExciseFirst_closure (m + 1) (by omega)) m

end CurveComplexGenusTwo.CWHurewicz
