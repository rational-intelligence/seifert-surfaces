import CurveComplexGenusTwo.CWHurewicz.CWBasic
import CurveComplexGenusTwo.CWHurewicz.CellDiskExtension
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Analysis.SpecialFunctions.Sigmoid

namespace CurveComplexGenusTwo.CWHurewicz

open Metric Set Topology Bornology
open scoped unitInterval OnePoint

/-- Collapsing the boundary of the standard cube gives a quotient sphere. -/
def whiteheadCubeBoundarySetoid (n : ℕ) : Setoid (Fin n → unitInterval) where
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

abbrev WhiteheadCubeSphere (n : ℕ) :=
  Quotient (whiteheadCubeBoundarySetoid n)

instance whiteheadCubeSphereTopology (n : ℕ) :
    TopologicalSpace (WhiteheadCubeSphere n) :=
  TopologicalSpace.coinduced (Quotient.mk (whiteheadCubeBoundarySetoid n)) inferInstance

private def whiteheadCubeInterior (n : ℕ) : Set (Fin n → unitInterval) :=
  (Cube.boundary (Fin n))ᶜ

private theorem whiteheadCubeBoundary_closed (n : ℕ) :
    IsClosed (Cube.boundary (Fin n) : Set (Fin n → unitInterval)) := by
  have h : (Cube.boundary (Fin n) : Set (Fin n → unitInterval)) =
      ⋃ i : Fin n, ({a | a i = 0} ∪ {a | a i = 1}) := by
    ext a
    simp only [Cube.boundary, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union]
  rw [h]
  apply isClosed_iUnion_of_finite
  intro i
  exact ((isClosed_singleton.preimage (continuous_apply i)).union
    (isClosed_singleton.preimage (continuous_apply i)))

private theorem whiteheadCubeInterior_open (n : ℕ) :
    IsOpen (whiteheadCubeInterior n) :=
  (whiteheadCubeBoundary_closed n).isOpen_compl

private noncomputable def whiteheadCubeCollapse (n : ℕ)
    (a : Fin n → unitInterval) : OnePoint (whiteheadCubeInterior n) := by
  classical
  exact if h : a ∈ Cube.boundary (Fin n) then ∞
    else OnePoint.some (⟨a, h⟩ : whiteheadCubeInterior n)

private theorem whiteheadCubeCollapse_continuous (n : ℕ) :
    Continuous (whiteheadCubeCollapse n) := by
  rw [continuous_def]
  intro s hs
  let U := whiteheadCubeInterior n
  let A : Set U := ((↑) : U → OnePoint U) ⁻¹' s
  have himage (B : Set U) (a : Fin n → unitInterval)
      (ha : a ∉ Cube.boundary (Fin n)) :
      a ∈ Subtype.val '' B ↔ (⟨a, ha⟩ : U) ∈ B := by
    constructor
    · rintro ⟨u, hu, heq⟩
      have he : u = (⟨a, ha⟩ : U) := Subtype.ext heq
      simpa [he] using hu
    · intro hu
      exact ⟨⟨a, ha⟩, hu, rfl⟩
  have hnoimage (B : Set U) (a : Fin n → unitInterval)
      (ha : a ∈ Cube.boundary (Fin n)) : a ∉ Subtype.val '' B := by
    rintro ⟨u, _, heq⟩
    exact u.property (heq ▸ ha)
  by_cases hInf : (∞ : OnePoint U) ∈ s
  · have hA : IsCompact Aᶜ := ((OnePoint.isOpen_iff_of_mem hInf).mp hs).2
    have heq : whiteheadCubeCollapse n ⁻¹' s = (Subtype.val '' Aᶜ)ᶜ := by
      ext a
      by_cases ha : a ∈ Cube.boundary (Fin n)
      · have hau : a ∉ U := by simpa [U, whiteheadCubeInterior] using ha
        simp [whiteheadCubeCollapse, ha, hInf, hau]
      · change whiteheadCubeCollapse n a ∈ s ↔ a ∉ Subtype.val '' Aᶜ
        simp only [whiteheadCubeCollapse, dite_eq_right ha]
        rw [himage Aᶜ a ha]
        simp [A]
    rw [heq]
    exact (hA.image continuous_subtype_val).isClosed.isOpen_compl
  · have hA : IsOpen A := (OnePoint.isOpen_iff_of_notMem hInf).mp hs
    have heq : whiteheadCubeCollapse n ⁻¹' s = Subtype.val '' A := by
      ext a
      by_cases ha : a ∈ Cube.boundary (Fin n)
      · simp [whiteheadCubeCollapse, ha, hInf, hnoimage A a ha]
      · change whiteheadCubeCollapse n a ∈ s ↔ a ∈ Subtype.val '' A
        simp only [whiteheadCubeCollapse, dite_eq_right ha]
        rw [himage A a ha]
        rfl
    rw [heq]
    exact (whiteheadCubeInterior_open n).isOpenMap_subtype_val A hA

private noncomputable def whiteheadCubeQuotientToOnePoint (n : ℕ) :
    WhiteheadCubeSphere n → OnePoint (whiteheadCubeInterior n) :=
  Quotient.lift (whiteheadCubeCollapse n) (by
    intro a b hab
    rcases hab with hab | ⟨ha, hb⟩
    · exact congrArg (whiteheadCubeCollapse n) hab
    · simp [whiteheadCubeCollapse, ha, hb])

private theorem whiteheadCubeQuotientToOnePoint_continuous (n : ℕ) :
    Continuous (whiteheadCubeQuotientToOnePoint n) := by
  apply continuous_coinduced_dom.mpr
  exact whiteheadCubeCollapse_continuous n

private theorem whiteheadCubeQuotientToOnePoint_surjective (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (whiteheadCubeQuotientToOnePoint n) := by
  intro z
  induction z using OnePoint.rec with
  | infty =>
      let a : Fin n → unitInterval := fun _ => 0
      have ha : a ∈ Cube.boundary (Fin n) := ⟨⟨0, by omega⟩, Or.inl rfl⟩
      exact ⟨Quotient.mk _ a, by simp [whiteheadCubeQuotientToOnePoint,
        whiteheadCubeCollapse, ha]⟩
  | coe u =>
      refine ⟨Quotient.mk _ u.val, ?_⟩
      change whiteheadCubeCollapse n u.val = OnePoint.some u
      rw [whiteheadCubeCollapse, dite_eq_right u.property]

private theorem whiteheadCubeQuotientToOnePoint_injective (n : ℕ) :
    Function.Injective (whiteheadCubeQuotientToOnePoint n) := by
  intro z w h
  induction z using Quotient.inductionOn with
  | _ a =>
    induction w using Quotient.inductionOn with
    | _ b =>
      change whiteheadCubeCollapse n a = whiteheadCubeCollapse n b at h
      by_cases ha : a ∈ Cube.boundary (Fin n)
      · by_cases hb : b ∈ Cube.boundary (Fin n)
        · exact Quotient.sound (Or.inr ⟨ha, hb⟩)
        · simp [whiteheadCubeCollapse, ha, hb] at h
      · by_cases hb : b ∈ Cube.boundary (Fin n)
        · simp [whiteheadCubeCollapse, ha, hb] at h
        · have hsub : (⟨a, ha⟩ : whiteheadCubeInterior n) = ⟨b, hb⟩ :=
            OnePoint.coe_injective (by
              simpa [whiteheadCubeCollapse, ha, hb] using h)
          have hab : a = b := congrArg Subtype.val hsub
          exact Quotient.sound (Or.inl hab)

private noncomputable def whiteheadCubeQuotientOnePointHomeo
    (n : ℕ) (hn : 1 ≤ n) :
    WhiteheadCubeSphere n ≃ₜ OnePoint (whiteheadCubeInterior n) := by
  letI : CompactSpace (WhiteheadCubeSphere n) := Quotient.compactSpace
  letI : LocallyCompactSpace (whiteheadCubeInterior n) :=
    (whiteheadCubeInterior_open n).locallyCompactSpace
  let e := Equiv.ofBijective (whiteheadCubeQuotientToOnePoint n)
    ⟨whiteheadCubeQuotientToOnePoint_injective n,
      whiteheadCubeQuotientToOnePoint_surjective n hn⟩
  exact Continuous.homeoOfEquivCompactToT2 (show Continuous e from
    whiteheadCubeQuotientToOnePoint_continuous n)

private noncomputable def whiteheadCubeInteriorEuclidean (n : ℕ) :
    whiteheadCubeInterior n ≃ₜ
      (Fin n → ↥(Ioo (0 : unitInterval) 1)) where
  toFun a i :=
    ⟨a.val i, by
      have h0 : a.val i ≠ 0 := by
        intro h
        exact a.property ⟨i, Or.inl h⟩
      have h1 : a.val i ≠ 1 := by
        intro h
        exact a.property ⟨i, Or.inr h⟩
      exact ⟨lt_of_le_of_ne bot_le h0.symm, lt_of_le_of_ne le_top h1⟩⟩
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

private noncomputable def whiteheadOpenIntervalHomeo :
    ℝ ≃ₜ ↥(Ioo (0 : I) 1) :=
  Topology.isEmbedding_sigmoid.toHomeomorph.trans
    (Homeomorph.setCongr unitInterval.range_sigmoid)

private noncomputable def whiteheadCubeInteriorRealHomeo (n : ℕ) :
    whiteheadCubeInterior n ≃ₜ (Fin n → ℝ) :=
  (whiteheadCubeInteriorEuclidean n).trans
    (Homeomorph.piCongrRight
      (fun _ : Fin n => whiteheadOpenIntervalHomeo.symm))

private noncomputable def whiteheadCubeSphereEuclideanHomeo
    (n : ℕ) (hn : 1 ≤ n) :
    WhiteheadCubeSphere n ≃ₜ
      ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  let k := onePointEquivSphereOfFinrankEq (ι := Fin (n + 1))
    (V := Fin n → ℝ) (by simp)
  exact (whiteheadCubeQuotientOnePointHomeo n hn).trans
    ((whiteheadCubeInteriorRealHomeo n).onePointCongr.trans k)

private noncomputable def whiteheadCubeQuotientMap (n : ℕ) :
    C((Fin n → unitInterval), WhiteheadCubeSphere n) :=
  ⟨Quotient.mk (whiteheadCubeBoundarySetoid n), continuous_coinduced_rng⟩

private noncomputable def whiteheadCubeBoundaryPoint (n : ℕ) :
    WhiteheadCubeSphere n :=
  Quotient.mk (whiteheadCubeBoundarySetoid n) (fun _ => 0)

private theorem whiteheadCubeQuotientMap_boundary (n : ℕ) (hn : 1 ≤ n)
    (a : Fin n → unitInterval) (ha : a ∈ Cube.boundary (Fin n)) :
    whiteheadCubeQuotientMap n a = whiteheadCubeBoundaryPoint n := by
  apply Quotient.sound
  right
  exact ⟨ha, ⟨⟨0, by omega⟩, Or.inl rfl⟩⟩

private noncomputable def whiteheadSphereMapToGenLoop
    {X : Type} [TopologicalSpace X] (n : ℕ) (hn : 1 ≤ n)
    (f : C(WhiteheadCubeSphere n, X)) :
    GenLoop (Fin n) X (f (whiteheadCubeBoundaryPoint n)) :=
  ⟨f.comp (whiteheadCubeQuotientMap n), by
    intro a ha
    change f (whiteheadCubeQuotientMap n a) = f (whiteheadCubeBoundaryPoint n)
    rw [whiteheadCubeQuotientMap_boundary n hn a ha]⟩

private theorem whiteheadSphereMap_nullhomotopic
    {X : Type} [TopologicalSpace X]
    (hpi : ∀ k : ℕ, 1 ≤ k → ∀ x : X,
      Subsingleton (HomotopyGroup.Pi k X x))
    (n : ℕ) (hn : 1 ≤ n) (f : C(WhiteheadCubeSphere n, X)) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const (WhiteheadCubeSphere n) (f (whiteheadCubeBoundaryPoint n))) := by
  let p := whiteheadSphereMapToGenLoop n hn f
  have hpk : GenLoop.Homotopic p
      (GenLoop.const : GenLoop (Fin n) X (f (whiteheadCubeBoundaryPoint n))) := by
    exact Quotient.exact ((hpi n hn _).allEq
      (⟦p⟧ : HomotopyGroup.Pi n X _)
      (⟦GenLoop.const⟧ : HomotopyGroup.Pi n X _))
  obtain ⟨K⟩ := hpk
  let q := Quotient.mk (whiteheadCubeBoundarySetoid n)
  have hq : IsQuotientMap q := ⟨⟨rfl⟩, Quotient.mk_surjective⟩
  let L : unitInterval × WhiteheadCubeSphere n → X := fun z =>
    Quotient.lift (fun a => K (z.1, a)) (by
      intro a b hab
      rcases hab with hab | ⟨ha, hb⟩
      · exact congrArg (fun c => K (z.1, c)) hab
      · exact (K.eq_fst z.1 ha).trans
          ((GenLoop.boundary p a ha).trans
            (GenLoop.boundary p b hb).symm) |>.trans
          (K.eq_fst z.1 hb).symm) z.2
  have hL : Continuous L := by
    apply hq.continuous_lift_prod_right
    exact K.continuous
  refine ⟨{ toContinuousMap := ⟨L, hL⟩, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro z
    induction z using Quotient.inductionOn with
    | _ a => exact K.apply_zero a
  · intro z
    induction z using Quotient.inductionOn with
    | _ a => exact K.apply_one a

private noncomputable abbrev normBridgeEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
  EuclideanSpace.equiv (Fin n) ℝ

private def supBallInEuclidean (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  (normBridgeEquiv n) ⁻¹' ball (0 : Fin n → ℝ) 1

private theorem supBallInEuclidean_convex (n : ℕ) :
    Convex ℝ (supBallInEuclidean n) := by
  exact (convex_ball (0 : Fin n → ℝ) 1).linear_preimage
    (normBridgeEquiv n).toLinearMap

private theorem supBallInEuclidean_nhds (n : ℕ) :
    supBallInEuclidean n ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) := by
  exact (normBridgeEquiv n).continuous.continuousAt.preimage_mem_nhds
    (by simpa using Metric.ball_mem_nhds (0 : Fin n → ℝ) (by norm_num : (0 : ℝ) < 1))

private theorem supBallInEuclidean_bounded (n : ℕ) :
    IsBounded (supBallInEuclidean n) := by
  let e := normBridgeEquiv n
  have h : IsCompact (closedBall (0 : Fin n → ℝ) 1) := isCompact_closedBall 0 1
  have hb := (h.image e.symm.continuous).isBounded
  apply hb.subset
  rintro z hz
  refine ⟨e z, ball_subset_closedBall hz, ?_⟩
  exact e.symm_apply_apply z

private theorem supBallInEuclidean_frontier (n : ℕ) :
    frontier (supBallInEuclidean n) =
      (normBridgeEquiv n) ⁻¹' sphere (0 : Fin n → ℝ) 1 := by
  change frontier ((normBridgeEquiv n).toHomeomorph ⁻¹'
    ball (0 : Fin n → ℝ) 1) =
    (normBridgeEquiv n).toHomeomorph ⁻¹' sphere 0 1
  rw [← (normBridgeEquiv n).toHomeomorph.preimage_frontier]
  rw [frontier_ball (0 : Fin n → ℝ) (by norm_num : (1 : ℝ) ≠ 0)]

private noncomputable def normGaugeHomeomorph (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  Classical.choose <|
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (supBallInEuclidean_convex n)
      ⟨0, (mem_interior_iff_mem_nhds).2 (supBallInEuclidean_nhds n)⟩
      (supBallInEuclidean_bounded n)

private theorem normGaugeHomeomorph_frontier (n : ℕ) :
    normGaugeHomeomorph n '' frontier (supBallInEuclidean n) =
      sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  exact (Classical.choose_spec <|
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (supBallInEuclidean_convex n)
      ⟨0, (mem_interior_iff_mem_nhds).2 (supBallInEuclidean_nhds n)⟩
      (supBallInEuclidean_bounded n)).2.2

private noncomputable def normChangeAmbientHomeomorph (n : ℕ) :
    (Fin n → ℝ) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (normBridgeEquiv n).symm.toHomeomorph.trans (normGaugeHomeomorph n)

private theorem normChangeAmbientHomeomorph_sphere (n : ℕ) :
    normChangeAmbientHomeomorph n '' sphere (0 : Fin n → ℝ) 1 =
      sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  let e := normBridgeEquiv n
  let h := normGaugeHomeomorph n
  calc
    normChangeAmbientHomeomorph n '' sphere (0 : Fin n → ℝ) 1 =
        h '' (e.symm '' sphere (0 : Fin n → ℝ) 1) := by
      exact (image_image h e.symm _).symm
    _ = h '' (e ⁻¹' sphere (0 : Fin n → ℝ) 1) := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        change e.symm y = x at hxy
        simpa [← hxy] using hy
      · intro hx
        exact ⟨e x, hx, e.symm_apply_apply x⟩
    _ = h '' frontier (supBallInEuclidean n) := by
      rw [supBallInEuclidean_frontier]
    _ = sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      normGaugeHomeomorph_frontier n

/-- The sup-norm cell sphere and the Euclidean sphere have the same topology. -/
noncomputable def cellSphereEuclideanHomeomorph (n : ℕ) :
    CellSphere n ≃ₜ ↥(sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  let g := normChangeAmbientHomeomorph n
  have hi : g '' sphere (0 : Fin n → ℝ) 1 =
      sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    normChangeAmbientHomeomorph_sphere n
  apply Homeomorph.sets g
  ext x
  constructor
  · intro hx
    change g x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1
    rw [← hi]
    exact ⟨x, hx, rfl⟩
  · intro hx
    change g x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 at hx
    obtain ⟨y, hy, hxy⟩ : g x ∈ g '' sphere (0 : Fin n → ℝ) 1 := hi.symm ▸ hx
    exact g.injective hxy ▸ hy

/-- The quotient cube is homeomorphic to the CW cell boundary. -/
noncomputable def whiteheadCubeSphereCellHomeo (n : ℕ) (hn : 1 ≤ n) :
    WhiteheadCubeSphere n ≃ₜ CellSphere (n + 1) := by
  exact (whiteheadCubeSphereEuclideanHomeo n hn).trans
    (cellSphereEuclideanHomeomorph (n + 1)).symm

/-- Trivial positive homotopy groups make every CW cell-sphere map extend
across its closed cell disk. -/
theorem cellSphereMap_extends_of_hpi
    {X : Type} [TopologicalSpace X]
    (hpi : ∀ k : ℕ, 1 ≤ k → ∀ x : X,
      Subsingleton (HomotopyGroup.Pi k X x))
    (n : ℕ) (hn : 1 ≤ n) (f : C(CellSphere (n + 1), X)) :
    ∃ F : C(CellDisk (n + 1), X),
      ∀ z : CellSphere (n + 1),
        F ⟨z.val, sphere_subset_closedBall z.property⟩ = f z := by
  let g := whiteheadCubeSphereCellHomeo n hn
  let u : C(WhiteheadCubeSphere n, X) := f.comp ⟨g, g.continuous⟩
  let y₀ : X := u (whiteheadCubeBoundaryPoint n)
  have hu : ContinuousMap.Homotopic u
      (ContinuousMap.const (WhiteheadCubeSphere n) y₀) :=
    whiteheadSphereMap_nullhomotopic hpi n hn u
  have hf : ContinuousMap.Homotopic f
      (ContinuousMap.const (CellSphere (n + 1)) y₀) := by
    have hh := hu.comp (ContinuousMap.Homotopic.refl
      (⟨g.symm, g.symm.continuous⟩ :
        C(CellSphere (n + 1), WhiteheadCubeSphere n)))
    convert hh using 1 <;> ext z <;> simp [u]
  exact cellSphereMap_extends_cellDisk (n + 1) f y₀ (Classical.choice hf)

end CurveComplexGenusTwo.CWHurewicz
