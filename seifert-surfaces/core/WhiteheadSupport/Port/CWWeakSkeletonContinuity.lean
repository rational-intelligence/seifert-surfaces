import WhiteheadSupport.Port.CWInfiniteCoherence
import WhiteheadSupport.Port.WeakCoverProduct

namespace SeifertSurfaces.WhiteheadSupport.Port.CW

universe u v

open _root_.Topology

variable {X : Type u} {Y : Type*} [tX : TopologicalSpace X] [TopologicalSpace Y]
  [Topology.CWComplex (Set.univ : Set X)]

/-- A closed-cell criterion for the weak topology of the skeletal cover. -/
theorem weakSkeletonCover_of_closedCells
    (hcell : ∀ n (i : Topology.CWComplex.cell (Set.univ : Set X) n),
      IsClosed (Topology.CWComplex.closedCell (C := (Set.univ : Set X)) n i)) :
    SeifertSurfaces.WhiteheadSupport.Port.WeakTopology.HasWeakTopologyFromCover
      (skeletonBelow X) := by
  constructor
  · exact skeletonBelow_union
  · change _ = ⨆ n : ℕ, TopologicalSpace.coinduced
      (fun z : ↥(skeletonBelow X n) => (z : X)) inferInstance
    apply le_antisymm
    · apply (continuous_id_iff_le).mp
      apply (@continuous_iff_isClosed X X tX
        (⨆ n : ℕ, TopologicalSpace.coinduced
          (fun z : ↥(skeletonBelow X n) => (z : X)) inferInstance) id).mpr
      intro A hA
      have hskel (n : ℕ) :
          IsClosed ((fun z : ↥(skeletonBelow X n) => (z : X)) ⁻¹' A) := by
        exact isClosed_coinduced.mp ((isClosed_iSup_iff.mp hA) n)
      apply Topology.CWComplex.closed' A (Set.subset_univ A)
      intro n i
      obtain ⟨B, hB, hEq⟩ := isClosed_induced_iff.mp (hskel (n + 1))
      have hsubset : Topology.CWComplex.closedCell
          (C := (Set.univ : Set X)) n i ⊆ skeletonBelow X (n + 1) := by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
          ⟨Nat.lt_succ_self n, Set.mem_iUnion.mpr ⟨i, hx⟩⟩⟩
      have hinter : A ∩ Topology.CWComplex.closedCell
          (C := (Set.univ : Set X)) n i =
          B ∩ Topology.CWComplex.closedCell (C := (Set.univ : Set X)) n i := by
        ext x
        constructor
        · intro hx
          refine ⟨?_, hx.2⟩
          have hz : (⟨x, hsubset hx.2⟩ : ↥(skeletonBelow X (n + 1))) ∈
              (fun z : ↥(skeletonBelow X (n + 1)) => (z : X)) ⁻¹' A := hx.1
          have hzB : (⟨x, hsubset hx.2⟩ : ↥(skeletonBelow X (n + 1))) ∈
              (fun z : ↥(skeletonBelow X (n + 1)) => (z : X)) ⁻¹' B := by
            rw [hEq]
            exact hz
          exact hzB
        · intro hx
          refine ⟨?_, hx.2⟩
          have hz : (⟨x, hsubset hx.2⟩ : ↥(skeletonBelow X (n + 1))) ∈
              (fun z : ↥(skeletonBelow X (n + 1)) => (z : X)) ⁻¹' B := hx.1
          have hzA : (⟨x, hsubset hx.2⟩ : ↥(skeletonBelow X (n + 1))) ∈
              (fun z : ↥(skeletonBelow X (n + 1)) => (z : X)) ⁻¹' A := by
            rw [← hEq]
            exact hz
          exact hzA
      change IsClosed (A ∩ Topology.CWComplex.closedCell
        (C := (Set.univ : Set X)) n i)
      rw [hinter]
      exact hB.inter (hcell n i)
    · apply iSup_le
      intro n
      exact continuous_iff_coinduced_le.mp continuous_subtype_val

theorem coherentSkeletonFunction_continuous_of_weakCover
    (hweak : SeifertSurfaces.WhiteheadSupport.Port.WeakTopology.HasWeakTopologyFromCover
      (skeletonBelow X))
    (f : ∀ n : ℕ, C(↥(skeletonBelow X n), Y))
    (hcompat : ∀ n m (hnm : n ≤ m) (z : ↥(skeletonBelow X n)),
      f n z = f m (skeletonInclusion hnm z)) :
    Continuous (coherentSkeletonFunction f) := by
  rw (occs := .pos [1]) [hweak.2]
  rw [continuous_iSup_dom]
  intro n
  rw [continuous_coinduced_dom]
  convert (f n).continuous using 1
  funext z
  exact coherentSkeletonFunction_apply f hcompat n z

theorem cwInfiniteColimit_of_weakSkeletonCover
    (hweak : SeifertSurfaces.WhiteheadSupport.Port.WeakTopology.HasWeakTopologyFromCover
      (skeletonBelow X))
    (f : ∀ n : ℕ, C(↥(skeletonBelow X n), Y))
    (hcompat : ∀ n m (hnm : n ≤ m) (z : ↥(skeletonBelow X n)),
      f n z = f m (skeletonInclusion hnm z)) :
    ∃! h : C(X, Y), ∀ n (z : ↥(skeletonBelow X n)), h z.val = f n z := by
  refine ⟨⟨coherentSkeletonFunction f,
    coherentSkeletonFunction_continuous_of_weakCover hweak f hcompat⟩, ?_, ?_⟩
  · intro n z
    exact coherentSkeletonFunction_apply f hcompat n z
  · intro h hh
    apply ContinuousMap.ext
    have hfun : (h : X → Y) = coherentSkeletonFunction f :=
      coherentSkeletonFunction_unique f hcompat h hh
    exact congrFun hfun

/-- The integrated product weak-cover result reduces global homotopy continuity
to the weak-cover property of the skeletal filtration. -/
theorem coherentSkeletonHomotopyFunction_continuous_of_weakCover
    (hweak : SeifertSurfaces.WhiteheadSupport.Port.WeakTopology.HasWeakTopologyFromCover
      (skeletonBelow X))
    (f g : C(X, Y))
    (Hn : ∀ n : ℕ,
      ContinuousMap.Homotopy
        (f.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y))
        (g.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y)))
    (hcompat : ∀ n m (hnm : n ≤ m) (t : unitInterval)
      (z : ↥(skeletonBelow X n)),
      Hn n (t, z) = Hn m (t, skeletonInclusion hnm z)) :
    Continuous (coherentSkeletonHomotopyFunction f g Hn) := by
  have hswap : Continuous (fun p : X × unitInterval =>
      coherentSkeletonHomotopyFunction f g Hn (p.2, p.1)) := by
    apply SeifertSurfaces.WhiteheadSupport.Port.WeakTopology.continuous_of_weakTopology_product
      (pieces := skeletonBelow X) hweak
    intro n
    have hpiece : Continuous (fun p : (skeletonBelow X n) × unitInterval =>
        Hn n (p.2, p.1)) := (Hn n).continuous.comp continuous_swap
    convert hpiece using 1
    funext p
    exact coherentSkeletonHomotopyFunction_apply f g Hn hcompat n p.2 p.1
  convert hswap.comp (continuous_swap : Continuous (Prod.swap :
    unitInterval × X → X × unitInterval)) using 1
  funext p
  rfl

theorem cwHomotopyColimit_of_weakSkeletonCover
    (hweak : SeifertSurfaces.WhiteheadSupport.Port.WeakTopology.HasWeakTopologyFromCover
      (skeletonBelow X))
    (f g : C(X, Y))
    (Hn : ∀ n : ℕ,
      ContinuousMap.Homotopy
        (f.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y))
        (g.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y)))
    (hcompat : ∀ n m (hnm : n ≤ m) (t : unitInterval)
      (z : ↥(skeletonBelow X n)),
      Hn n (t, z) = Hn m (t, skeletonInclusion hnm z)) :
    ContinuousMap.Homotopic f g := by
  exact coherentSkeletonHomotopy_of_continuous f g Hn hcompat
    (coherentSkeletonHomotopyFunction_continuous_of_weakCover hweak f g Hn hcompat)

theorem weakSkeletonCover_of_t2 [T2Space X] :
    SeifertSurfaces.WhiteheadSupport.Port.WeakTopology.HasWeakTopologyFromCover
      (skeletonBelow X) := by
  apply weakSkeletonCover_of_closedCells
  intro n i
  exact Topology.CWComplex.isClosed_closedCell

theorem cwHomotopyColimit_of_t2 [T2Space X]
    (f g : C(X, Y))
    (Hn : ∀ n : ℕ,
      ContinuousMap.Homotopy
        (f.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y))
        (g.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y)))
    (hcompat : ∀ n m (hnm : n ≤ m) (t : unitInterval)
      (z : ↥(skeletonBelow X n)),
      Hn n (t, z) = Hn m (t, skeletonInclusion hnm z)) :
    ContinuousMap.Homotopic f g := by
  exact cwHomotopyColimit_of_weakSkeletonCover weakSkeletonCover_of_t2 f g Hn hcompat

theorem cwInfiniteColimit_of_t2 [T2Space X]
    (f : ∀ n : ℕ, C(↥(skeletonBelow X n), Y))
    (hcompat : ∀ n m (hnm : n ≤ m) (z : ↥(skeletonBelow X n)),
      f n z = f m (skeletonInclusion hnm z)) :
    ∃! h : C(X, Y), ∀ n (z : ↥(skeletonBelow X n)), h z.val = f n z := by
  exact cwInfiniteColimit_of_weakSkeletonCover weakSkeletonCover_of_t2 f hcompat

end SeifertSurfaces.WhiteheadSupport.Port.CW
