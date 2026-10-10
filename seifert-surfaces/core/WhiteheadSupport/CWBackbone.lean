import WhiteheadSupport.Port.CWWhiteheadFromCellStep

/-!
Generator interfaces for the actual point-Whitehead construction.
The skeletal set is the union of genuine closed CW cells. The extension theorem
must produce the next homotopy and its restriction equation from vanishing
homotopy groups. The colimit theorem must prove global continuity; neither is
supplied as an assumed Whitehead interface.
-/

namespace SeifertSurfaces.WhiteheadSupport.CW

universe u v

open Topology

/-- The closed cells of dimension strictly smaller than `n`. -/
def skeletonBelow (X : Type u) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) : Set X :=
  ⋃ (m : ℕ) (_ : m < n) (i : Topology.CWComplex.cell (Set.univ : Set X) m),
    Topology.CWComplex.closedCell (C := (Set.univ : Set X)) m i

theorem skeletonBelow_mono {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] {n m : ℕ} (h : n ≤ m) :
    skeletonBelow X n ⊆ skeletonBelow X m := by
  exact Port.CW.skeletonBelow_mono h

theorem skeletonBelow_union {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] :
    (⋃ n : ℕ, skeletonBelow X n) = Set.univ := by
  exact Port.CW.skeletonBelow_union

/-- Literal subtype inclusion, with its explicit continuous underlying map. -/
def skeletonInclusion {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] {n m : ℕ} (h : n ≤ m) :
    C(↥(skeletonBelow X n), ↥(skeletonBelow X m)) :=
  ⟨fun z => ⟨z.val, skeletonBelow_mono h z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The empty skeleton supports the initial homotopy to the selected point. -/
theorem cw_base_homotopy {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (x0 : X) :
    Nonempty (ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X 0), X)))
      ((ContinuousMap.const X x0).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X 0), X)))) := by
  exact Port.CW.cwBaseHomotopy x0

/-- The actual relative cellular extension step. All cell-filling work is a
conclusion to prove from `hpi`, not an additional hypothesis. -/
theorem cw_extend_nullhomotopy_step_t2
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X]
    (x0 : X) (n : ℕ)
    (hpi : ∀ k : ℕ, 1 ≤ k → ∀ x : X,
      Subsingleton (HomotopyGroup.Pi k X x))
    (Hn : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X)))
      ((ContinuousMap.const X x0).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X)))) :
    ∃ Hnext : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X (n + 1)), X)))
      ((ContinuousMap.const X x0).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X (n + 1)), X))),
      ∀ (t : unitInterval) (z : ↥(skeletonBelow X n)),
        Hnext (t, skeletonInclusion (Nat.le_succ n) z) = Hn (t, z) := by
  exact Port.CW.cwExtendNullhomotopyStepT2 x0 n hpi Hn

/-- Compatible skeletal homotopies glue continuously in independently chosen
domain and codomain universes, using the locally compact interval product. -/
theorem cw_homotopy_colimit_t2
    {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set X)]
    (f g : C(X, Y))
    (Hn : ∀ n : ℕ,
      ContinuousMap.Homotopy
        (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X)))
        (g.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X))))
    (hcompat : ∀ n m (hnm : n ≤ m) (t : unitInterval)
      (z : ↥(skeletonBelow X n)),
      Hn n (t, z) = Hn m (t, skeletonInclusion hnm z)) :
    ContinuousMap.Homotopic f g := by
  exact Port.CW.cwHomotopyColimitT2 f g Hn hcompat

end SeifertSurfaces.WhiteheadSupport.CW
