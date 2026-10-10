import WhiteheadSupport.Port.CWColimitT2Repaired

namespace SeifertSurfaces.WhiteheadSupport.Port.CW

universe u v

open _root_.Topology
open scoped ContinuousMap

/-- The empty lower skeleton supports the initial identity-to-constant homotopy. -/
theorem cwBaseHomotopy {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (x₀ : X) :
    Nonempty (ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X 0), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X 0), X)))) := by
  have heq : ((ContinuousMap.id X).comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X 0), X))) =
      ((ContinuousMap.const X x₀).comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X 0), X))) := by
    ext z
    have hz : False := by simpa [skeletonBelow] using z.property
    exact hz.elim
  rw [← heq]
  exact ⟨ContinuousMap.Homotopy.refl _⟩

/-- The point-map Whitehead argument after the cellular extension theorem is supplied. -/
theorem cwPointWhiteheadT2_of_step {X : Type u} [TopologicalSpace X]
    [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [PathConnectedSpace X]
    (_hpi : ∀ n : ℕ, 1 ≤ n → ∀ x : X,
      Subsingleton (HomotopyGroup.Pi n X x))
    (hstep : ∀ (x₀ : X) (n : ℕ)
      (Hn : ContinuousMap.Homotopy
        ((ContinuousMap.id X).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(skeletonBelow X n), X)))
        ((ContinuousMap.const X x₀).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(skeletonBelow X n), X)))),
      ∃ Hnext : ContinuousMap.Homotopy
        ((ContinuousMap.id X).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(skeletonBelow X (n + 1)), X)))
        ((ContinuousMap.const X x₀).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(skeletonBelow X (n + 1)), X))),
        ∀ (t : unitInterval) (z : ↥(skeletonBelow X n)),
          Hnext (t, skeletonInclusion (Nat.le_succ n) z) = Hn (t, z)) :
    Nonempty (X ≃ₕ Unit) := by
  obtain ⟨x₀⟩ : Nonempty X := PathConnectedSpace.nonempty
  let F : C(X, X) := ContinuousMap.id X
  let G : C(X, X) := ContinuousMap.const X x₀
  let P (n : ℕ) := ContinuousMap.Homotopy
    (F.comp (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥(skeletonBelow X n), X)))
    (G.comp (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥(skeletonBelow X n), X)))
  let H : ∀ n, P n := Nat.rec (Classical.choice (cwBaseHomotopy x₀))
    (fun n h => Classical.choose (hstep x₀ n h))
  have hsuccessor (n : ℕ) (t : unitInterval) (z : ↥(skeletonBelow X n)) :
      H (n + 1) (t, skeletonInclusion (Nat.le_succ n) z) = H n (t, z) := by
    exact (Classical.choose_spec (hstep x₀ n (H n))) t z
  have hcompat : ∀ n m (hnm : n ≤ m) (t : unitInterval)
      (z : ↥(skeletonBelow X n)),
      H n (t, z) = H m (t, skeletonInclusion hnm z) := by
    intro n m hnm
    induction hnm with
    | refl =>
      intro t z
      rfl
    | @step m hnm ih =>
      intro t z
      rw [ih t z]
      exact (hsuccessor m t (skeletonInclusion hnm z)).symm
  have hfg : F.Homotopic G := cwHomotopyColimitT2 F G H hcompat
  refine ⟨⟨ContinuousMap.const X Unit.unit,
    ContinuousMap.const Unit x₀, ?_, ?_⟩⟩
  · exact hfg.symm
  · rfl

theorem contractibleOfCWAllPiSubsingletonT2_of_step
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] [PathConnectedSpace X]
    (hpi : ∀ n : ℕ, 1 ≤ n → ∀ x : X,
      Subsingleton (HomotopyGroup.Pi n X x))
    (hstep : ∀ (x₀ : X) (n : ℕ)
      (Hn : ContinuousMap.Homotopy
        ((ContinuousMap.id X).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(skeletonBelow X n), X)))
        ((ContinuousMap.const X x₀).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(skeletonBelow X n), X)))),
      ∃ Hnext : ContinuousMap.Homotopy
        ((ContinuousMap.id X).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(skeletonBelow X (n + 1)), X)))
        ((ContinuousMap.const X x₀).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(skeletonBelow X (n + 1)), X))),
        ∀ (t : unitInterval) (z : ↥(skeletonBelow X n)),
          Hnext (t, skeletonInclusion (Nat.le_succ n) z) = Hn (t, z)) :
    ContractibleSpace X := by
  exact (Classical.choice (cwPointWhiteheadT2_of_step hpi hstep)).contractibleSpace

end SeifertSurfaces.WhiteheadSupport.Port.CW
