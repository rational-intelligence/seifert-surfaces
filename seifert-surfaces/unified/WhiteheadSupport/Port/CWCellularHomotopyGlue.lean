import WhiteheadSupport.Port.CWStepT2

namespace SeifertSurfaces.WhiteheadSupport.Port.CW

universe u v

open _root_.Topology Metric
open scoped Topology.Homotopy

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]

omit [T2Space X] in
private theorem step_point_old_or_cell (n : ℕ)
    (z : ↥(skeletonBelow X (n + 1))) :
    (∃ y : ↥(skeletonBelow X n),
      skeletonInclusion (Nat.le_succ n) y = z) ∨
    (∃ (i : Topology.CWComplex.cell (Set.univ : Set X) n)
      (w : CellDisk n), characteristicToStep n i w = z) := by
  rcases Set.mem_iUnion.mp z.property with ⟨m, hm⟩
  rcases Set.mem_iUnion.mp hm with ⟨hmn, hm⟩
  rcases Set.mem_iUnion.mp hm with ⟨i, hi⟩
  by_cases hmn' : m < n
  · left
    refine ⟨⟨z.val, Set.mem_iUnion.mpr ⟨m,
      Set.mem_iUnion.mpr ⟨hmn', Set.mem_iUnion.mpr ⟨i, hi⟩⟩⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  · right
    have hmeq : m = n := by omega
    subst m
    rcases hi with ⟨w, hw, heq⟩
    refine ⟨i, ⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    exact heq

/-- Compatible cylinder maps on every new cell glue to a homotopy on the
successor skeleton. The obstruction-theoretic production of these maps is
separate from this topological gluing lemma. -/
theorem cwExtendHomotopyStep_of_cellwise
    (x₀ : X) (n : ℕ)
    (Hn : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), X))))
    (G : ∀ _i : Topology.CWComplex.cell (Set.univ : Set X) n,
      C(unitInterval × CellDisk n, X))
    (hboundary : ∀ i (b : CellSphere n) (t : unitInterval),
      G i (t, ⟨b.val, sphere_subset_closedBall b.property⟩) =
        Hn (t, attaching n i b))
    (hzero : ∀ i (w : CellDisk n),
      G i (0, w) = (characteristicToStep n i w).val)
    (hone : ∀ i (w : CellDisk n), G i (1, w) = x₀) :
    ∃ Hnext : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X (n + 1)), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X (n + 1)), X))),
      ∀ (t : unitInterval) (z : ↥(skeletonBelow X n)),
        Hnext (t, skeletonInclusion (Nat.le_succ n) z) = Hn (t, z) := by
  let F : C(↥(skeletonBelow X n), C(unitInterval, X)) :=
    (⟨fun p : ↥(skeletonBelow X n) × unitInterval => Hn (p.2, p.1),
      Hn.continuous.comp continuous_swap⟩ :
      C(↥(skeletonBelow X n) × unitInterval, X)).curry
  let D : ∀ i : Topology.CWComplex.cell (Set.univ : Set X) n,
      C(CellDisk n, C(unitInterval, X)) := fun i =>
    (⟨fun p : CellDisk n × unitInterval => G i (p.2, p.1),
      (G i).continuous.comp continuous_swap⟩ :
      C(CellDisk n × unitInterval, X)).curry
  have hcompat : ∀ i (b : CellSphere n),
      F (attaching n i b) =
        D i ⟨b.val, sphere_subset_closedBall b.property⟩ := by
    intro i b
    apply ContinuousMap.ext
    intro t
    exact (hboundary i b t).symm
  obtain ⟨h, ⟨hold, hcell⟩, _⟩ :=
    cwStepUniversal_of_t2 n F D hcompat
  let K : C(unitInterval × ↥(skeletonBelow X (n + 1)), X) :=
    ⟨fun p => h p.2 p.1,
      (ContinuousMap.continuous_uncurry_of_continuous h).comp continuous_swap⟩
  have Kold (t : unitInterval) (z : ↥(skeletonBelow X n)) :
      K (t, skeletonInclusion (Nat.le_succ n) z) = Hn (t, z) := by
    change (h (skeletonInclusion (Nat.le_succ n) z)) t = Hn (t, z)
    simpa [F] using congrFun (congrArg DFunLike.coe (hold z)) t
  have Kcell (t : unitInterval)
      (i : Topology.CWComplex.cell (Set.univ : Set X) n) (w : CellDisk n) :
      K (t, characteristicToStep n i w) = G i (t, w) := by
    change (h (characteristicToStep n i w)) t = G i (t, w)
    simpa [D] using congrFun (congrArg DFunLike.coe (hcell i w)) t
  have Kzero (z : ↥(skeletonBelow X (n + 1))) : K (0, z) = z.val := by
    rcases step_point_old_or_cell n z with ⟨y, rfl⟩ | ⟨i, w, rfl⟩
    · rw [Kold]
      exact Hn.apply_zero y
    · rw [Kcell]
      exact hzero i w
  have Kone (z : ↥(skeletonBelow X (n + 1))) : K (1, z) = x₀ := by
    rcases step_point_old_or_cell n z with ⟨y, rfl⟩ | ⟨i, w, rfl⟩
    · rw [Kold]
      exact Hn.apply_one y
    · rw [Kcell]
      exact hone i w
  exact ⟨⟨K, Kzero, Kone⟩, Kold⟩

/-- The zero-cell step uses only path connectedness; its attaching sphere is empty. -/
theorem cwExtendNullhomotopyStepT2_zero [PathConnectedSpace X]
    (x₀ : X)
    (Hn : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X 0), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X 0), X)))) :
    ∃ Hnext : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X (0 + 1)), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X (0 + 1)), X))),
      ∀ (t : unitInterval) (z : ↥(skeletonBelow X 0)),
        Hnext (t, skeletonInclusion (Nat.le_succ 0) z) = Hn (t, z) := by
  let w₀ : CellDisk 0 := ⟨0, by simp⟩
  have w_unique (w : CellDisk 0) : w = w₀ := by
    apply Subtype.ext
    funext j
    exact Fin.elim0 j
  let p (i : Topology.CWComplex.cell (Set.univ : Set X) 0) :
      Path (characteristicToStep 0 i w₀).val x₀ :=
    (PathConnectedSpace.joined _ _).somePath
  let G : ∀ _i : Topology.CWComplex.cell (Set.univ : Set X) 0,
      C(unitInterval × CellDisk 0, X) := fun i =>
    ⟨fun q => p i q.1, (p i).continuous.comp continuous_fst⟩
  apply cwExtendHomotopyStep_of_cellwise x₀ 0 Hn G
  · intro i b t
    have hb : False := by simpa [CellSphere, Pi.norm_def] using b.property
    exact hb.elim
  · intro i w
    rw [w_unique w]
    exact (p i).source
  · intro i w
    exact (p i).target

omit [T2Space X] in
/-- Vanishing positive homotopy groups gives a relative-boundary contraction
of every based cubical loop. The remaining obstruction bridge must turn the
characteristic cylinder boundary into such a loop. -/
theorem cubeLoop_nullhomotopic_of_hpi
    (hpi : ∀ k : ℕ, 1 ≤ k → ∀ x : X,
      Subsingleton (HomotopyGroup.Pi k X x))
    (k : ℕ) (hk : 1 ≤ k) (x : X)
    (p : GenLoop (Fin k) X x) :
    GenLoop.Homotopic p (GenLoop.const : GenLoop (Fin k) X x) := by
  exact Quotient.exact ((hpi k hk x).allEq
    (⟦p⟧ : HomotopyGroup.Pi k X x)
    (⟦GenLoop.const⟧ : HomotopyGroup.Pi k X x))

end SeifertSurfaces.WhiteheadSupport.Port.CW
