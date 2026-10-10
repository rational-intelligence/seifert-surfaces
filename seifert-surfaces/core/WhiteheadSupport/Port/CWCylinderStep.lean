import WhiteheadSupport.Port.CWBoundaryFaces
import WhiteheadSupport.Port.CWCellularHomotopyGlue

namespace SeifertSurfaces.WhiteheadSupport.Port.CW

universe u v

open _root_.Topology Metric

/-- Vanishing `πₙ` fills the prescribed characteristic cylinder boundary. -/
theorem cylinderBoundaryMap_extends
    {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (hpi : ∀ k : ℕ, 1 ≤ k → ∀ x : X,
      Subsingleton (HomotopyGroup.Pi k X x))
    (x₀ : X) (n : ℕ) (hn : 1 ≤ n)
    (Hn : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X))))
    (i : Topology.CWComplex.cell (Set.univ : Set X) n) :
    ∃ G : C(unitInterval × CellDisk n, X),
      (∀ (b : CellSphere n) (t : unitInterval),
        G (t, ⟨b.val, sphere_subset_closedBall b.property⟩) =
          Hn (t, attaching n i b)) ∧
      (∀ w : CellDisk n,
        G (0, w) = (characteristicToStep n i w).val) ∧
      (∀ w : CellDisk n, G (1, w) = x₀) := by
  let e := cylinderBoundarySphereHomeomorph n
  let b := cylinderBoundaryMap x₀ n Hn i
  let f : C(CellSphere (n + 1), X) :=
    b.comp ⟨e.symm, e.symm.continuous⟩
  obtain ⟨F, hF⟩ := cellSphereMap_extends_of_hpi hpi n hn f
  let G : C(unitInterval × CellDisk n, X) := F.comp (cylinderToDisk n)
  have hboundary (p : ↥(cylinderBoundary n)) : G p.val = b p := by
    calc
      G p.val = F ⟨(e p).val,
          sphere_subset_closedBall (e p).property⟩ := by rfl
      _ = f (e p) := hF (e p)
      _ = b p := by simp [f, e]
  refine ⟨G, ?_, ?_, ?_⟩
  · intro b' t
    rw [hboundary ⟨(t, ⟨b'.val, sphere_subset_closedBall b'.property⟩),
      cylinderBoundary_side n t b'⟩]
    exact cylinderBoundaryMap_side x₀ n Hn i t b'
  · intro w
    rw [hboundary ⟨((0 : unitInterval), w), cylinderBoundary_zero n w⟩]
    exact cylinderBoundaryMap_zero x₀ n Hn i w
  · intro w
    rw [hboundary ⟨((1 : unitInterval), w), cylinderBoundary_one n w⟩]
    exact cylinderBoundaryMap_one x₀ n Hn i w

/-- The reviewed Hausdorff relative cellular extension step. -/
theorem cwExtendNullhomotopyStepT2
    {X : Type u} [TopologicalSpace X]
    [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [PathConnectedSpace X]
    (x₀ : X) (n : ℕ)
    (hpi : ∀ k : ℕ, 1 ≤ k → ∀ x : X,
      Subsingleton (HomotopyGroup.Pi k X x))
    (Hn : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), X)))) :
    ∃ Hnext : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X (n + 1)), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X (n + 1)), X))),
      ∀ (t : unitInterval) (z : ↥(skeletonBelow X n)),
        Hnext (t, skeletonInclusion (Nat.le_succ n) z) = Hn (t, z) := by
  by_cases hn0 : n = 0
  · subst n
    exact cwExtendNullhomotopyStepT2_zero x₀ Hn
  · have hn : 1 ≤ n := by omega
    classical
    choose G hG using fun i =>
      cylinderBoundaryMap_extends hpi x₀ n hn Hn i
    exact cwExtendHomotopyStep_of_cellwise x₀ n Hn G
      (fun i b t => (hG i).1 b t)
      (fun i w => (hG i).2.1 w)
      (fun i w => (hG i).2.2 w)

end SeifertSurfaces.WhiteheadSupport.Port.CW
