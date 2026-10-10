import Mathlib

/-!
Source: curve-complex-genus-two.pdf, proof of Theorem 1.1 (Section 11).
Blueprint: scratch/blueprinter/cw_hurewicz/PLAN.md, nodes 0-1.
All theorem bodies here are proof obligations for later reviewed proof work.
-/

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology

set_option synthInstance.maxHeartbeats 1000000

/-- The exact integral singular-homology object used by `IsAcyclicIntegral`. -/
noncomputable abbrev H (X : Type) [TopologicalSpace X] (n : ℕ) : ModuleCat.{0} ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)

/-- Degree zero is the canonical augmentation, not an assertion that `H₀` is zero. -/
def AcyclicIntegral (X : Type) [TopologicalSpace X] : Prop :=
  (∀ n : ℕ, 0 < n → IsZero (H X n)) ∧
  IsIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ))

theorem acyclic_positive {X : Type} [TopologicalSpace X]
    (h : AcyclicIntegral X) (n : ℕ) (hn : 0 < n) : IsZero (H X n) := by
  exact h.1 n hn

theorem nonempty_of_simplyConnected {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] : Nonempty X := by
  exact PathConnectedSpace.nonempty

theorem pathConnected_of_simplyConnected {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] : PathConnectedSpace X := by
  infer_instance

theorem homology_subsingleton_of_isZero {X : Type} [TopologicalSpace X]
    (n : ℕ) (_h : IsZero (H X n)) : Subsingleton (H X n) := by
  exact ModuleCat.subsingleton_of_isZero _h

/-- The union of all closed cells of dimensions strictly below `n`. Unlike
Mathlib's `skeletonLT`, this set definition does not require `T2Space`. -/
def skeletonBelow (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) : Set X :=
  ⋃ (m : ℕ) (_ : m < n) (i : Topology.CWComplex.cell (Set.univ : Set X) m),
    Topology.CWComplex.closedCell (C := (Set.univ : Set X)) m i

theorem skeletonBelow_mono {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] {n m : ℕ} (h : n ≤ m) :
    skeletonBelow X n ⊆ skeletonBelow X m := by
  intro x hx
  simp only [skeletonBelow, Set.mem_iUnion] at hx ⊢
  obtain ⟨k, hk, i, hi⟩ := hx
  exact ⟨k, lt_of_lt_of_le hk h, i, hi⟩

theorem skeletonBelow_union {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] :
    (⋃ n : ℕ, skeletonBelow X n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ (⋃ (m : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set X) m),
      Topology.CWComplex.closedCell (C := (Set.univ : Set X)) m i) := by
    exact (Topology.CWComplex.union (C := (Set.univ : Set X))).symm ▸ Set.mem_univ x
  simp only [Set.mem_iUnion] at hx
  obtain ⟨m, i, hmi⟩ := hx
  refine Set.mem_iUnion.2 ⟨m + 1, ?_⟩
  change x ∈ ⋃ (k : ℕ) (_ : k < m + 1)
    (j : Topology.CWComplex.cell (Set.univ : Set X) k),
      Topology.CWComplex.closedCell (C := (Set.univ : Set X)) k j
  exact Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨by omega,
    Set.mem_iUnion.2 ⟨i, hmi⟩⟩⟩

abbrev CellDisk (n : ℕ) :=
  ↥(Metric.closedBall (0 : Fin n → ℝ) 1)

abbrev CellSphere (n : ℕ) :=
  ↥(Metric.sphere (0 : Fin n → ℝ) 1)

/-- The actual characteristic map, restricted to its closed domain. -/
noncomputable def characteristic {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (i : Topology.CWComplex.cell (Set.univ : Set X) n) : C(CellDisk n, X) :=
  ⟨fun z => Topology.CWComplex.map n i z.val,
    (Topology.CWComplex.continuousOn n i).domRestrict⟩

/-- The attaching map lands in the union of lower-dimensional closed cells. -/
noncomputable def attaching {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (i : Topology.CWComplex.cell (Set.univ : Set X) n) :
    C(CellSphere n, ↥(skeletonBelow X n)) :=
  ⟨fun z => ⟨Topology.CWComplex.map n i z.val, by
      obtain ⟨I, hI⟩ := Topology.CWComplex.cellFrontier_subset_finite_closedCell n i
      have hz : Topology.CWComplex.map n i z.val ∈
          Topology.CWComplex.cellFrontier (C := (Set.univ : Set X)) n i :=
        ⟨z.val, z.property, rfl⟩
      have hi := hI hz
      simp only [Set.mem_iUnion] at hi
      obtain ⟨m, hm, j, hj, hmem⟩ := hi
      exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm,
        Set.mem_iUnion.mpr ⟨j, hmem⟩⟩⟩⟩,
    ((Topology.CWComplex.continuousOn n i).mono
      Metric.sphere_subset_closedBall).domRestrict.subtype_mk _⟩

/-- Every characteristic disk maps into the next skeletal set. -/
noncomputable def characteristicToStep {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (i : Topology.CWComplex.cell (Set.univ : Set X) n) :
    C(CellDisk n, ↥(skeletonBelow X (n + 1))) :=
  ⟨fun z => ⟨Topology.CWComplex.map n i z.val, by
      exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨by omega,
        Set.mem_iUnion.mpr ⟨i, ⟨z.val, z.property, rfl⟩⟩⟩⟩⟩,
    (Topology.CWComplex.continuousOn n i).domRestrict.subtype_mk _⟩

/-- Inclusion of one skeletal set into a later skeletal set. -/
noncomputable def skeletonInclusion {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] {n m : ℕ} (h : n ≤ m) :
    C(↥(skeletonBelow X n), ↥(skeletonBelow X m)) :=
  ⟨fun z => ⟨z.val, skeletonBelow_mono h z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

end CurveComplexGenusTwo.CWHurewicz
