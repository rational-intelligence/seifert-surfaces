import WhiteheadSupport.Port.CWBasic

namespace SeifertSurfaces.WhiteheadSupport.Port.CW

universe u v

open Topology

variable {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [Topology.CWComplex (Set.univ : Set X)]

/-- Compatible skeletal maps determine a unique underlying function on the CW space.
Continuity is the separate weak-topology obligation. -/
noncomputable def coherentSkeletonFunction
    (f : ∀ n : ℕ, C(↥(skeletonBelow X n), Y)) : X → Y := by
  classical
  intro x
  have hx : x ∈ ⋃ n : ℕ, skeletonBelow X n := by
    rw [skeletonBelow_union]
    trivial
  let n : ℕ := Classical.choose (Set.mem_iUnion.mp hx)
  exact f n ⟨x, Classical.choose_spec (Set.mem_iUnion.mp hx)⟩

theorem coherentSkeletonFunction_apply
    (f : ∀ n : ℕ, C(↥(skeletonBelow X n), Y))
    (hcompat : ∀ n m (hnm : n ≤ m) (z : ↥(skeletonBelow X n)),
      f n z = f m (skeletonInclusion hnm z))
    (n : ℕ) (z : ↥(skeletonBelow X n)) :
    coherentSkeletonFunction f z.val = f n z := by
  classical
  unfold coherentSkeletonFunction
  dsimp
  let hx : z.val ∈ ⋃ k : ℕ, skeletonBelow X k := by
    rw [skeletonBelow_union]
    trivial
  let m := Classical.choose (Set.mem_iUnion.mp hx)
  have hm : z.val ∈ skeletonBelow X m := Classical.choose_spec (Set.mem_iUnion.mp hx)
  rcases le_total m n with hmn | hnm
  · simpa only [skeletonInclusion, ContinuousMap.coe_mk, Subtype.coe_mk] using
      hcompat m n hmn ⟨z.val, hm⟩
  · exact (hcompat n m hnm z).symm

theorem coherentSkeletonFunction_unique
    (f : ∀ n : ℕ, C(↥(skeletonBelow X n), Y))
    (hcompat : ∀ n m (hnm : n ≤ m) (z : ↥(skeletonBelow X n)),
      f n z = f m (skeletonInclusion hnm z))
    (g : X → Y)
    (hg : ∀ n (z : ↥(skeletonBelow X n)), g z.val = f n z) :
    g = coherentSkeletonFunction f := by
  funext x
  have hx : x ∈ ⋃ n : ℕ, skeletonBelow X n := by
    rw [skeletonBelow_union]
    trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  calc
    g x = f n ⟨x, hn⟩ := hg n ⟨x, hn⟩
    _ = coherentSkeletonFunction f x := (coherentSkeletonFunction_apply f hcompat n ⟨x, hn⟩).symm

/-- The compatible skeletal homotopies also determine a pointwise global map. -/
noncomputable def coherentSkeletonHomotopyFunction
    (f g : C(X, Y))
    (Hn : ∀ n : ℕ,
      ContinuousMap.Homotopy
        (f.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y))
        (g.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y))) : unitInterval × X → Y := by
  classical
  intro p
  have hp : p.2 ∈ ⋃ n : ℕ, skeletonBelow X n := by
    rw [skeletonBelow_union]
    trivial
  let n := Classical.choose (Set.mem_iUnion.mp hp)
  exact Hn n (p.1, ⟨p.2, Classical.choose_spec (Set.mem_iUnion.mp hp)⟩)

theorem coherentSkeletonHomotopyFunction_apply
    (f g : C(X, Y))
    (Hn : ∀ n : ℕ,
      ContinuousMap.Homotopy
        (f.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y))
        (g.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y)))
    (hcompat : ∀ n m (hnm : n ≤ m) (t : unitInterval)
      (z : ↥(skeletonBelow X n)),
      Hn n (t, z) = Hn m (t, skeletonInclusion hnm z))
    (n : ℕ) (t : unitInterval) (z : ↥(skeletonBelow X n)) :
    coherentSkeletonHomotopyFunction f g Hn (t, z.val) = Hn n (t, z) := by
  classical
  unfold coherentSkeletonHomotopyFunction
  dsimp
  let hp : z.val ∈ ⋃ k : ℕ, skeletonBelow X k := by
    rw [skeletonBelow_union]
    trivial
  let m := Classical.choose (Set.mem_iUnion.mp hp)
  have hm : z.val ∈ skeletonBelow X m := Classical.choose_spec (Set.mem_iUnion.mp hp)
  rcases le_total m n with hmn | hnm
  · simpa only [skeletonInclusion, ContinuousMap.coe_mk, Subtype.coe_mk] using
      hcompat m n hmn t ⟨z.val, hm⟩
  · exact (hcompat n m hnm t z).symm

theorem coherentSkeletonHomotopyFunction_unique
    (f g : C(X, Y))
    (Hn : ∀ n : ℕ,
      ContinuousMap.Homotopy
        (f.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y))
        (g.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y)))
    (hcompat : ∀ n m (hnm : n ≤ m) (t : unitInterval)
      (z : ↥(skeletonBelow X n)),
      Hn n (t, z) = Hn m (t, skeletonInclusion hnm z))
    (k : unitInterval × X → Y)
    (hk : ∀ n (t : unitInterval) (z : ↥(skeletonBelow X n)),
      k (t, z.val) = Hn n (t, z)) :
    k = coherentSkeletonHomotopyFunction f g Hn := by
  funext p
  have hp : p.2 ∈ ⋃ n : ℕ, skeletonBelow X n := by
    rw [skeletonBelow_union]
    trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
  calc
    k p = Hn n (p.1, ⟨p.2, hn⟩) := hk n p.1 ⟨p.2, hn⟩
    _ = coherentSkeletonHomotopyFunction f g Hn p :=
      (coherentSkeletonHomotopyFunction_apply f g Hn hcompat n p.1 ⟨p.2, hn⟩).symm

theorem coherentSkeletonHomotopyFunction_zero
    (f g : C(X, Y))
    (Hn : ∀ n : ℕ,
      ContinuousMap.Homotopy
        (f.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y))
        (g.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y)))
    (hcompat : ∀ n m (hnm : n ≤ m) (t : unitInterval)
      (z : ↥(skeletonBelow X n)),
      Hn n (t, z) = Hn m (t, skeletonInclusion hnm z))
    (x : X) : coherentSkeletonHomotopyFunction f g Hn (0, x) = f x := by
  have hx : x ∈ ⋃ n : ℕ, skeletonBelow X n := by
    rw [skeletonBelow_union]
    trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  rw [coherentSkeletonHomotopyFunction_apply f g Hn hcompat n 0 ⟨x, hn⟩]
  exact (Hn n).apply_zero ⟨x, hn⟩

theorem coherentSkeletonHomotopyFunction_one
    (f g : C(X, Y))
    (Hn : ∀ n : ℕ,
      ContinuousMap.Homotopy
        (f.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y))
        (g.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y)))
    (hcompat : ∀ n m (hnm : n ≤ m) (t : unitInterval)
      (z : ↥(skeletonBelow X n)),
      Hn n (t, z) = Hn m (t, skeletonInclusion hnm z))
    (x : X) : coherentSkeletonHomotopyFunction f g Hn (1, x) = g x := by
  have hx : x ∈ ⋃ n : ℕ, skeletonBelow X n := by
    rw [skeletonBelow_union]
    trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  rw [coherentSkeletonHomotopyFunction_apply f g Hn hcompat n 1 ⟨x, hn⟩]
  exact (Hn n).apply_one ⟨x, hn⟩

/-- The exact remaining continuity obligation for global homotopy gluing. -/
theorem coherentSkeletonHomotopy_of_continuous
    (f g : C(X, Y))
    (Hn : ∀ n : ℕ,
      ContinuousMap.Homotopy
        (f.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y))
        (g.comp ⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow X n), Y)))
    (hcompat : ∀ n m (hnm : n ≤ m) (t : unitInterval)
      (z : ↥(skeletonBelow X n)),
      Hn n (t, z) = Hn m (t, skeletonInclusion hnm z))
    (hcontinuous : Continuous (coherentSkeletonHomotopyFunction f g Hn)) :
    ContinuousMap.Homotopic f g := by
  refine ⟨{
    toContinuousMap := ⟨coherentSkeletonHomotopyFunction f g Hn, hcontinuous⟩
    map_zero_left := coherentSkeletonHomotopyFunction_zero f g Hn hcompat
    map_one_left := coherentSkeletonHomotopyFunction_one f g Hn hcompat
  }⟩

end SeifertSurfaces.WhiteheadSupport.Port.CW
