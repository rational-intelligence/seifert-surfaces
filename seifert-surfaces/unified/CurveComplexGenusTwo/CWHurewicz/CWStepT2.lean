import CurveComplexGenusTwo.CWHurewicz.CWBasic

namespace CurveComplexGenusTwo.CWHurewicz

open Topology Metric

variable {X : Type} [TopologicalSpace X]
  [Topology.CWComplex (Set.univ : Set X)] [T2Space X]

/-- The characteristic disk, with codomain its closed-cell image. -/
noncomputable def characteristicToClosedCell (n : ℕ)
    (i : Topology.CWComplex.cell (Set.univ : Set X) n) :
    C(CellDisk n, ↥(Topology.CWComplex.closedCell
      (C := (Set.univ : Set X)) n i)) :=
  ⟨fun z => ⟨Topology.CWComplex.map n i z.val,
      ⟨z.val, z.property, rfl⟩⟩,
    (characteristic n i).continuous.subtype_mk _⟩

theorem characteristicToClosedCell_surjective (n : ℕ)
    (i : Topology.CWComplex.cell (Set.univ : Set X) n) :
    Function.Surjective (characteristicToClosedCell n i) := by
  rintro ⟨x, z, hz, rfl⟩
  exact ⟨⟨z, hz⟩, rfl⟩

/-- Compact-domain / Hausdorff-range quotient for each characteristic disk. -/
theorem characteristicToClosedCell_quotient (n : ℕ)
    (i : Topology.CWComplex.cell (Set.univ : Set X) n) :
    IsQuotientMap (characteristicToClosedCell n i) :=
  .of_surjective_continuous
    (characteristicToClosedCell_surjective n i)
    (characteristicToClosedCell n i).continuous

/-- A lower-dimensional characteristic disk viewed in a later successor
skeleton. -/
noncomputable def characteristicToLaterStep (n m : ℕ) (hm : m ≤ n)
    (i : Topology.CWComplex.cell (Set.univ : Set X) m) :
    C(CellDisk m, ↥(skeletonBelow X (n + 1))) :=
  (skeletonInclusion (Nat.succ_le_succ hm)).comp (characteristicToStep m i)

private theorem skeletonBelow_eq_skeletonLT (n : ℕ) :
    skeletonBelow X n =
      (Topology.CWComplex.skeletonLT (Set.univ : Set X) n : Set X) := by
  simp [skeletonBelow, Topology.RelCWComplex.coe_skeletonLT]
  rfl

private theorem later_openCell_disjoint (n m : ℕ) (hm : n < m)
    (i : Topology.CWComplex.cell (Set.univ : Set X) m) :
    Disjoint (skeletonBelow X (n + 1))
      (Topology.CWComplex.openCell (C := (Set.univ : Set X)) m i) := by
  rw [skeletonBelow_eq_skeletonLT]
  exact Topology.CWComplex.disjoint_skeletonLT_openCell (by exact_mod_cast hm)

private theorem characteristicToLaterStep_val (n m : ℕ) (hm : m ≤ n)
    (i : Topology.CWComplex.cell (Set.univ : Set X) m) (z : CellDisk m) :
    (characteristicToLaterStep n m hm i z).val =
      Topology.CWComplex.map m i z.val := rfl

/-- Weak CW topology on one finite successor stage: a function continuous on
all characteristic disks present in the stage is continuous on the stage.
No finiteness assumption is made on the cell index sets. -/
theorem continuous_step_of_cellwise {Y : Type*} [TopologicalSpace Y]
    (n : ℕ) (h : ↥(skeletonBelow X (n + 1)) → Y)
    (hcell : ∀ m (hm : m ≤ n)
      (i : Topology.CWComplex.cell (Set.univ : Set X) m),
      Continuous (fun z : CellDisk m =>
        h (characteristicToLaterStep n m hm i z))) :
    Continuous h := by
  rw [continuous_iff_isClosed]
  intro s hs
  let A : Set X := {x | ∃ hx : x ∈ skeletonBelow X (n + 1), h ⟨x, hx⟩ ∈ s}
  have hAsub : A ⊆ (Set.univ : Set X) := Set.subset_univ _
  have hAcl : IsClosed A := by
    apply Topology.CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
      hAsub
    intro m hm i
    by_cases hmn : m ≤ n
    · right
      have hpre : IsClosed {z : CellDisk m |
          h (characteristicToLaterStep n m hmn i z) ∈ s} :=
        hs.preimage (hcell m hmn i)
      have hcompact : IsCompact ((characteristic m i) '' {z : CellDisk m |
          h (characteristicToLaterStep n m hmn i z) ∈ s}) :=
        hpre.isCompact.image (characteristic m i).continuous
      have hclosed : IsClosed ((fun z : CellDisk m =>
          Topology.CWComplex.map m i z.val) ''
          {z : CellDisk m |
            h (characteristicToLaterStep n m hmn i z) ∈ s}) := by
        have heqmap : (fun z : CellDisk m =>
            Topology.CWComplex.map m i z.val) =
            (characteristic m i : CellDisk m → X) := rfl
        rw [heqmap]
        exact hcompact.isClosed
      convert hclosed using 1
      ext x
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hx, hsx⟩, z, hz, rfl⟩
        refine ⟨⟨z, hz⟩, ?_, rfl⟩
        have heq : (⟨Topology.CWComplex.map m i z, hx⟩ :
            ↥(skeletonBelow X (n + 1))) =
            characteristicToLaterStep n m hmn i ⟨z, hz⟩ := by
          apply Subtype.ext
          rfl
        exact heq ▸ hsx
      · rintro ⟨z, hz, rfl⟩
        refine ⟨?_, ⟨z.val, z.property, rfl⟩⟩
        refine ⟨(characteristicToLaterStep n m hmn i z).property, ?_⟩
        have heq : (⟨Topology.CWComplex.map m i z.val,
            (characteristicToLaterStep n m hmn i z).property⟩ :
            ↥(skeletonBelow X (n + 1))) =
            characteristicToLaterStep n m hmn i z := by
          apply Subtype.ext
          rfl
        simpa [heq] using hz
    · left
      have hlt : n < m := Nat.lt_of_not_ge hmn
      exact (later_openCell_disjoint n m hlt i).mono_left
        (fun x hx => hx.1)
  have heq : h ⁻¹' s = Subtype.val ⁻¹' A := by
    ext x
    simp [A]
  rw [heq]
  exact hAcl.preimage continuous_subtype_val

private theorem disk_ball_or_sphere (n : ℕ) (z : CellDisk n) :
    z.val ∈ ball (0 : Fin n → ℝ) 1 ∨
      z.val ∈ sphere (0 : Fin n → ℝ) 1 := by
  have hz : z.val ∈ ball (0 : Fin n → ℝ) 1 ∪ sphere 0 1 := by
    rw [Metric.ball_union_sphere]
    exact z.property
  exact hz

private theorem interior_not_mem_old (n : ℕ)
    (i : Topology.CWComplex.cell (Set.univ : Set X) n)
    (z : CellDisk n) (hz : z.val ∈ ball (0 : Fin n → ℝ) 1) :
    Topology.CWComplex.map n i z.val ∉ skeletonBelow X n := by
  have hdis : Disjoint (skeletonBelow X n)
      (Topology.CWComplex.openCell (C := (Set.univ : Set X)) n i) := by
    rw [skeletonBelow_eq_skeletonLT]
    exact Topology.CWComplex.disjoint_skeletonLT_openCell le_rfl
  intro hmem
  exact (Set.disjoint_left.mp hdis) hmem ⟨z.val, hz, rfl⟩

private theorem boundary_mem_old (n : ℕ)
    (i : Topology.CWComplex.cell (Set.univ : Set X) n)
    (z : CellDisk n) (hz : z.val ∈ sphere (0 : Fin n → ℝ) 1) :
    Topology.CWComplex.map n i z.val ∈ skeletonBelow X n :=
  (attaching n i ⟨z.val, hz⟩).property

private theorem same_cell_interior_injective (n : ℕ)
    (i : Topology.CWComplex.cell (Set.univ : Set X) n)
    (u v : CellDisk n)
    (hu : u.val ∈ ball (0 : Fin n → ℝ) 1)
    (hv : v.val ∈ ball (0 : Fin n → ℝ) 1)
    (heq : Topology.CWComplex.map n i u.val =
      Topology.CWComplex.map n i v.val) : u = v := by
  apply Subtype.ext
  apply (Topology.CWComplex.map n i).injOn
  · rwa [Topology.CWComplex.source_eq]
  · rwa [Topology.CWComplex.source_eq]
  · exact heq

/-- Compatible boundary data force any two disk representatives of a point
to receive the same value. -/
theorem characteristic_fiber_values_compatible {Y : Type*} [TopologicalSpace Y]
    (n : ℕ) (f : C(↥(skeletonBelow X n), Y))
    (g : ∀ i : Topology.CWComplex.cell (Set.univ : Set X) n,
      C(CellDisk n, Y))
    (hboundary : ∀ i (z : CellSphere n),
      f (attaching n i z) =
        g i ⟨z.val, Metric.sphere_subset_closedBall z.property⟩)
    (i j : Topology.CWComplex.cell (Set.univ : Set X) n)
    (u v : CellDisk n)
    (heq : Topology.CWComplex.map n i u.val =
      Topology.CWComplex.map n j v.val) :
    g i u = g j v := by
  rcases disk_ball_or_sphere n u with hu | hu
  · rcases disk_ball_or_sphere n v with hv | hv
    · have hij : i = j := by
        by_contra hne
        have hdis := Topology.CWComplex.disjoint_openCell_of_ne
          (C := (Set.univ : Set X)) (n := n) (m := n) (i := i) (j := j)
          (by simpa using hne)
        exact (Set.disjoint_left.mp hdis) ⟨u.val, hu, rfl⟩
          (heq ▸ ⟨v.val, hv, rfl⟩)
      subst j
      rw [same_cell_interior_injective n i u v hu hv heq]
    · exact False.elim ((interior_not_mem_old n i u hu)
        (heq ▸ boundary_mem_old n j v hv))
  · have hug : g i u = f (attaching n i ⟨u.val, hu⟩) := by
      simpa using (hboundary i ⟨u.val, hu⟩).symm
    rcases disk_ball_or_sphere n v with hv | hv
    · exact False.elim ((interior_not_mem_old n j v hv)
        (heq.symm ▸ boundary_mem_old n i u hu))
    · have hvg : g j v = f (attaching n j ⟨v.val, hv⟩) := by
        simpa using (hboundary j ⟨v.val, hv⟩).symm
      rw [hug, hvg]
      congr 1
      apply Subtype.ext
      exact heq

private theorem exists_newCell_of_not_old (n : ℕ)
    (x : ↥(skeletonBelow X (n + 1)))
    (hx : x.val ∉ skeletonBelow X n) :
    ∃ i : Topology.CWComplex.cell (Set.univ : Set X) n,
      ∃ z : CellDisk n, Topology.CWComplex.map n i z.val = x.val := by
  rcases Set.mem_iUnion.mp x.property with ⟨m, hm⟩
  rcases Set.mem_iUnion.mp hm with ⟨hmn, hm⟩
  rcases Set.mem_iUnion.mp hm with ⟨i, hi⟩
  have hmeq : m = n := by
    by_contra hne
    have hlt : m < n := by omega
    exact hx (Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hlt,
      Set.mem_iUnion.mpr ⟨i, hi⟩⟩⟩)
  subst m
  rcases hi with ⟨z, hz, heq⟩
  exact ⟨i, ⟨z, hz⟩, heq⟩

private noncomputable def chosenNewCell (n : ℕ)
    (x : ↥(skeletonBelow X (n + 1)))
    (hx : x.val ∉ skeletonBelow X n) :
    Σ i : Topology.CWComplex.cell (Set.univ : Set X) n,
      {z : CellDisk n // Topology.CWComplex.map n i z.val = x.val} :=
  let he := exists_newCell_of_not_old n x hx
  let z := Classical.choose (Classical.choose_spec he)
  ⟨Classical.choose he, ⟨z, Classical.choose_spec (Classical.choose_spec he)⟩⟩

private noncomputable def successorValue {Y : Type*} [TopologicalSpace Y]
    (n : ℕ) (f : C(↥(skeletonBelow X n), Y))
    (g : ∀ i : Topology.CWComplex.cell (Set.univ : Set X) n,
      C(CellDisk n, Y))
    (x : ↥(skeletonBelow X (n + 1))) : Y := by
  classical
  exact if hx : x.val ∈ skeletonBelow X n then f ⟨x.val, hx⟩
    else g (chosenNewCell n x hx).1 (chosenNewCell n x hx).2.1

private theorem successorValue_old {Y : Type*} [TopologicalSpace Y]
    (n : ℕ) (f : C(↥(skeletonBelow X n), Y))
    (g : ∀ i : Topology.CWComplex.cell (Set.univ : Set X) n,
      C(CellDisk n, Y))
    (z : ↥(skeletonBelow X n)) :
    successorValue n f g (skeletonInclusion (Nat.le_succ n) z) = f z := by
  simp [successorValue, z.property, skeletonInclusion]

private theorem successorValue_cell {Y : Type*} [TopologicalSpace Y]
    (n : ℕ) (f : C(↥(skeletonBelow X n), Y))
    (g : ∀ i : Topology.CWComplex.cell (Set.univ : Set X) n,
      C(CellDisk n, Y))
    (hboundary : ∀ i (z : CellSphere n),
      f (attaching n i z) =
        g i ⟨z.val, Metric.sphere_subset_closedBall z.property⟩)
    (i : Topology.CWComplex.cell (Set.univ : Set X) n)
    (z : CellDisk n) :
    successorValue n f g (characteristicToStep n i z) = g i z := by
  have hval : (characteristicToStep n i z).val =
      Topology.CWComplex.map n i z.val := rfl
  by_cases hx : Topology.CWComplex.map n i z.val ∈ skeletonBelow X n
  · have hz : z.val ∈ sphere (0 : Fin n → ℝ) 1 := by
      rcases disk_ball_or_sphere n z with hb | hs
      · exact False.elim ((interior_not_mem_old n i z hb) hx)
      · exact hs
    have heq : (⟨Topology.CWComplex.map n i z.val, hx⟩ :
        ↥(skeletonBelow X n)) = attaching n i ⟨z.val, hz⟩ := by
      apply Subtype.ext
      rfl
    simpa [successorValue, hval, hx, heq] using hboundary i ⟨z.val, hz⟩
  · let w := chosenNewCell n (characteristicToStep n i z) hx
    have hweq : Topology.CWComplex.map n w.1 w.2.1.val =
        Topology.CWComplex.map n i z.val := w.2.2
    have hw := characteristic_fiber_values_compatible n f g hboundary
      w.1 i w.2.1 z hweq
    simpa [successorValue, hval, hx, w] using hw

/-- The repaired successor attachment mapping property for Hausdorff CW
spaces, stated with the boundary equation exposed directly. -/
theorem cwStepUniversal_of_t2 {Y : Type*} [TopologicalSpace Y]
    (n : ℕ)
    (f : C(↥(skeletonBelow X n), Y))
    (g : ∀ i : Topology.CWComplex.cell (Set.univ : Set X) n,
      C(CellDisk n, Y))
    (hboundary : ∀ i (z : CellSphere n),
      f (attaching n i z) =
        g i ⟨z.val, Metric.sphere_subset_closedBall z.property⟩) :
    ∃! h : C(↥(skeletonBelow X (n + 1)), Y),
      (∀ z, h (skeletonInclusion (Nat.le_succ n) z) = f z) ∧
      (∀ i z, h (characteristicToStep n i z) = g i z) := by
  let h : ↥(skeletonBelow X (n + 1)) → Y := successorValue n f g
  have hc : Continuous h := by
    apply continuous_step_of_cellwise n h
    intro m hm i
    by_cases hmn : m < n
    · have hsucc : m + 1 ≤ n := Nat.succ_le_of_lt hmn
      have heq : (fun z : CellDisk m =>
          h (characteristicToLaterStep n m hm i z)) =
          fun z => f (skeletonInclusion hsucc (characteristicToStep m i z)) := by
        funext z
        have hpt : characteristicToLaterStep n m hm i z =
            skeletonInclusion (Nat.le_succ n)
              (skeletonInclusion hsucc (characteristicToStep m i z)) := by
          apply Subtype.ext
          rfl
        rw [hpt]
        exact successorValue_old n f g _
      rw [heq]
      fun_prop
    · have hmeq : m = n := by omega
      subst m
      have heq : (fun z : CellDisk n =>
          h (characteristicToLaterStep n n hm i z)) =
          fun z => g i z := by
        funext z
        have hpt : characteristicToLaterStep n n hm i z =
            characteristicToStep n i z := by
          apply Subtype.ext
          rfl
        rw [hpt]
        exact successorValue_cell n f g hboundary i z
      rw [heq]
      exact (g i).continuous
  refine ⟨⟨h, hc⟩, ?_, ?_⟩
  · constructor
    · exact successorValue_old n f g
    · exact successorValue_cell n f g hboundary
  · intro k hk
    apply ContinuousMap.ext
    intro x
    by_cases hx : x.val ∈ skeletonBelow X n
    · let z : ↥(skeletonBelow X n) := ⟨x.val, hx⟩
      have hpt : skeletonInclusion (Nat.le_succ n) z = x := by
        apply Subtype.ext
        rfl
      rw [← hpt, hk.1 z]
      exact (successorValue_old n f g z).symm
    · obtain ⟨i, z, heq⟩ := exists_newCell_of_not_old n x hx
      have hpt : characteristicToStep n i z = x := by
        apply Subtype.ext
        exact heq
      rw [← hpt, hk.2 i z]
      exact (successorValue_cell n f g hboundary i z).symm

end CurveComplexGenusTwo.CWHurewicz
