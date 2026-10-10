import CurveComplexGenusTwo.CWHurewicz.PublicExport.GlobalCellRemoval

namespace CurveComplexGenusTwo.CWHurewicz

open Topology

private theorem highStageSelected_closed
    {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    (p : ℕ → X) (hp : ∀ n, p n ∉ skeletonBelow X n)
    {A : Set X} (hA : A ⊆ Set.range p) : IsClosed A := by
  apply (Topology.CWComplex.closed (Set.univ : Set X) A (Set.subset_univ A)).mpr
  intro m i
  have hfinite : (A ∩ Topology.CWComplex.closedCell
      (C := (Set.univ : Set X)) m i).Finite := by
    apply ((Finset.range (m + 1)).finite_toSet.image p).subset
    rintro x ⟨hxA,hxcell⟩
    obtain ⟨n,rfl⟩ := hA hxA
    have hnm : n < m + 1 := by
      by_contra hn
      have hle : m + 1 ≤ n := le_of_not_gt hn
      have hmem : p n ∈ skeletonBelow X (m + 1) := by
        rw [skeletonBelow]
        refine Set.mem_iUnion.mpr ⟨m, ?_⟩
        refine Set.mem_iUnion.mpr ⟨Nat.lt_succ_self m, ?_⟩
        exact Set.mem_iUnion.mpr ⟨i, hxcell⟩
      exact hp n (skeletonBelow_mono hle hmem)
    exact ⟨n, by simp [hnm], rfl⟩
  exact hfinite.isClosed

theorem compact_subset_skeletonBelow
    {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    {K : Set X} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ skeletonBelow X n := by
  classical
  by_contra h
  have hex : ∀ n : ℕ, ∃ x : X, x ∈ K ∧ x ∉ skeletonBelow X n := by
    intro n
    by_contra hn
    apply h
    refine ⟨n, ?_⟩
    intro x hx
    by_contra hnot
    exact hn ⟨x,hx,hnot⟩
  choose p hpK hpOutside using hex
  have hrangeK : Set.range p ⊆ K := by
    rintro x ⟨n,rfl⟩
    exact hpK n
  have hclosed : IsClosed (Set.range p) :=
    highStageSelected_closed p hpOutside Set.Subset.rfl
  have hdis : IsDiscrete (Set.range p) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro s hs
    refine ⟨s, highStageSelected_closed p hpOutside hs, ?_⟩
    exact Set.inter_eq_left.mpr hs
  have hfinite : (Set.range p).Finite :=
    (hK.of_isClosed_subset hclosed hrangeK).finite hdis
  have hcover : Set.range p ⊆ ⋃ n : ℕ, skeletonBelow X n := by
    intro x _
    have hall : x ∈ ⋃ m : ℕ,
        ⋃ i : Topology.CWComplex.cell (Set.univ : Set X) m,
          Topology.CWComplex.openCell (C := (Set.univ : Set X)) m i := by
      exact (Topology.CWComplex.iUnion_openCell_eq_complex
        (C := (Set.univ : Set X))).symm ▸ Set.mem_univ x
    obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hall
    obtain ⟨i,hmi⟩ := Set.mem_iUnion.mp hm
    refine Set.mem_iUnion.mpr ⟨m + 1, ?_⟩
    rw [skeletonBelow]
    refine Set.mem_iUnion.mpr ⟨m, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Nat.lt_succ_self m, ?_⟩
    exact Set.mem_iUnion.mpr ⟨i,
      (Topology.CWComplex.openCell_subset_closedCell
        (C := (Set.univ : Set X)) m i) hmi⟩
  obtain ⟨I,hI,hsub⟩ := Set.finite_subset_iUnion hfinite hcover
  obtain ⟨N,hN⟩ := hI.bddAbove
  have hpN : p N ∈ skeletonBelow X N := by
    have hpn := hsub (Set.mem_range_self N)
    obtain ⟨m,hpm⟩ := Set.mem_iUnion.mp hpn
    obtain ⟨hm,hpm⟩ := Set.mem_iUnion.mp hpm
    exact skeletonBelow_mono (hN hm) hpm
  exact hpOutside N hpN

end CurveComplexGenusTwo.CWHurewicz
