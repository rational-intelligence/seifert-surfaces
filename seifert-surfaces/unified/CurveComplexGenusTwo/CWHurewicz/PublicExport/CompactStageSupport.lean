import CurveComplexGenusTwo.CWHurewicz.PublicExport.GlobalCellRemoval

namespace CurveComplexGenusTwo.CWHurewicz

open Topology

private def topStageIndex {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (i : Topology.CWComplex.cell (Set.univ : Set X) n) : StageCellIndex X n :=
  ⟨⟨n, Nat.lt_succ_self n⟩, i⟩

private theorem topStagePoints_closed
    {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    (n : ℕ) (J : Set (Topology.CWComplex.cell (Set.univ : Set X) n))
    (p : ∀ i : J, CellDisk n)
    (hp : ∀ i, ‖(p i).val‖ < 1)
    {S : Set ↥(skeletonBelow X (n + 1))}
    (hS : S ⊆ Set.range (fun i : J =>
      stagePresentation n ⟨topStageIndex n i.val, p i⟩)) : IsClosed S := by
  apply (stagePresentation_quotient n).isClosed_preimage.mp
  apply isClosed_sigma_iff.mpr
  intro a
  have hsub : Set.Subsingleton
      ((Sigma.mk a) ⁻¹' (stagePresentation (X := X) n) ⁻¹' S) := by
    intro z hz w hw
    obtain ⟨i, hi⟩ := hS hz
    obtain ⟨j, hj⟩ := hS hw
    have hiz : (⟨topStageIndex n i.val, p i⟩ :
        Σ a : StageCellIndex X n, CellDisk a.1.val) = ⟨a,z⟩ :=
      stagePresentation_top_fiber n (topStageIndex n i.val) a rfl (p i) z
        (hp i) (congrArg Subtype.val hi)
    have hjw : (⟨topStageIndex n j.val, p j⟩ :
        Σ a : StageCellIndex X n, CellDisk a.1.val) = ⟨a,w⟩ :=
      stagePresentation_top_fiber n (topStageIndex n j.val) a rfl (p j) w
        (hp j) (congrArg Subtype.val hj)
    have hij : i = j := by
      have hi' := congrArg Sigma.fst hiz
      have hj' := congrArg Sigma.fst hjw
      apply Subtype.ext
      simpa [topStageIndex] using hi'.trans hj'.symm
    subst j
    cases hiz
    cases hjw
    rfl
  exact hsub.finite.isClosed

theorem compact_stage_finiteTopCellSupport
    {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    (n : ℕ) {K : Set ↥(skeletonBelow X (n + 1))} (hK : IsCompact K) :
    ∃ F : Finset (StageCellIndex X n),
      (∀ a ∈ F, a.1.val = n) ∧
      ∀ x ∈ K, x.val ∈ finiteTopCellSupport n F := by
  classical
  let J : Set (Topology.CWComplex.cell (Set.univ : Set X) n) :=
    {i | ∃ z : CellDisk n, ‖z.val‖ < 1 ∧
      stagePresentation n ⟨topStageIndex n i,z⟩ ∈ K}
  have hex : ∀ i : J, ∃ z : CellDisk n, ‖z.val‖ < 1 ∧
      stagePresentation n ⟨topStageIndex n i.val,z⟩ ∈ K :=
    fun i => i.property
  choose p hp hpK using hex
  let q : J → ↥(skeletonBelow X (n + 1)) :=
    fun i => stagePresentation n ⟨topStageIndex n i.val,p i⟩
  have hqK : Set.range q ⊆ K := by
    rintro x ⟨i,rfl⟩
    exact hpK i
  have hclosed : IsClosed (Set.range q) :=
    topStagePoints_closed n J p hp (S := Set.range q) (by exact Set.Subset.rfl)
  have hdis : IsDiscrete (Set.range q) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro s hs
    refine ⟨s, topStagePoints_closed n J p hp hs, ?_⟩
    exact Set.inter_eq_left.mpr hs
  have hqfinite : (Set.range q).Finite :=
    (hK.of_isClosed_subset hclosed hqK).finite hdis
  have hqinj : Function.Injective q := by
    intro i j hij
    have h := stagePresentation_top_fiber n (topStageIndex n i.val)
      (topStageIndex n j.val) rfl (p i) (p j) (hp i)
      (congrArg Subtype.val hij)
    apply Subtype.ext
    simpa [topStageIndex] using congrArg Sigma.fst h
  letI : Finite J := (Set.finite_range_iff hqinj).mp hqfinite
  letI : Fintype J := Fintype.ofFinite J
  let F : Finset (StageCellIndex X n) :=
    Finset.univ.image (fun i : J => topStageIndex n i.val)
  refine ⟨F, ?_, ?_⟩
  · intro a ha
    change a ∈ Finset.univ.image (fun i : J => topStageIndex n i.val) at ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    rfl
  · intro x hx
    obtain ⟨⟨a,z⟩, heq⟩ := (stagePresentation_quotient (X := X) n).surjective x
    have hav : characteristic a.1.val a.2 z = x.val :=
      congrArg Subtype.val heq
    rcases a with ⟨⟨m,hm⟩,i⟩
    by_cases hmn : m = n
    · subst m
      by_cases hz : ‖z.val‖ < 1
      · right
        have hi : i ∈ J := by
          refine ⟨z, hz, ?_⟩
          simpa [topStageIndex] using heq ▸ hx
        refine Set.mem_iUnion.mpr ⟨topStageIndex n i, ?_⟩
        refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
        · change topStageIndex n i ∈ Finset.univ.image
            (fun j : J => topStageIndex n j.val)
          exact Finset.mem_image.mpr ⟨⟨i,hi⟩, Finset.mem_univ _, rfl⟩
        · exact ⟨z.val, z.property, hav⟩
      · left
        have hzle : ‖z.val‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
        have hzeq : ‖z.val‖ = 1 := le_antisymm hzle (le_of_not_gt hz)
        have hboundary : z.val ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using hzeq
        have hbelow : characteristic n i z ∈ skeletonBelow X n :=
          (attaching n i ⟨z.val,hboundary⟩).property
        exact hav ▸ hbelow
    · left
      have hlt : m < n := by omega
      change x.val ∈ skeletonBelow X n
      rw [skeletonBelow]
      refine Set.mem_iUnion.mpr ⟨m, ?_⟩
      refine Set.mem_iUnion.mpr ⟨hlt, ?_⟩
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      exact ⟨z.val, z.property, hav⟩

end CurveComplexGenusTwo.CWHurewicz
