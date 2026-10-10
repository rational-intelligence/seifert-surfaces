import CurveComplexGenusTwo.CWHurewicz.PublicExport.CellPointAvoidance

namespace CurveComplexGenusTwo.CWHurewicz
open Topology
open scoped unitInterval

private theorem openCore_not_below
    {X : Type} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    (n : ℕ) (a : StageCellIndex X n) (ha : a.1.val = n)
    (x : ↥(skeletonBelow X (n+1)))
    (hx : x ∈ stageOpenCore n a 1) : x.val ∉ skeletonBelow X n := by
  rcases hx with ⟨z, hz, heq⟩
  have hdis : Disjoint (skeletonBelow X n)
      (Topology.CWComplex.openCell (C := (Set.univ : Set X)) a.1.val a.2) := by
    have he : skeletonBelow X n =
        (Topology.CWComplex.skeletonLT (Set.univ : Set X) n : Set X) := by
      simp [skeletonBelow, Topology.RelCWComplex.coe_skeletonLT]
      rfl
    rw [he]
    exact Topology.CWComplex.disjoint_skeletonLT_openCell (by exact_mod_cast ha.ge)
  intro h
  exact Set.disjoint_left.mp hdis h ⟨z, hz, heq⟩

private theorem openCore_ne_other_center
    {X : Type} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    (n : ℕ) (a b : StageCellIndex X n) (ha : a.1.val = n) (hab : a ≠ b)
    (x : ↥(skeletonBelow X (n+1)))
    (hx : x ∈ stageOpenCore n a 1) : x ≠ stageCellCenter n b := by
  rintro he
  rcases hx with ⟨z, hz, heq⟩
  have hz' : z ∈ Metric.closedBall (0 : Fin a.1.val → ℝ) 1 :=
    Metric.ball_subset_closedBall hz
  have heq' := heq.trans (congrArg Subtype.val he)
  change (characteristic a.1.val a.2 ⟨z,hz'⟩) =
    characteristic b.1.val b.2 ⟨0,by simp⟩ at heq'
  have hf := stagePresentation_top_fiber n a b ha ⟨z,hz'⟩ ⟨0,by simp⟩
    (by simpa only [Metric.mem_ball, dist_zero_right] using hz) heq'
  exact hab (congrArg Sigma.fst hf)

private theorem openCore_mem_finiteSupport
    {X : Type} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    (n : ℕ) (F : Finset (StageCellIndex X n)) (a : StageCellIndex X n)
    (ha : a ∈ F) (x : ↥(skeletonBelow X (n+1)))
    (hx : x ∈ stageOpenCore n a 1) : x.val ∈ finiteTopCellSupport n F := by
  rcases hx with ⟨z,hz,heq⟩
  right
  apply Set.mem_iUnion.mpr
  refine ⟨a, Set.mem_iUnion.mpr ⟨ha, ?_⟩⟩
  exact ⟨z, Metric.ball_subset_closedBall hz, heq⟩

/-- Iterated geometric perturbation, retaining the given finite top-cell support
and fixing every source point initially in the lower skeleton. -/
theorem finiteCellPointAvoidance
    {X : Type} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    {S : Type*} [TopologicalSpace S] {k n : ℕ}
    (e : S → (Fin k → ℝ)) (he : IsClosedEmbedding e) (hkn : k < n)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (f : C(S, ↥(skeletonBelow X (n+1))))
    (hsupp : ∀ z, (f z).val ∈ finiteTopCellSupport n F) :
    ∃ g : C(S, ↥(skeletonBelow X (n+1))),
    ∃ H : ContinuousMap.HomotopyRel f g
        {z | (f z).val ∈ skeletonBelow X n},
        (∀ z a, a ∈ F → g z ≠ stageCellCenter n a) ∧
        ∀ t z, (H (t,z)).val ∈ finiteTopCellSupport n F := by
  classical
  let P : Set S := {z | (f z).val ∈ skeletonBelow X n}
  have hgo (A : Finset (StageCellIndex X n)) (hA : A ⊆ F) :
      ∃ g : C(S, ↥(skeletonBelow X (n+1))),
        ∃ H : ContinuousMap.HomotopyRel f g P,
          (∀ z a, a ∈ A → g z ≠ stageCellCenter n a) ∧
          ∀ t z, (H (t,z)).val ∈ finiteTopCellSupport n F := by
    induction A using Finset.induction_on with
    | empty =>
        refine ⟨f, ContinuousMap.HomotopyRel.refl f P, ?_, ?_⟩
        · intro z a ha
          simp at ha
        · intro t z
          simpa using hsupp z
    | @insert a A ha ih =>
        have haF : a ∈ F := hA (Finset.mem_insert_self a A)
        have hAF : A ⊆ F := Finset.Subset.trans (Finset.subset_insert a A) hA
        obtain ⟨g,H,havoid,hsup⟩ := ih hAF
        obtain ⟨g',K,hnew,hloc⟩ := oneCellPointAvoidance e he hkn a (hF a haF) g
        have hKfix (t : I) (z : S) (hz : z ∈ P) : K (t,z) = g z := by
          apply K.prop t z
          intro hc
          have hgz : g z = f z := by simpa using H.prop 1 z hz
          have ho : f z ∈ stageOpenCore n a 1 :=
            stageClosedCore_subset_open n a (by norm_num : (1:ℝ)/2 < 1)
              (hgz ▸ hc)
          exact openCore_not_below n a (hF a haF) (f z) ho hz
        let K' : ContinuousMap.HomotopyRel g g' P := {
          toHomotopy := K.toHomotopy
          prop' := hKfix }
        let J := H.trans K'
        refine ⟨g', J, ?_, ?_⟩
        · intro z b hb
          rcases Finset.mem_insert.mp hb with rfl | hbA
          · exact hnew z
          · rcases hloc 1 z with heq | ⟨_,ho⟩
            · have hg : g' z = g z := by simpa using heq
              exact hg ▸ havoid z b hbA
            · have hab : a ≠ b := by
                intro heq
                exact ha (heq ▸ hbA)
              exact openCore_ne_other_center n a b (hF a haF)
                hab (g' z) (by simpa using ho)
        · intro t z
          rw [ContinuousMap.HomotopyRel.trans_apply]
          split_ifs
          · exact hsup _ z
          · change (K (_,z)).val ∈ finiteTopCellSupport n F
            rcases hloc _ z with heq | ⟨_,ho⟩
            · rw [heq]
              have hg : (g z).val ∈ finiteTopCellSupport n F := by
                simpa using hsup 1 z
              exact hg
            · exact openCore_mem_finiteSupport n F a haF _ ho
  exact hgo F (Finset.Subset.refl F)

end CurveComplexGenusTwo.CWHurewicz
