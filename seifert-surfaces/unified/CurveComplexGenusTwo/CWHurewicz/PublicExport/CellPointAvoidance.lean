import CurveComplexGenusTwo.CWHurewicz.PublicExport.CenterAvoidance
import CurveComplexGenusTwo.CWHurewicz.PublicExport.CellCoreTopology

namespace CurveComplexGenusTwo.CWHurewicz
open Topology Metric Set
open scoped unitInterval

private theorem glueTwoOpen {D Y : Type*} [TopologicalSpace D] [TopologicalSpace Y]
    (U V : Set D) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (f : C(U,Y)) (g : C(V,Y))
    (hfg : ∀ x (hu : x ∈ U) (hv : x ∈ V), f ⟨x,hu⟩ = g ⟨x,hv⟩) :
    ∃ h : C(D,Y), (∀ x : U, h x.val = f x) ∧ (∀ x : V, h x.val = g x) := by
  let pieces : Bool → Set D := fun b => cond b U V
  let maps : ∀ b, C(pieces b,Y) := fun b => by cases b; exact g; exact f
  have hc : ∀ b c x (hb : x ∈ pieces b) (hc : x ∈ pieces c),
      maps b ⟨x,hb⟩ = maps c ⟨x,hc⟩ := by
    intro b c x hb hc
    cases b <;> cases c
    · rfl
    · exact (hfg x hc hb).symm
    · exact hfg x hb hc
    · rfl
  have hn : ∀ x : D, ∃ b, pieces b ∈ nhds x := by
    intro x
    have hx : x ∈ U ∪ V := hcover.symm ▸ mem_univ x
    rcases hx with hx | hx
    · exact ⟨true,hU.mem_nhds hx⟩
    · exact ⟨false,hV.mem_nhds hx⟩
  refine ⟨ContinuousMap.liftCover pieces maps hc hn, ?_, ?_⟩
  · intro x
    exact ContinuousMap.liftCover_coe (S := pieces) (φ := maps) (hφ := hc) (hS := hn) (i := true) x
  · intro x
    exact ContinuousMap.liftCover_coe (S := pieces) (φ := maps) (hφ := hc) (hS := hn) (i := false) x

/-- A genuine center-avoidance homotopy for a map that can cross arbitrary
CW cell boundaries. The only dimension assumption is k < n. The map is
unchanged off the inner half-core of the selected top cell. -/
theorem oneCellPointAvoidance
    {X : Type} [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)] [T2Space X]
    {S : Type*} [TopologicalSpace S] {k n : ℕ}
    (e : S → (Fin k → ℝ)) (he : IsClosedEmbedding e) (hkn : k < n)
    (a : StageCellIndex X n) (ha : a.1.val = n)
    (f : C(S, ↥(skeletonBelow X (n+1)))) :
    ∃ g : C(S, ↥(skeletonBelow X (n+1))),
      ∃ H : ContinuousMap.HomotopyRel f g
        {z | f z ∉ stageClosedCore n a (1/2)},
        (∀ z, g z ≠ stageCellCenter n a) ∧
        ∀ t z, H (t,z) = f z ∨
          (f z ∈ stageOpenCore n a 1 ∧ H (t,z) ∈ stageOpenCore n a 1) := by
  let K : Set S := f ⁻¹' stageClosedCore n a (3/4)
  let U : Set S := f ⁻¹' stageOpenCore n a (3/4)
  let V : Set S := (f ⁻¹' stageClosedCore n a (1/2))ᶜ
  have hK : IsClosed K := (stageClosedCore_isClosed n a (3/4) (by norm_num)).preimage f.continuous
  have hU : IsOpen U := (stageOpenCore_isOpen n a ha (3/4) (by norm_num)).preimage f.continuous
  have hV : IsOpen V := ((stageClosedCore_isClosed n a (1/2) (by norm_num)).preimage f.continuous).isOpen_compl
  have hUK : U ⊆ K := fun _ hz => stageOpenCore_subset_closed n a le_rfl hz
  have hcov : U ∪ V = univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases hz : z ∈ V
    · exact Or.inr hz
    · exact Or.inl (stageClosedCore_subset_open n a (by norm_num : (1:ℝ)/2 < 3/4)
        (by simpa [V] using hz))
  let c : C(K, Fin a.1.val → ℝ) :=
    (stageCoreCoordinate n a (3/4) (by norm_num)).comp
      ⟨fun z => ⟨f z.val,z.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hc (z : K) : ‖c z‖ ≤ 3/4 := stageCoreCoordinate_norm_le n a (3/4) (by norm_num) _
  have hci (z : K) : Topology.CWComplex.map a.1.val a.2 (c z) = (f z.val).val :=
    stageCoreCoordinate_inverse n a (3/4) (by norm_num) _
  obtain ⟨v,hvn,hvd,hvf⟩ := closedEmbedding_centerAvoidance (show k < a.1.val by omega)
    (fun z : K => e z.val) (he.comp hK.isClosedEmbedding_subtypeVal) c
  have hvball (z : K) : ‖v z‖ < 1 := by
    have hd : ‖v z-c z‖ < 1/8 := by simpa only [dist_eq_norm] using hvd z
    have hnorm := norm_add_le (v z-c z) (c z)
    rw [sub_add_cancel] at hnorm
    have := hc z
    linarith
  let ku : C(U,K) := ⟨fun z => ⟨z.val,hUK z.property⟩, continuous_subtype_val.subtype_mk _⟩
  let coord : C(I × U, Fin a.1.val → ℝ) :=
    ⟨fun p => (1-(p.1 : ℝ)) • c (ku p.2) + (p.1 : ℝ) • v (ku p.2), by fun_prop⟩
  have hb (p : I × U) : coord p ∈ ball (0 : Fin a.1.val → ℝ) 1 := by
    apply (convex_ball (0 : Fin a.1.val → ℝ) (1 : ℝ))
    · rw [mem_ball,dist_zero_right]
      exact (hc (ku p.2)).trans_lt (by norm_num)
    · simpa only [mem_ball,dist_zero_right] using hvball (ku p.2)
    · exact sub_nonneg.mpr p.1.property.2
    · exact p.1.property.1
    · ring
  let L : C(I × U, ↥(skeletonBelow X (n+1))) :=
    (characteristicToLaterStep n a.1.val (by omega) a.2).comp
      ⟨fun p => ⟨coord p,ball_subset_closedBall (hb p)⟩, coord.continuous.subtype_mk _⟩
  have hLzero (z : U) : L (0,z) = f z.val := by
    apply Subtype.ext
    change Topology.CWComplex.map a.1.val a.2 (coord (0,z)) = _
    have hco : coord (0,z) = c (ku z) := by simp [coord]
    rw [hco]
    exact hci (ku z)
  have hLfix (t : I) (z : U) (hzV : z.val ∈ V) : L (t,z) = f z.val := by
    have hcn : 1/2 ≤ ‖c (ku z)‖ := by
      by_contra h
      apply hzV
      exact ⟨c (ku z), by rw [mem_closedBall,dist_zero_right]; exact (lt_of_not_ge h).le,
        hci (ku z)⟩
    apply Subtype.ext
    change Topology.CWComplex.map a.1.val a.2 (coord (t,z)) = _
    have hco : coord (t,z) = c (ku z) := by
      change (1-(t : ℝ)) • c (ku z) + (t : ℝ) • v (ku z) = c (ku z)
      rw [hvf (ku z) hcn, ← add_smul]
      simp
    rw [hco]
    exact hci (ku z)
  let Ut : Set (I × S) := Prod.snd ⁻¹' U
  let Vt : Set (I × S) := Prod.snd ⁻¹' V
  let Lu : C(Ut, ↥(skeletonBelow X (n+1))) :=
    L.comp ⟨fun p => (p.val.1,⟨p.val.2,p.property⟩), by fun_prop⟩
  let Rv : C(Vt, ↥(skeletonBelow X (n+1))) :=
    f.comp ⟨fun p => p.val.2, continuous_snd.comp continuous_subtype_val⟩
  obtain ⟨Hc,hHu,hHv⟩ := glueTwoOpen Ut Vt (hU.preimage continuous_snd)
    (hV.preimage continuous_snd) (by
      change Prod.snd ⁻¹' U ∪ Prod.snd ⁻¹' V = univ
      rw [← preimage_union,hcov,preimage_univ]) Lu Rv
    (fun p hp hq => hLfix p.1 ⟨p.2,hp⟩ hq)
  have hHu' (t : I) (z : S) (hz : z ∈ U) : Hc (t,z) = L (t,⟨z,hz⟩) :=
    hHu ⟨(t,z),hz⟩
  have hHv' (t : I) (z : S) (hz : z ∈ V) : Hc (t,z) = f z := hHv ⟨(t,z),hz⟩
  have hH0 (z : S) : Hc (0,z) = f z := by
    have hz : z ∈ U ∪ V := hcov.symm ▸ mem_univ z
    rcases hz with hz | hz
    · rw [hHu' 0 z hz]
      exact hLzero ⟨z,hz⟩
    · exact hHv' 0 z hz
  let g : C(S, ↥(skeletonBelow X (n+1))) := Hc.comp ⟨fun z => (1,z), by fun_prop⟩
  let H : ContinuousMap.HomotopyRel f g V := {
    toContinuousMap := Hc
    map_zero_left := hH0
    map_one_left := fun _ => rfl
    prop' := hHv' }
  refine ⟨g,H,?_,?_⟩
  · intro z hgz
    by_cases hz : z ∈ U
    · have hval := congrArg Subtype.val hgz
      change (Hc (1,z)).val = _ at hval
      rw [hHu' 1 z hz] at hval
      have hcoord : coord (1,⟨z,hz⟩) = v (ku ⟨z,hz⟩) := by simp [coord]
      change Topology.CWComplex.map a.1.val a.2 (coord (1,⟨z,hz⟩)) =
        Topology.CWComplex.map a.1.val a.2 0 at hval
      rw [hcoord] at hval
      apply hvn (ku ⟨z,hz⟩)
      apply (Topology.CWComplex.map a.1.val a.2).injOn
      · rw [Topology.CWComplex.source_eq,mem_ball,dist_zero_right]
        exact hvball _
      · rw [Topology.CWComplex.source_eq]; simp
      · exact hval
    · have hzV : z ∈ V := (hcov.symm ▸ mem_univ z : z ∈ U ∪ V).resolve_left hz
      have hgz' : g z = f z := hHv' 1 z hzV
      have hzcenter : f z ≠ (stageCellCenter n a).val := by
        intro hh
        apply hzV
        exact ⟨0, by simp, hh.symm⟩
      exact hzcenter (congrArg Subtype.val (hgz'.symm.trans hgz))
  · intro t z
    by_cases hz : z ∈ U
    · right
      constructor
      · exact stageClosedCore_subset_open n a (by norm_num : (3:ℝ)/4 < 1) (hUK hz)
      · change Hc (t,z) ∈ _
        rw [hHu' t z hz]
        exact ⟨coord (t,⟨z,hz⟩),hb _,rfl⟩
    · exact Or.inl (hHv' t z ((hcov.symm ▸ mem_univ z : z ∈ U ∪ V).resolve_left hz))

end CurveComplexGenusTwo.CWHurewicz
