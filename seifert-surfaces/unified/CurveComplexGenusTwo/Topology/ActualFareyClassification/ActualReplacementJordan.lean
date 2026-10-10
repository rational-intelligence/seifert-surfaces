import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualBigonWhiskers
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFullFarSideTarget

open Set Topology Schoenflies

/-- Last left contact and first right contact of the ACTUAL target segment
remove all unwanted endpoint-tail intersections. The resulting old/new arcs
form an actual Jordan curve and still contain the entire original bigon arc. -/
theorem actual_far_target_has_jordan_replacement_subarcs
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (a r s b : ℝ)
    (har : a<r) (hrs : r<s) (hsb : s<b)
    (hcore : Disjoint (G '' Icc r s) (segment ℝ (G a) (G b))) :
    ∃ u v : ℝ, a ≤ u ∧ u<r ∧ s<v ∧ v ≤ b ∧
      segment ℝ (G u) (G v)⊆segment ℝ (G a) (G b) ∧
      (G '' Icc u v)∩segment ℝ (G u) (G v)={G u,G v} ∧
      IsJordanCurve ((G '' Icc u v)∪segment ℝ (G u) (G v)) := by
  let B := segment ℝ (G a) (G b)
  let L := Icc a r∩G ⁻¹' B
  let R := Icc s b∩G ⁻¹' B
  have hB : IsClosed B := (isCompact_segment (G a) (G b)).isClosed
  have hpre : IsClosed (G ⁻¹' B) := hB.preimage G.continuous
  have hL : L.Nonempty := ⟨a,⟨le_rfl,har.le⟩,left_mem_segment ℝ _ _⟩
  have hR : R.Nonempty := ⟨b,⟨hsb.le,le_rfl⟩,right_mem_segment ℝ _ _⟩
  obtain ⟨u,hu,humax⟩ := (isCompact_Icc.inter_right hpre).exists_isGreatest hL
  obtain ⟨v,hv,hvmin⟩ := (isCompact_Icc.inter_right hpre).exists_isLeast hR
  have hur : u<r := by
    apply lt_of_le_of_ne hu.1.2
    intro he
    subst u
    exact disjoint_left.mp hcore ⟨r,⟨le_rfl,hrs.le⟩,rfl⟩ hu.2
  have hsv : s<v := by
    apply lt_of_le_of_ne hv.1.1
    intro he
    subst v
    exact disjoint_left.mp hcore ⟨s,⟨hrs.le,le_rfl⟩,rfl⟩ hv.2
  have huv : u<v := hur.trans (hrs.trans hsv)
  have htarget : segment ℝ (G u) (G v)⊆B := (convex_segment (G a) (G b)).segment_subset hu.2 hv.2
  have hno : ∀ t∈Ioo u v, G t∉B := by
    intro t ht htb
    by_cases htr : t ≤ r
    · have htL : t∈L := ⟨⟨hu.1.1.trans ht.1.le,htr⟩,htb⟩
      exact not_le_of_gt ht.1 (humax htL)
    by_cases hst : s ≤ t
    · have htR : t∈R := ⟨⟨hst,ht.2.le.trans hv.1.2⟩,htb⟩
      exact not_le_of_gt ht.2 (hvmin htR)
    · exact disjoint_left.mp hcore ⟨t,⟨(le_of_not_ge htr),(le_of_not_ge hst)⟩,rfl⟩ htb
  have hmeet : (G '' Icc u v)∩segment ℝ (G u) (G v)={G u,G v} := by
    apply subset_antisymm
    · rintro z ⟨⟨t,ht,rfl⟩,htB⟩
      by_cases htu : t=u
      · exact Or.inl (congrArg G htu)
      by_cases htv : t=v
      · exact Or.inr (congrArg G htv)
      exact False.elim (hno t ⟨lt_of_le_of_ne ht.1 (Ne.symm htu),lt_of_le_of_ne ht.2 htv⟩ (htarget htB))
    · intro z hz
      rcases hz with hz|hz
      · rw [hz]
        exact ⟨⟨u,⟨le_rfl,huv.le⟩,rfl⟩,left_mem_segment ℝ _ _⟩
      · have hz' : z=G v := hz
        rw [hz']
        exact ⟨⟨v,⟨huv.le,le_rfl⟩,rfl⟩,right_mem_segment ℝ _ _⟩
  have hne : G u≠G v := fun hh => huv.ne (hG.injective hh)
  have hsource := continuous_injective_interval_isArcBetween G hG.injective huv
  exact ⟨u,v,hu.1.1,hur,hsv,hv.1.2,htarget,hmeet,
    IsJordanCurve.of_two_arcs hsource (isArcBetween_segment hne).reverse
      (fun z hzA hzB => by
        have hz : z∈(G '' Icc u v)∩segment ℝ (G u) (G v) := ⟨hzA,hzB⟩
        rw [hmeet] at hz
        exact hz)⟩

#print axioms actual_far_target_has_jordan_replacement_subarcs
