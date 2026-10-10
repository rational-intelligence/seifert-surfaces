import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualBigonWhiskers

open Set Topology Schoenflies Metric unitInterval

/-- Openness chooses actual short exterior whiskers inside the prescribed
whole-bigonic operation neighborhood; no whisker or access certificate is input. -/
theorem clean_bigon_open_neighborhood_has_short_actual_whiskers
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s : ℝ)
    (hrs : r<s) (hshort : s-r<T) (L : Set Plane) (hGL : range G⊆L)
    (hJ : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (he : Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) L)
    (hcontact : segment ℝ (G r) (G s)∩L={G r,G s})
    (U : Set Plane) (hU : IsOpen U)
    (hKU : closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))⊆U) :
    ∃ a b : ℝ, a<r ∧ s<b ∧ b-a<T ∧
    ∃ p : Path (G r) (G a), ∃ q : Path (G s) (G b),
      IsEmbedding p ∧ IsEmbedding q ∧
      range p=G '' Icc a r ∧ range q=G '' Icc s b ∧
      range p⊆U ∧ range q⊆U ∧
      range p∩closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))={G r} ∧
      range q∩closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))={G s} ∧
      Disjoint (range p) (range q) ∧ G '' Icc a b⊆U := by
  let K := closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
  have hKL : K∩L=G '' Icc r s :=
    clean_empty_bigon_closed_disk_family_contact G r s hrs L hGL hJ he hcontact
  have hcore : G '' Icc r s⊆U := by
    intro z hz
    exact hKU (show z∈K from (show z∈K∩L from hKL.symm ▸ hz).1)
  have hrU : G r∈U := hcore ⟨r,⟨le_rfl,hrs.le⟩,rfl⟩
  have hsU : G s∈U := hcore ⟨s,⟨hrs.le,le_rfl⟩,rfl⟩
  obtain ⟨er,her,hbr⟩ := Metric.mem_nhds_iff.mp
    ((hU.preimage G.continuous).mem_nhds hrU)
  obtain ⟨es,hes,hbs⟩ := Metric.mem_nhds_iff.mp
    ((hU.preimage G.continuous).mem_nhds hsU)
  let d := min (er/2) (min (es/2) ((T-(s-r))/4))
  have hd : 0<d := by dsimp [d]; positivity
  have hdr : d<er := by
    have hh := min_le_left (er/2) (min (es/2) ((T-(s-r))/4))
    dsimp [d]; linarith
  have hds : d<es := by
    have hh := (min_le_right (er/2) (min (es/2) ((T-(s-r))/4))).trans
      (min_le_left (es/2) ((T-(s-r))/4))
    dsimp [d]; linarith
  have hdT : d ≤ (T-(s-r))/4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let a := r-d
  let b := s+d
  have har : a<r := by dsimp [a]; linarith
  have hsb : s<b := by dsimp [b]; linarith
  have hba : b-a<T := by dsimp [a,b]; linarith
  have hleft : G '' Icc a r⊆U := by
    rintro z ⟨t,ht,rfl⟩
    apply hbr
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [a] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hright : G '' Icc s b⊆U := by
    rintro z ⟨t,ht,rfl⟩
    apply hbs
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [b] at ht
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨p,q,hp,hq,_,_,hpr,hqr,hpK,hqK,hpq,hfull⟩ :=
    clean_actual_bigon_endpoint_whiskers G hG r s a b hrs har hsb L hGL hJ he hcontact
  refine ⟨a,b,har,hsb,hba,p,q,hp,hq,hpr,hqr,hpr.symm ▸ hleft,hqr.symm ▸ hright,
    hpK,hqK,hpq,?_⟩
  rw [←hfull]
  rintro z ((hz|hz)|hz)
  · exact hleft (hpr ▸ hz)
  · exact hcore hz
  · exact hright (hqr ▸ hz)

#print axioms clean_bigon_open_neighborhood_has_short_actual_whiskers
