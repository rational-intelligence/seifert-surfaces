import CurveComplexGenusTwo.Topology.ActualFareyClassification.BigonEnlargedUniformSupport
import CurveComplexGenusTwo.Topology.BandGlobalGluing.ActualWholeWhiskerHalfCollarScaffold

open Set Topology Schoenflies unitInterval

/-- The actual parametrized line supplies a whole embedded whisker, including
its parametrization, rather than an assumed exterior access arc. -/
theorem actual_embedded_line_interval_path
    (G : C(ℝ,Plane)) (hG : Function.Injective G) (a b : ℝ) (hab : a≠b) :
    ∃ p : Path (G a) (G b), IsEmbedding p ∧
      (∀ t : I, p t=G (reparam a b t)) ∧ range p=G '' uIcc a b := by
  let p : Path (G a) (G b) :=
    { toFun := fun t => G (reparam a b t)
      continuous_toFun := G.continuous.comp (continuous_reparam.comp continuous_subtype_val)
      source' := by simp
      target' := by simp }
  have hp : Function.Injective p := by
    intro t u he
    apply Subtype.ext
    exact reparam_injective hab (hG he)
  refine ⟨p,(p.continuous.isClosedEmbedding hp).isEmbedding,fun _ => rfl,?_⟩
  rw [←image_reparam_I,image_image]
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,t.property,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨⟨t,ht⟩,rfl⟩

/-- Actual clean bigon contacts give both exterior endpoint whiskers. Their
only contacts with the entire closed disk are the respective old corners. -/
theorem clean_actual_bigon_endpoint_whiskers
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (r s a b : ℝ)
    (hrs : r<s) (har : a<r) (hsb : s<b) (L : Set Plane)
    (hGL : range G⊆L)
    (hJ : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (he : Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) L)
    (hcontact : segment ℝ (G r) (G s)∩L={G r,G s}) :
    ∃ p : Path (G r) (G a), ∃ q : Path (G s) (G b),
      IsEmbedding p ∧ IsEmbedding q ∧
      (∀ t : I, p t=G (reparam r a t)) ∧
      (∀ t : I, q t=G (reparam s b t)) ∧
      range p=G '' Icc a r ∧ range q=G '' Icc s b ∧
      range p∩closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))={G r} ∧
      range q∩closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))={G s} ∧
      Disjoint (range p) (range q) ∧
      (range p∪G '' Icc r s)∪range q=G '' Icc a b := by
  obtain ⟨p,hp,hpp,hpr⟩ := actual_embedded_line_interval_path G hG.injective r a har.ne'
  obtain ⟨q,hq,hqp,hqr⟩ := actual_embedded_line_interval_path G hG.injective s b hsb.ne
  rw [uIcc_of_ge har.le] at hpr
  rw [uIcc_of_le hsb.le] at hqr
  let K := closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
  have hKL : K∩L=G '' Icc r s :=
    clean_empty_bigon_closed_disk_family_contact G r s hrs L hGL hJ he hcontact
  have hcore : G '' Icc r s⊆K := by
    intro z hz
    exact (show z∈K∩L from hKL.symm ▸ hz).1
  refine ⟨p,q,hp,hq,hpp,hqp,hpr,hqr,?_,?_,?_,?_⟩
  · rw [hpr]
    apply subset_antisymm
    · rintro z ⟨⟨t,ht,rfl⟩,hzK⟩
      have hz : G t∈G '' Icc r s := hKL ▸ ⟨hzK,hGL (mem_range_self _)⟩
      obtain ⟨u,hu,heu⟩ := hz
      have hut := hG.injective heu
      have htr : t=r := by subst u; exact le_antisymm ht.2 hu.1
      simp [htr]
    · rintro z (rfl : z=G r)
      exact ⟨⟨r,⟨har.le,le_rfl⟩,rfl⟩,hcore ⟨r,⟨le_rfl,hrs.le⟩,rfl⟩⟩
  · rw [hqr]
    apply subset_antisymm
    · rintro z ⟨⟨t,ht,rfl⟩,hzK⟩
      have hz : G t∈G '' Icc r s := hKL ▸ ⟨hzK,hGL (mem_range_self _)⟩
      obtain ⟨u,hu,heu⟩ := hz
      have hut := hG.injective heu
      have hts : t=s := by subst u; exact le_antisymm hu.2 ht.1
      simp [hts]
    · rintro z (rfl : z=G s)
      exact ⟨⟨s,⟨le_rfl,hsb.le⟩,rfl⟩,hcore ⟨s,⟨hrs.le,le_rfl⟩,rfl⟩⟩
  · rw [hpr,hqr]
    apply disjoint_left.mpr
    rintro z ⟨t,ht,rfl⟩ ⟨u,hu,heq⟩
    have hut := hG.injective heq
    subst u
    linarith [ht.2,hu.1]
  · rw [hpr,hqr,←image_union,←image_union]
    congr 1
    ext t
    constructor
    · rintro ((ht|ht)|ht)
      · exact ⟨ht.1,ht.2.trans (hrs.le.trans hsb.le)⟩
      · exact ⟨har.le.trans ht.1,ht.2.trans hsb.le⟩
      · exact ⟨(har.le.trans hrs.le).trans ht.1,ht.2⟩
    · intro ht
      by_cases htr : t ≤ r
      · exact Or.inl (Or.inl ⟨ht.1,htr⟩)
      by_cases hts : t ≤ s
      · exact Or.inl (Or.inr ⟨(le_of_not_ge htr),hts⟩)
      · exact Or.inr ⟨le_of_not_ge hts,ht.2⟩

#print axioms actual_embedded_line_interval_path
#print axioms clean_actual_bigon_endpoint_whiskers
