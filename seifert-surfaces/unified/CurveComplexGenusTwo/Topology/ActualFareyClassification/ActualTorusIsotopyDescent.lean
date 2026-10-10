import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedTerminalStripProducer
import CurveComplexGenusTwo.Topology.TorusDeckLift

open Set Topology Schoenflies CurveComplex

/-- Actual lattice-equivariant plane isotopies descend jointly continuously to
ambient isotopies of the standard torus. Marked fixing is retained literally. -/
theorem actual_lattice_isotopy_descends_to_marked_torus
    (H : AmbientIsotopy Plane)
    (heq : ∀ t (i : ℤ×ℤ) z,
      H.map (t,z+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)))=
      H.map (t,z)+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)))
    (p : Plane) (hfix : ∀ t, H.map (t,p)=p) :
    ∃ K : AmbientIsotopy (Circle×Circle),
      (∀ t z, K.map (t,(Circle.exp (z 0),Circle.exp (z 1)))=
        (Circle.exp (H.map (t,z) 0),Circle.exp (H.map (t,z) 1))) ∧
      (∀ t, K.map (t,(Circle.exp (p 0),Circle.exp (p 1)))=
        (Circle.exp (p 0),Circle.exp (p 1))) := by
  classical
  let q : C(Plane,Circle×Circle) :=
    ⟨fun z => (Circle.exp (z 0),Circle.exp (z 1)), by fun_prop⟩
  let e : Plane ≃ₜ ℝ×ℝ :=
    (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).trans Homeomorph.finTwoArrow
  have hqopen : IsOpenMap q :=
    (Circle.isCoveringMap_exp.isOpenMap.prodMap Circle.isCoveringMap_exp.isOpenMap).comp e.isOpenMap
  have hqsurj : Function.Surjective q := by
    rintro ⟨a,b⟩
    obtain ⟨x,hx⟩ := Circle.exp_surjective a
    obtain ⟨y,hy⟩ := Circle.exp_surjective b
    exact ⟨Plane.mk x y,Prod.ext hx hy⟩
  have hdeck (x y : Plane) (hxy : q x=q y) :
      ∃ i : ℤ×ℤ, x=y+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)) := by
    obtain ⟨a,ha⟩ := Circle.exp_eq_exp.mp (congrArg Prod.fst hxy)
    obtain ⟨b,hb⟩ := Circle.exp_eq_exp.mp (congrArg Prod.snd hxy)
    refine ⟨(a,b), ?_⟩
    ext k
    fin_cases k <;> assumption
  have hqdeck (i : ℤ×ℤ) (z : Plane) :
      q (z+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)))=q z := by
    simp [q,Plane.mk,Circle.exp_add]
  let Q : C(Interval×Plane,Interval×(Circle×Circle)) :=
    ⟨fun x => (x.1,q x.2), by fun_prop⟩
  have hid : IsOpenMap (id : Interval → Interval) := by
    intro U hU
    simpa using hU
  have hQ : IsQuotientMap Q :=
    (hid.prodMap hqopen).isQuotientMap Q.continuous
      (Function.surjective_id.prodMap hqsurj)
  let F : C(Interval×Plane,Circle×Circle) := q.comp H.map
  have hfactor : Function.FactorsThrough F Q := by
    rintro ⟨s,x⟩ ⟨t,y⟩ hxy
    have hst : s=t := congrArg Prod.fst hxy
    subst t
    obtain ⟨i,rfl⟩ := hdeck x y (congrArg Prod.snd hxy)
    change q (H.map (s,y+Plane.mk _ _))=q (H.map (s,y))
    rw [heq,hqdeck]
  let M : C(Interval×(Circle×Circle),Circle×Circle) := hQ.lift F hfactor
  have hM (t : Interval) (z : Plane) : M (t,q z)=q (H.map (t,z)) :=
    congrArg (fun f : C(Interval×Plane,Circle×Circle) => f (t,z)) (hQ.lift_comp F hfactor)
  have hbij (t : Interval) : Function.Bijective (fun z => M (t,z)) := by
    obtain ⟨h,hh⟩ := H.homeomorphism_at t
    constructor
    · intro a b hab
      obtain ⟨x,rfl⟩ := hqsurj a
      obtain ⟨y,rfl⟩ := hqsurj b
      change M (t,q x)=M (t,q y) at hab
      rw [hM,hM] at hab
      obtain ⟨i,hi⟩ := hdeck (H.map (t,x)) (H.map (t,y)) hab
      have hxy : x=y+Plane.mk ((i.1:ℝ)*(2*Real.pi)) ((i.2:ℝ)*(2*Real.pi)) := by
        apply h.injective
        rw [hh,hh,heq]
        exact hi
      rw [hxy,hqdeck]
    · intro a
      obtain ⟨x,rfl⟩ := hqsurj a
      refine ⟨q (h.symm x), ?_⟩
      change M (t,q (h.symm x))=q x
      rw [hM,← hh,h.apply_symm_apply]
  let K : AmbientIsotopy (Circle×Circle) := {
    map := M
    homeomorphism_at := by
      intro t
      have ht : Continuous (fun z => M (t,z)) := by fun_prop
      exact ⟨(Equiv.ofBijective _ (hbij t)).toHomeomorphOfContinuousClosed ht ht.isClosedMap,
        fun _ => rfl⟩
    at_zero := by
      intro a
      obtain ⟨x,rfl⟩ := hqsurj a
      rw [hM,H.at_zero] }
  refine ⟨K,?_,?_⟩
  · exact hM
  · intro t
    change M (t,q p)=q p
    rw [hM,hfix]

#print axioms actual_lattice_isotopy_descends_to_marked_torus
