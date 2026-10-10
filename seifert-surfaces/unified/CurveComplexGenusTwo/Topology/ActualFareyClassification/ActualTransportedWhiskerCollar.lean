import CurveComplexGenusTwo.Topology.ActualFareyClassification.MidpointJordanChart
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualBigonWhiskers

open Set Topology Schoenflies CurveComplex unitInterval

/-- Transport the actual exterior-whisker constructor through an exact old-disk
chart. Neither the half-collar nor its attachment port is supplied. -/
theorem actual_charted_exterior_whisker_half_collar
    (K : Set Plane) (F : Plane ≃ₜ Plane) (hFK : F '' K=Plane.closedSquare 0 1)
    (x y : Plane) (hx : F x=Plane.mk 1 0)
    (p : Path x y) (hp : IsEmbedding p) (hmeet : range p∩K={x})
    (U : Set Plane) (hU : IsOpen U) (hpU : range p⊆U) :
    ∃ rho : ℝ, 0<rho ∧ rho≤1 ∧ ∃ E : I×Icc (-1:ℝ) 1 → Plane,
      IsEmbedding E ∧
      (∀ w : Icc (-1:ℝ) 1, E (0,w)=F.symm (Plane.mk 1 (rho*w))) ∧
      (∀ t : I, E (t,⟨0,by norm_num⟩)=p t) ∧ range E⊆U ∧
      range E∩K=(fun w : Icc (-1:ℝ) 1 => F.symm (Plane.mk 1 (rho*w))) '' univ := by
  let q : Path (Plane.mk 1 0) (F y) := (p.map F.continuous).cast hx.symm rfl
  have hq (t : I) : q t=F (p t) := rfl
  have hqE : IsEmbedding q := F.isEmbedding.comp hp
  have hqmeet : range q∩Plane.closedSquare 0 1={Plane.mk 1 0} := by
    ext z
    constructor
    · rintro ⟨⟨t,rfl⟩,hz⟩
      rw [←hFK] at hz
      obtain ⟨w,hw,he⟩ := hz
      have hpt : p t∈K := F.injective (he.trans (hq t)).symm ▸ hw
      have hp0 : p t=x := by
        have hh : p t∈range p∩K := ⟨mem_range_self _,hpt⟩
        rw [hmeet] at hh
        exact hh
      simp [hq,hp0,hx]
    · rintro (rfl : z=Plane.mk 1 0)
      refine ⟨⟨0,by simp [hq,hx]⟩,?_⟩
      rw [mem_closedSquare_zero_one]
      norm_num [Plane.supNorm,Plane.mk]
  have hqU : range q⊆F '' U := by
    rintro z ⟨t,rfl⟩
    exact ⟨p t,hpU (mem_range_self _),hq t |>.symm⟩
  obtain ⟨rho,hrho,hrho1,B,hB,hport,hcenter,hBU,hBK⟩ :=
    actual_whole_exterior_whisker_half_collar q hqE hqmeet (F '' U) (F.isOpenMap _ hU) hqU
  let E := F.symm ∘ B
  refine ⟨rho,hrho,hrho1,E,F.symm.isEmbedding.comp hB,?_,?_,?_,?_⟩
  · intro w; change F.symm (B (0,w))=_; rw [hport]
  · intro t; change F.symm (B _)=p t; rw [hcenter,hq,F.symm_apply_apply]
  · rintro z ⟨w,rfl⟩
    obtain ⟨v,hv,he⟩ := hBU (mem_range_self w)
    change F.symm (B w)∈U
    rw [←he,F.symm_apply_apply]
    exact hv
  · ext z
    constructor
    · rintro ⟨⟨w,rfl⟩,hzK⟩
      have hz : B w∈range B∩Plane.closedSquare 0 1 := by
        refine ⟨mem_range_self _,?_⟩
        rw [←hFK]
        exact ⟨F.symm (B w),hzK,F.apply_symm_apply _⟩
      rw [hBK] at hz
      obtain ⟨v,_,hv⟩ := hz
      exact ⟨v,trivial,congrArg F.symm hv⟩
    · rintro ⟨w,_,rfl⟩
      refine ⟨⟨(0,w),by change F.symm (B (0,w))=_; rw [hport]⟩,?_⟩
      have hzQ : Plane.mk 1 (rho*w)∈Plane.closedSquare 0 1 := by
        rw [mem_closedSquare_zero_one]
        change max |(1:ℝ)| |rho*(w:ℝ)|≤1
        rw [abs_one,abs_mul,abs_of_pos hrho]
        exact max_le le_rfl ((mul_le_mul_of_nonneg_left (abs_le.mpr w.property) hrho.le).trans (by simpa using hrho1))
      rw [←hFK] at hzQ
      obtain ⟨v,hv,he⟩ := hzQ
      change F.symm (Plane.mk 1 (rho*w))∈K
      rwa [←he,F.symm_apply_apply]

#print axioms actual_charted_exterior_whisker_half_collar
