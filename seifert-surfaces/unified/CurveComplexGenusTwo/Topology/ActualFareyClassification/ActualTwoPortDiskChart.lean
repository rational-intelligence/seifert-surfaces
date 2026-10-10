import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualRectangularPortGluing

open Set Topology Schoenflies CurveComplex unitInterval

/-- Glue the two constructed half-collars to the actual old disk, then extend
its actual embedded closed-square parametrization over the whole plane. -/
theorem actual_two_attached_half_collars_disk_chart
    (K : Set Plane) (F : Plane ≃ₜ Plane) (hFK : F '' K=Plane.closedSquare 0 1)
    (rho sigma : ℝ) (hrho : 0<rho) (hrho1 : rho ≤ 1) (hsigma : 0<sigma) (hsigma1 : sigma ≤ 1)
    (E Q : I×Icc (-1:ℝ) 1→Plane) (hE : IsEmbedding E) (hQ : IsEmbedding Q)
    (hEQ : Disjoint (range E) (range Q))
    (hEport : ∀ w : Icc (-1:ℝ) 1, E (0,w)=F.symm (Plane.mk 1 (rho*w)))
    (hQport : ∀ w : Icc (-1:ℝ) 1, Q (0,w)=F.symm (Plane.mk (-1) (-sigma*w)))
    (hEK : range E∩K=(fun w : Icc (-1:ℝ) 1 => F.symm (Plane.mk 1 (rho*w))) '' univ)
    (hQK : range Q∩K=(fun w : Icc (-1:ℝ) 1 => F.symm (Plane.mk (-1) (-sigma*w))) '' univ) :
    ∃ Phi : Plane ≃ₜ Plane, Phi '' Plane.closedSquare 0 1=(K∪range E)∪range Q := by
  let D := Plane.closedSquare 0 1
  let R := {z : Plane | 1 ≤ z 0 ∧ z 0 ≤ 2 ∧ |z 1| ≤ rho}
  let L := {z : Plane | -2 ≤ z 0 ∧ z 0 ≤  -1 ∧ |z 1| ≤ sigma}
  have h0 : IsHomeoOn F.symm F D K := {
    mapsTo := by
      intro z hz
      change z∈Plane.closedSquare 0 1 at hz
      rw [←hFK] at hz
      obtain ⟨x,hx,he⟩ := hz
      rwa [←he,F.symm_apply_apply]
    mapsTo_inv := by
      intro z hz
      change F z∈Plane.closedSquare 0 1
      exact hFK ▸ mem_image_of_mem F hz
    continuousOn := F.symm.continuous.continuousOn
    continuousOn_inv := F.continuous.continuousOn
    invOn := ⟨fun z _ => F.apply_symm_apply z,fun z _ => F.symm_apply_apply z⟩ }
  have hK : IsClosed K := by
    rw [←h0.image_eq]
    exact ((isCompact_closedSquare 0 1).image F.symm.continuous).isClosed
  have hR : IsClosed R := by
    change IsClosed ({z : Plane | 1 ≤ z 0}∩({z : Plane | z 0 ≤ 2}∩{z : Plane | |z 1| ≤ rho}))
    exact
    (isClosed_le continuous_const (show Continuous (fun z : Plane => z 0) by fun_prop)).inter
      ((isClosed_le (show Continuous (fun z : Plane => z 0) by fun_prop) continuous_const).inter (isClosed_le (show Continuous (fun z : Plane => |z 1|) by fun_prop) continuous_const))
  have hL : IsClosed L := by
    change IsClosed ({z : Plane | -2 ≤ z 0}∩({z : Plane | z 0 ≤ -1}∩{z : Plane | |z 1| ≤ sigma}))
    exact
    (isClosed_le continuous_const (show Continuous (fun z : Plane => z 0) by fun_prop)).inter
      ((isClosed_le (show Continuous (fun z : Plane => z 0) by fun_prop) continuous_const).inter (isClosed_le (show Continuous (fun z : Plane => |z 1|) by fun_prop) continuous_const))
  obtain ⟨fR,gR,hfgR,hagreeR,himageR⟩ := actual_rectangular_port_restricted_homeomorphism
    K F hFK rho 1 hrho hrho1 (Or.inl rfl) E hE (by simpa using hEport) (by simpa using hEK)
  simp only [one_mul] at hfgR hagreeR himageR
  change IsHomeoOn fR gR R (range E) at hfgR
  change (∀ z∈D∩R, fR z=F.symm z) at hagreeR
  change F.symm '' (D∩R)=K∩range E at himageR
  obtain ⟨fL,gL,hfgL,hagreeL,himageL⟩ := actual_rectangular_port_restricted_homeomorphism
    K F hFK sigma (-1) hsigma hsigma1 (Or.inr rfl) Q hQ (by simpa using hQport) (by simpa using hQK)
  have hLset : {z : Plane | 1 ≤ (-1:ℝ)*z 0 ∧ (-1:ℝ)*z 0 ≤ 2 ∧ |z 1| ≤ sigma}=L := by
    ext z
    dsimp [L]
    constructor
    · intro hz; exact ⟨by linarith [hz.2.1],by linarith [hz.1],hz.2.2⟩
    · intro hz; exact ⟨by linarith [hz.2.1],by linarith [hz.1],hz.2.2⟩
  rw [hLset] at hfgL hagreeL himageL
  obtain ⟨f,g,hfg,hfD,hfR⟩ := glue_closed_homeoOn (Plane.isClosed_closedSquare 0 1) hR hK
    (isCompact_range hE.continuous).isClosed h0 hfgR (fun z hz => (hagreeR z hz).symm) himageR
  have hRL : Disjoint R L := by
    apply disjoint_left.mpr
    intro z hzR hzL
    linarith [hzR.1,hzL.2.1]
  have hOverlap : (D∪R)∩L=D∩L := by
    ext z
    constructor
    · rintro ⟨hz,hzL⟩
      rcases hz with hzD|hzR
      · exact ⟨hzD,hzL⟩
      · exact False.elim (disjoint_left.mp hRL hzR hzL)
    · rintro ⟨hzD,hzL⟩; exact ⟨Or.inl hzD,hzL⟩
  have hTarOverlap : (K∪range E)∩range Q=K∩range Q := by
    ext z
    constructor
    · rintro ⟨hz,hzQ⟩
      rcases hz with hzK|hzE
      · exact ⟨hzK,hzQ⟩
      · exact False.elim (disjoint_left.mp hEQ hzE hzQ)
    · rintro ⟨hzK,hzQ⟩; exact ⟨Or.inl hzK,hzQ⟩
  have hagree : ∀ z∈(D∪R)∩L, f z=fL z := by
    intro z hz
    rw [hOverlap] at hz
    exact (hfD z hz.1).trans (hagreeL z hz).symm
  have himage : f '' ((D∪R)∩L)=(K∪range E)∩range Q := by
    rw [hOverlap,hTarOverlap,←himageL]
    apply image_congr
    intro z hz
    exact hfD z hz.1
  obtain ⟨f0,g0,hfg0,_,_⟩ := glue_closed_homeoOn ((Plane.isClosed_closedSquare 0 1).union hR) hL
    (hK.union (isCompact_range hE.continuous).isClosed) (isCompact_range hQ.continuous).isClosed
    hfg hfgL hagree himage
  obtain ⟨H,hH⟩ := square_with_two_ports_radial_model rho sigma hrho hrho1 hsigma hsigma1
  change H '' D=(D∪R)∪L at hH
  let e : ↥D→Plane := fun z => f0 (H z)
  have hec : Continuous e := hfg0.continuousOn.comp_continuous
    (H.continuous.comp continuous_subtype_val) (fun z => hH ▸ mem_image_of_mem H z.property)
  have hei : Function.Injective e := by
    intro z w he
    apply Subtype.ext
    apply H.injective
    exact hfg0.injOn (hH ▸ mem_image_of_mem H z.property) (hH ▸ mem_image_of_mem H w.property) he
  have he : IsEmbedding e := by
    let : CompactSpace ↥D := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
    exact (hec.isClosedEmbedding hei).isEmbedding
  obtain ⟨Phi,hPhi⟩ := exists_ambient_extension_of_embedded_closed_square e he
  refine ⟨Phi,?_⟩
  calc
    Phi '' D=range e := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩; exact ⟨⟨x,hx⟩,(hPhi ⟨x,hx⟩).symm⟩
      · rintro ⟨x,rfl⟩; exact ⟨x,x.property,hPhi x⟩
    _=f0 '' ((D∪R)∪L) := by
      rw [←hH]
      ext z
      constructor
      · rintro ⟨x,rfl⟩; exact ⟨H x,mem_image_of_mem H x.property,rfl⟩
      · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
    _=(K∪range E)∪range Q := hfg0.image_eq

#print axioms actual_two_attached_half_collars_disk_chart
