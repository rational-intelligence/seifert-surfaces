import Section5ActualSurfaceProjectionV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
open SeifertSurfaces.Foundations
noncomputable section

/-- Local inverses of one actual surface projection glue to a single inverse
around the entire compact boundary circle. -/
theorem compact_surface_cylinder_inverse {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanHalfSpace 2) S] [IsManifold (𝓡∂ 2) ∞ S]
    (f : S → Circle × Time) (hf : ContMDiff (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) ∞ f)
    (beta : Circle → S) (hbeta : Continuous beta)
    (hzero : ∀ z, f (beta z) = (z,0))
    (hloc : ∀ z, IsLocalDiffeomorphAt (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) ∞ f (beta z)) :
    ∃ e : PartialDiffeomorph (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) S (Circle × Time) ∞,
      (e : S → Circle × Time) = f ∧ range beta ⊆ e.source ∧
      (∀ z, (z,0) ∈ e.target) ∧ (∀ z, e.symm (z,0) = beta z) := by
  classical
  letI : Nonempty S := ⟨beta 1⟩
  choose Phi hPhi hEq using hloc
  let O : Set S := ⋃ z, (Phi z).source
  have hO : IsOpen O := isOpen_iUnion fun z => (Phi z).open_source
  let K : Set S := range beta
  have hK : IsCompact K := isCompact_range hbeta
  have hKO : K ⊆ O := by
    rintro _ ⟨z,rfl⟩
    exact mem_iUnion.mpr ⟨z,hPhi z⟩
  have hlocalO : ∀ p ∈ O, IsLocalDiffeomorphAt (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) ∞ f p := by
    intro p hp
    obtain ⟨z,hz⟩ := mem_iUnion.mp hp
    exact ⟨Phi z,hz,hEq z⟩
  have hKinj : InjOn f K := by
    rintro _ ⟨z,rfl⟩ _ ⟨w,rfl⟩ hzw
    rw [hzero,hzero] at hzw
    exact congrArg beta (congrArg Prod.fst hzw)
  obtain ⟨T,hT,hKT,hTinj⟩ := hKinj.exists_isOpen_superset hK
    (fun p _ => hf.continuous.continuousAt) (by
      intro p hp
      obtain ⟨Phi',hpPhi',hEqPhi'⟩ := hlocalO p (hKO hp)
      refine ⟨Phi'.source,Phi'.open_source.mem_nhds hpPhi',?_⟩
      intro u hu v hv huv
      exact Phi'.toPartialEquiv.injOn hu hv
        ((hEqPhi' hu).symm.trans (huv.trans (hEqPhi' hv))))
  let R : Set S := T ∩ O
  have hR : IsOpen R := hT.inter hO
  have hKR : K ⊆ R := fun p hp => ⟨hKT hp,hKO hp⟩
  have hRinj : InjOn f R := hTinj.mono inter_subset_left
  have hlocalR : IsLocalDiffeomorphOn (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) ∞ f R := by
    rintro ⟨p,hp⟩
    exact hlocalO p hp.2
  have hopen : IsOpenMap (R.domRestrict f) := by
    intro W hW
    rw [Set.domRestrict_eq,Set.image_comp]
    let V : Set S := ((↑) : R → S) '' W
    have hV : IsOpen V := hR.isOpenMap_subtype_val W hW
    have hVR : V ⊆ R := by rintro _ ⟨p,hp,rfl⟩; exact p.2
    change IsOpen (f '' V)
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨p,hp,rfl⟩
    obtain ⟨Psi,hpPsi,hEqPsi⟩ := hlocalR ⟨p,hVR hp⟩
    refine ⟨Psi.toOpenPartialHomeomorph '' (V ∩ Psi.source),?_,?_,?_⟩
    · rintro _ ⟨q,hq,rfl⟩
      exact ⟨q,hq.1,hEqPsi hq.2⟩
    · exact Psi.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (hV.inter Psi.open_source) inter_subset_right
    · exact ⟨p,⟨hp,hpPsi⟩, (hEqPsi hpPsi).symm⟩
  let e : OpenPartialHomeomorph S (Circle × Time) :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hRinj.toPartialEquiv f R)
      (hf.continuous.continuousOn) hopen hR
  have he_coe : (e : S → Circle × Time) = f := rfl
  have he_source : e.source = R := rfl
  have he_smooth : ContMDiffOn ((𝓡 1).prod (𝓡∂ 1)) (𝓡∂ 2) ∞ e.symm e.target := by
    intro y hy
    let p : S := e.symm y
    have hp : p ∈ R := e.map_target hy
    obtain ⟨Psi,hpPsi,hEqPsi⟩ := hlocalR ⟨p,hp⟩
    have hpH : f p = y := e.right_inv hy
    have hyPsi : y ∈ Psi.target := by
      rw [← hpH,hEqPsi hpPsi]
      exact Psi.toPartialEquiv.map_source hpPsi
    have hPsiY : (Psi.symm : Circle × Time → S) y = p := by
      rw [← hpH,hEqPsi hpPsi]
      exact Psi.toPartialEquiv.left_inv hpPsi
    have hnear : e.symm =ᶠ[𝓝 y] (Psi.symm : Circle × Time → S) := by
      have hpre := (Psi.symm.contMDiffOn.continuousOn.continuousAt
        (Psi.open_target.mem_nhds hyPsi)).preimage_mem_nhds
          (by rw [hPsiY]; exact hR.mem_nhds hp)
      filter_upwards [Psi.open_target.mem_nhds hyPsi,hpre,e.open_target.mem_nhds hy]
        with y' hy'Psi hy'pre hy'e
      have hp'Psi : Psi.symm y' ∈ Psi.source := Psi.toPartialEquiv.map_target hy'Psi
      have hH' : f (Psi.symm y') = y' := by
        rw [hEqPsi hp'Psi]
        exact Psi.toPartialEquiv.right_inv hy'Psi
      apply e.injOn (e.map_target hy'e) hy'pre
      rw [e.right_inv hy'e,he_coe,hH']
    exact ((Psi.symm.contMDiffOn.contMDiffAt (Psi.open_target.mem_nhds hyPsi)).congr_of_eventuallyEq
      hnear).contMDiffWithinAt
  let E : PartialDiffeomorph (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1))
      S (Circle × Time) ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := hf.contMDiffOn
    contMDiffOn_invFun := he_smooth }
  refine ⟨E,rfl,hKR,?_,?_⟩
  · intro z
    have hz : beta z ∈ E.source := hKR (mem_range_self z)
    have he : E (beta z) = (z,0) := hzero z
    rw [← he]
    exact E.map_source hz
  · intro z
    have hz : beta z ∈ E.source := hKR (mem_range_self z)
    have he : E (beta z) = (z,0) := hzero z
    rw [← he]
    exact E.left_inv hz

#print axioms compact_surface_cylinder_inverse
end
end SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
