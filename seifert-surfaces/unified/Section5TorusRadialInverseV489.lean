import Section5PolarDistanceV489

noncomputable section
open Set Topology Function Filter Manifold
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem torus_smooth_local_inverse_v489
    {f : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)}
    (hf : ContMDiff (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) ∞ f)
    {x : ℝ × (Circle × Circle)}
    (hinv : (mfderiv (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) f x).IsInvertible) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) ∞ f x := by
  obtain ⟨Phi,hxPhi,hEqPhi⟩ :=
    DifferentialGeometry.Coordinates.contMDiffAt_isLocalDiffeomorphAt_of_mfderiv
      (n := 1) le_rfl (by exact_mod_cast (WithTop.one_ne_top : (1 : ℕ∞) ≠ ⊤))
      (hf.contMDiffAt.of_le (by exact_mod_cast le_top)) hinv
  have hInvPhi : ∀ z ∈ Phi.source,
      (mfderiv (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) f z).IsInvertible := by
    intro z hz
    exact (show IsLocalDiffeomorphAt (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 1 f z from
      ⟨Phi,hz,hEqPhi⟩).isInvertible_mfderiv (by norm_num)
  have hs : ContMDiffOn (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) ∞
      (Phi.symm : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) Phi.target := by
    rw [contMDiffOn_infty]
    intro k y hy
    let z : ℝ × (Circle × Circle) := Phi.symm y
    have hz : z ∈ Phi.source := Phi.toPartialEquiv.map_target hy
    have hfz : f z = y := by
      rw [hEqPhi hz]
      exact Phi.toPartialEquiv.right_inv hy
    obtain ⟨Psi,hzPsi,hEqPsi⟩ :=
      DifferentialGeometry.Coordinates.contMDiffAt_isLocalDiffeomorphAt_of_mfderiv
        (n := ((max 1 k : ℕ) : ℕ∞ω)) (by exact_mod_cast le_max_left 1 k)
        (by exact_mod_cast ENat.natCast_ne_top (max 1 k))
        (hf.contMDiffAt.of_le (by exact_mod_cast le_top)) (hInvPhi z hz)
    have hyPsi : y ∈ Psi.target := by
      rw [← hfz,hEqPsi hzPsi]
      exact Psi.toPartialEquiv.map_source hzPsi
    have hPsiY : (Psi.symm : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) y = z := by
      rw [← hfz,hEqPsi hzPsi]
      exact Psi.toPartialEquiv.left_inv hzPsi
    have hnear : (Phi.symm : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) =ᶠ[𝓝 y] Psi.symm := by
      have hpre := (Psi.symm.contMDiffOn.continuousOn.continuousAt
        (Psi.open_target.mem_nhds hyPsi)).preimage_mem_nhds
          (by rw [hPsiY]; exact Phi.open_source.mem_nhds hz)
      filter_upwards [Psi.open_target.mem_nhds hyPsi,hpre,Phi.open_target.mem_nhds hy]
        with y' hy'Psi hy'pre hy'Phi
      have hz'Psi : Psi.symm y' ∈ Psi.source := Psi.toPartialEquiv.map_target hy'Psi
      have hfPsi : f (Psi.symm y') = y' := by
        rw [hEqPsi hz'Psi]
        exact Psi.toPartialEquiv.right_inv hy'Psi
      apply Phi.toPartialEquiv.injOn (Phi.toPartialEquiv.map_target hy'Phi) hy'pre
      rw [Phi.toPartialEquiv.right_inv hy'Phi,← hEqPhi hy'pre,hfPsi]
    have hPsi : ContMDiffAt (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (k : ℕ∞ω)
        (Psi.symm : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) y :=
      (Psi.symm.contMDiffOn.contMDiffAt (Psi.open_target.mem_nhds hyPsi)).of_le
        (by exact_mod_cast le_max_right 1 k)
    exact (hPsi.congr_of_eventuallyEq hnear).contMDiffWithinAt
  refine ⟨{ toPartialEquiv := Phi.toPartialEquiv
            open_source := Phi.open_source
            open_target := Phi.open_target
            contMDiffOn_toFun := hf.contMDiffOn.congr (fun z hz => (hEqPhi hz).symm)
            contMDiffOn_invFun := hs },hxPhi,hEqPhi⟩

/-- Injective finite rank of the radial-time map at the whole initial torus. -/
theorem torus_radial_graph_rank_v489 (f : ℝ × (Circle × Circle) → ℝ)
    (hf : ContMDiff (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) ∞ f)
    (htrans : ∀ z, mfderiv (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) f (0,z) (1,0) ≠ 0)
    (z : (Circle × Circle)) :
    (mfderiv (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1)))
      (fun q : ℝ × (Circle × Circle) => (f q,q.2)) (0,z)).IsInvertible := by
  let D : (ℝ × (Euc 1 × Euc 1)) →L[ℝ] (ℝ × (Euc 1 × Euc 1)) :=
    mfderiv (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1)))
      (fun q : ℝ × (Circle × Circle) => (f q,q.2)) (0,z)
  let d : (ℝ × (Euc 1 × Euc 1)) →L[ℝ] ℝ := mfderiv (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) f (0,z)
  have hD : D = d.prod
      (ContinuousLinearMap.snd ℝ ℝ (Euc 1 × Euc 1)) := by
    have he := mfderiv_prodMk (hf.mdifferentiableAt (x := (0,z)) (by simp))
      (mdifferentiableAt_snd (x := (0,z)))
    rw [mfderiv_snd] at he
    exact he
  have hi : Injective D := by
    intro u v huv
    have hw : u.2 = v.2 := by
      have h := congrArg Prod.snd huv
      rw [hD] at h
      exact h
    have hsub : D (u-v) = 0 := by rw [map_sub,huv,sub_self]
    have hd : u-v = (u.1-v.1) • ((1 : ℝ),(0 : Euc 1 × Euc 1)) := by ext <;> simp [hw]
    have hs : (u.1-v.1) * d (1,0) = 0 := by
      have h := congrArg Prod.fst hsub
      rw [hd,map_smul,hD] at h
      exact h
    have hfirst : u.1 = v.1 := sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right (htrans z))
    exact Prod.ext hfirst hw
  let e : (ℝ × (Euc 1 × Euc 1)) ≃ₗ[ℝ] (ℝ × (Euc 1 × Euc 1)) := D.toLinearMap.linearEquivOfInjective hi rfl
  let eL : (ℝ × (Euc 1 × Euc 1)) ≃L[ℝ] (ℝ × (Euc 1 × Euc 1)) := {
    toLinearEquiv := e
    continuous_toFun := D.continuous
    continuous_invFun := e.symm.toLinearMap.continuous_of_finiteDimensional }
  exact ⟨eL,rfl⟩

/-- The local smooth inverses glue around the entire compact initial torus,
with the radial map itself as the literal forward function. -/
theorem torus_radial_compact_partialDiffeomorph_v489 (f : ℝ × (Circle × Circle) → ℝ)
    (hf : ContMDiff (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) ∞ f)
    (hzero : ∀ z, f (0,z) = 0)
    (htrans : ∀ z, mfderiv (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) f (0,z) (1,0) ≠ 0) :
    ∃ e : PartialDiffeomorph (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1)))
        (ℝ × (Circle × Circle)) (ℝ × (Circle × Circle)) ∞,
      (e : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) = (fun q => (f q,q.2)) ∧
      ({0} ×ˢ (univ : Set (Circle × Circle))) ⊆ e.source ∧
      ({0} ×ˢ (univ : Set (Circle × Circle))) ⊆ e.target ∧
      (∀ z, (e.symm : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) (0,z) = (0,z)) := by
  classical
  let H : ℝ × (Circle × Circle) → ℝ × (Circle × Circle) := fun q => (f q,q.2)
  have hH : ContMDiff (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) ∞ H :=
    hf.prodMk contMDiff_snd
  have hloc (z : (Circle × Circle)) : IsLocalDiffeomorphAt (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1)))
      (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) ∞ H (0,z) :=
    torus_smooth_local_inverse_v489 hH (torus_radial_graph_rank_v489 f hf htrans z)
  choose Phi hPhi hEq using hloc
  let O : Set (ℝ × (Circle × Circle)) := ⋃ z, (Phi z).source
  have hO : IsOpen O := isOpen_iUnion fun z => (Phi z).open_source
  let K : Set (ℝ × (Circle × Circle)) := {0} ×ˢ univ
  have hK : IsCompact K := isCompact_singleton.prod isCompact_univ
  have hKO : K ⊆ O := by
    rintro ⟨t,z⟩ ⟨ht,_⟩
    have ht0 : t = 0 := ht
    subst t
    exact mem_iUnion.mpr ⟨z,hPhi z⟩
  have hlocalO : ∀ p ∈ O, IsLocalDiffeomorphAt (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1)))
      (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) ∞ H p := by
    intro p hp
    obtain ⟨z,hz⟩ := mem_iUnion.mp hp
    exact ⟨Phi z,hz,hEq z⟩
  have hKinj : InjOn H K := by
    intro u hu v hv huv
    have hfirst : u.1 = v.1 := (show u.1 = 0 from hu.1).trans (show v.1 = 0 from hv.1).symm
    have hsecond := congrArg (fun r : ℝ × (Circle × Circle) => r.2) huv
    exact Prod.ext hfirst hsecond
  obtain ⟨T,hT,hKT,hTinj⟩ := hKinj.exists_isOpen_superset hK
    (fun p _ => hH.continuous.continuousAt) (by
      intro p hp
      obtain ⟨Phi',hpPhi',hEqPhi'⟩ := hlocalO p (hKO hp)
      refine ⟨Phi'.source,Phi'.open_source.mem_nhds hpPhi',?_⟩
      intro u hu v hv huv
      exact Phi'.toPartialEquiv.injOn hu hv
        ((hEqPhi' hu).symm.trans (huv.trans (hEqPhi' hv))))
  let R : Set (ℝ × (Circle × Circle)) := T ∩ O
  have hR : IsOpen R := hT.inter hO
  have hKR : K ⊆ R := fun p hp => ⟨hKT hp,hKO hp⟩
  have hRinj : InjOn H R := hTinj.mono inter_subset_left
  have hlocalR : IsLocalDiffeomorphOn (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) ∞ H R := by
    rintro ⟨p,hp⟩
    exact hlocalO p hp.2
  have hopen : IsOpenMap (R.domRestrict H) := by
    intro W hW
    rw [Set.domRestrict_eq,Set.image_comp]
    let V : Set (ℝ × (Circle × Circle)) := ((↑) : R → ℝ × (Circle × Circle)) '' W
    have hV : IsOpen V := hR.isOpenMap_subtype_val W hW
    have hVR : V ⊆ R := by rintro _ ⟨p,hp,rfl⟩; exact p.2
    change IsOpen (H '' V)
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨p,hp,rfl⟩
    obtain ⟨Psi,hpPsi,hEqPsi⟩ := hlocalR ⟨p,hVR hp⟩
    refine ⟨Psi.toOpenPartialHomeomorph '' (V ∩ Psi.source),?_,?_,?_⟩
    · rintro _ ⟨q,hq,rfl⟩
      exact ⟨q,hq.1,hEqPsi hq.2⟩
    · exact Psi.toOpenPartialHomeomorph.isOpen_image_of_subset_source
        (hV.inter Psi.open_source) inter_subset_right
    · exact ⟨p,⟨hp,hpPsi⟩, (hEqPsi hpPsi).symm⟩
  let e : OpenPartialHomeomorph (ℝ × (Circle × Circle)) (ℝ × (Circle × Circle)) :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hRinj.toPartialEquiv H R)
      (hH.continuous.continuousOn) hopen hR
  have he_coe : (e : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) = H := rfl
  have he_source : e.source = R := rfl
  have he_smooth : ContMDiffOn (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) ∞ e.symm e.target := by
    intro y hy
    let p : ℝ × (Circle × Circle) := e.symm y
    have hp : p ∈ R := e.map_target hy
    obtain ⟨Psi,hpPsi,hEqPsi⟩ := hlocalR ⟨p,hp⟩
    have hpH : H p = y := e.right_inv hy
    have hyPsi : y ∈ Psi.target := by
      rw [← hpH,hEqPsi hpPsi]
      exact Psi.toPartialEquiv.map_source hpPsi
    have hPsiY : (Psi.symm : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) y = p := by
      rw [← hpH,hEqPsi hpPsi]
      exact Psi.toPartialEquiv.left_inv hpPsi
    have hnear : e.symm =ᶠ[𝓝 y] (Psi.symm : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) := by
      have hpre := (Psi.symm.contMDiffOn.continuousOn.continuousAt
        (Psi.open_target.mem_nhds hyPsi)).preimage_mem_nhds
          (by rw [hPsiY]; exact hR.mem_nhds hp)
      filter_upwards [Psi.open_target.mem_nhds hyPsi,hpre,e.open_target.mem_nhds hy]
        with y' hy'Psi hy'pre hy'e
      have hp'Psi : Psi.symm y' ∈ Psi.source := Psi.toPartialEquiv.map_target hy'Psi
      have hH' : H (Psi.symm y') = y' := by
        rw [hEqPsi hp'Psi]
        exact Psi.toPartialEquiv.right_inv hy'Psi
      apply e.injOn (e.map_target hy'e) hy'pre
      rw [e.right_inv hy'e,he_coe,hH']
    exact ((Psi.symm.contMDiffOn.contMDiffAt (Psi.open_target.mem_nhds hyPsi)).congr_of_eventuallyEq
      hnear).contMDiffWithinAt
  let E : PartialDiffeomorph (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1)))
      (ℝ × (Circle × Circle)) (ℝ × (Circle × Circle)) ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := hH.contMDiffOn
    contMDiffOn_invFun := he_smooth }
  have hEzero (z : (Circle × Circle)) : E (0,z) = (0,z) := by
    change (f (0,z),z) = (0,z)
    rw [hzero]
  refine ⟨E,rfl,hKR,?_,?_⟩
  · rintro ⟨t,z⟩ ⟨ht,_⟩
    have ht0 : t = 0 := ht
    subst t
    rw [← hEzero z]
    exact E.toPartialEquiv.map_source (hKR (show (0,z) ∈ K from ⟨by simp,mem_univ z⟩))
  · intro z
    calc (E.symm : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) (0,z) = E.symm (E (0,z)) :=
        congrArg E.symm (hEzero z).symm
      _ = (0,z) := E.toPartialEquiv.left_inv
        (hKR (show (0,z) ∈ K from ⟨by simp,mem_univ z⟩))

#print axioms torus_smooth_local_inverse_v489
#print axioms torus_radial_graph_rank_v489
#print axioms torus_radial_compact_partialDiffeomorph_v489
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
