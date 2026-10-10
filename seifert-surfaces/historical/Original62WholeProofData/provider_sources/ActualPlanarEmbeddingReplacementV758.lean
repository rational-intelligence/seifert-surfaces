import SchoenfliesNativeCoimportProbeV754

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology
noncomputable section
namespace CompressionActualPlanarEmbeddingReplacementV758

abbrev Plane := Schoenflies.Plane

/-- Replace an entire closed planar region inside an ambient homeomorphism.
    Boundary agreement and the exact open/closed image identities ensure that
    the prescribed embedding is preserved at EVERY region point. -/
theorem whole_region_extension (K U : Set Plane) (hK : IsClosed K)
    (hU : IsOpen U) (hUK : U ⊆ K) (k₀ : K)
    (f : C(K,Plane)) (hf : IsEmbedding f) (H : Plane ≃ₜ Plane)
    (hrange : Set.range f = H '' K)
    (hopen : f '' {x : K | (x : Plane) ∈ U} = H '' U)
    (hboundary : ∀ x : K,(x : Plane) ∉ U → f x = H x) :
    ∃ F : Plane ≃ₜ Plane,∀ x : K,F x = f x := by
  classical
  let V : Set Plane := Set.range f
  let O : Set Plane := H '' U
  have hVclosed : IsClosed V := by
    change IsClosed (Set.range f)
    rw [hrange]
    exact H.isClosedMap K hK
  have hOopen : IsOpen O := H.isOpenMap U hU
  have hOV : O ⊆ V := by
    change H '' U ⊆ Set.range f
    rw [← hopen]
    exact image_subset_range _ _
  let e : K ≃ₜ V := hf.toHomeomorph
  have hef (x : K) : (e x : Plane) = f x := rfl
  let a : Plane → Plane := Function.extend Subtype.val f (fun _ => f k₀)
  have haf (x : K) : a x = f x := Subtype.val_injective.extend_apply _ _ x
  let b : Plane → Plane := Function.extend Subtype.val
    (fun x : V => (e.symm x : Plane)) (fun _ => k₀.val)
  have heb (x : V) : b x = (e.symm x : Plane) := Subtype.val_injective.extend_apply _ _ x
  let p : Plane → Plane := K.piecewise a H
  let q : Plane → Plane := V.piecewise b H.symm
  have hpa (x : K) : p x = f x := by
    change K.piecewise a H x = f x
    rw [Set.piecewise_eq_of_mem K a H x.property,haf]
  have hpb (x : Plane) (hx : x ∉ K) : p x = H x := Set.piecewise_eq_of_notMem K a H hx
  have hqb (x : V) : q x = (e.symm x : Plane) := by
    change V.piecewise b H.symm x = _
    rw [Set.piecewise_eq_of_mem V b H.symm x.property,heb]
  have hqc (x : Plane) (hx : x ∉ V) : q x = H.symm x := Set.piecewise_eq_of_notMem V b H.symm hx
  have hpH (x : Plane) (hx : x ∉ U) : p x = H x := by
    by_cases hxK : x ∈ K
    · exact (hpa ⟨x,hxK⟩).trans (hboundary ⟨x,hxK⟩ hx)
    · exact hpb x hxK
  have hqH (y : Plane) (hy : y ∉ O) : q y = H.symm y := by
    by_cases hyV : y ∈ V
    · let x := e.symm ⟨y,hyV⟩
      have hfx : f x = y := congrArg Subtype.val (e.apply_symm_apply ⟨y,hyV⟩)
      have hxU : (x : Plane) ∉ U := by
        intro hx
        apply hy
        change y ∈ H '' U
        rw [← hopen]
        exact ⟨x,hx,hfx⟩
      have hHx : H x = y := (hboundary x hxU).symm.trans hfx
      exact (hqb ⟨y,hyV⟩).trans (H.injective (by rw [H.apply_symm_apply]; exact hHx))
    · exact hqc y hyV
  have hpc : Continuous p := by
    have hfirst : ContinuousOn p K := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      exact f.continuous.congr (fun x => (hpa x).symm)
    have hsecond : ContinuousOn p Uᶜ := H.continuous.continuousOn.congr
      (fun x hx => hpH x hx)
    have hcover : K ∪ Uᶜ = Set.univ := by
      ext x
      simp only [mem_union,mem_compl_iff,mem_univ,iff_true]
      by_cases hx : x ∈ U
      · exact Or.inl (hUK hx)
      · exact Or.inr hx
    rw [← continuousOn_univ,← hcover]
    exact hfirst.union_of_isClosed hsecond hK hU.isClosed_compl
  have hqcont : Continuous q := by
    have hfirst : ContinuousOn q V := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      exact (continuous_subtype_val.comp e.symm.continuous).congr (fun x => (hqb x).symm)
    have hsecond : ContinuousOn q Oᶜ := H.symm.continuous.continuousOn.congr
      (fun x hx => hqH x hx)
    have hcover : V ∪ Oᶜ = Set.univ := by
      ext x
      simp only [mem_union,mem_compl_iff,mem_univ,iff_true]
      by_cases hx : x ∈ O
      · exact Or.inl (hOV hx)
      · exact Or.inr hx
    rw [← continuousOn_univ,← hcover]
    exact hfirst.union_of_isClosed hsecond hVclosed hOopen.isClosed_compl
  have hqp (x : Plane) : q (p x) = x := by
    by_cases hx : x ∈ K
    · rw [hpa ⟨x,hx⟩]
      have he : e ⟨x,hx⟩ = ⟨f ⟨x,hx⟩,mem_range_self _⟩ := rfl
      rw [hqb ⟨f ⟨x,hx⟩,mem_range_self _⟩,← he,e.symm_apply_apply]
    · rw [hpb x hx,hqc]
      · exact H.symm_apply_apply x
      · change H x ∉ Set.range f
        rw [hrange]
        rintro ⟨z,hz,he⟩
        exact hx ((H.injective he) ▸ hz)
  have hpq (y : Plane) : p (q y) = y := by
    by_cases hy : y ∈ V
    · rw [hqb ⟨y,hy⟩,hpa]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩)
    · rw [hqc y hy,hpb]
      · exact H.apply_symm_apply y
      · intro hx
        apply hy
        change y ∈ Set.range f
        rw [hrange]
        exact ⟨H.symm y,hx,H.apply_symm_apply y⟩
  let F : Plane ≃ₜ Plane := {
    toFun := p
    invFun := q
    left_inv := hqp
    right_inv := hpq
    continuous_toFun := hpc
    continuous_invFun := hqcont }
  exact ⟨F,hpa⟩

end CompressionActualPlanarEmbeddingReplacementV758
