import ActualTaperedNormalBlockIsotopyV837

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped Manifold ContDiff
open Set Topology Manifold
open SeifertSurfaces.Foundations
noncomputable section
namespace CompressionActualSupportedChartAmbientIsotopyV846

/-- Construct the compact parameter-preserving bundle from the actual
    supported homeomorphism stages, then extend it through a chart. The
    closure avoidance hypotheses concern the full specified forbidden set. -/
theorem supported_chart_ambient_isotopy
    {X M : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (e : OpenPartialHomeomorph X M) (W : Set X) (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (hWs : closure W ⊆ e.source)
    (L : Time → X ≃ₜ X) (hL : Continuous (fun p : Time × X => L p.1 p.2))
    (hL0 : ∀ x,L 0 x = x) (hoff : ∀ t x,x ∉ W → L t x = x)
    (Z : Set M) (hZ : Disjoint (e '' closure W) Z)
    (hbd : Disjoint (e '' closure W) ((𝓡∂ 3).boundary M)) :
    ∃ I : TopologicalAmbientIsotopy M,
      IsOpen (e '' W) ∧ IsCompact (closure (e '' W)) ∧
      Disjoint (closure (e '' W)) Z ∧
      Disjoint (closure (e '' W)) ((𝓡∂ 3).boundary M) ∧
      (∀ t x,x ∉ e '' W → I.stage t x = x) ∧
      (∀ t x,x ∈ (𝓡∂ 3).boundary M → I.stage t x = x) ∧
      ∀ t x,x ∈ closure W → I.stage t (e x) = e (L t x) := by
  classical
  let K : Set X := closure W
  have hLo (t : Time) (x : X) (hx : x ∉ K) : L t x = x :=
    hoff t x (fun hw => hx (subset_closure hw))
  have hLi (t : Time) (x : X) (hx : x ∉ K) : (L t).symm x = x :=
    (L t).injective (by rw [(L t).apply_symm_apply,hLo t x hx])
  have hmaps (t : Time) : MapsTo (L t) K K := by
    intro x hx
    by_contra hn
    have he : x = L t x := (L t).injective (hLo t (L t x) hn).symm
    exact hn (he ▸ hx)
  have hmapsi (t : Time) : MapsTo (L t).symm K K := by
    intro x hx
    by_contra hn
    have he : x = (L t).symm x := (L t).symm.injective (hLi t ((L t).symm x) hn).symm
    exact hn (he ▸ hx)
  have hLc : Continuous (fun p : Time × X => (L p.1).symm p.2) :=
    CompressionActualCompactlySupportedContinuousBijectionV823.continuous_family_inverse
      L hL K hWc hLo
  let H : (Time × K) ≃ₜ (Time × K) := {
    toFun := fun p => (p.1,⟨L p.1 p.2.val,hmaps p.1 p.2.property⟩)
    invFun := fun p => (p.1,⟨(L p.1).symm p.2.val,hmapsi p.1 p.2.property⟩)
    left_inv := by intro p; exact Prod.ext rfl (Subtype.ext ((L p.1).symm_apply_apply p.2.val))
    right_inv := by intro p; exact Prod.ext rfl (Subtype.ext ((L p.1).apply_symm_apply p.2.val))
    continuous_toFun := continuous_fst.prodMk
      ((hL.comp (continuous_fst.prodMk continuous_snd.subtype_val)).subtype_mk _)
    continuous_invFun := continuous_fst.prodMk
      ((hLc.comp (continuous_fst.prodMk continuous_snd.subtype_val)).subtype_mk _) }
  have hHf (t : Time) (p : K) (hp : p.val ∈ frontier K) : H (t,p) = (t,p) := by
    have hn : p.val ∉ W := by
      intro hw
      have hi : p.val ∈ interior K :=
        hW.subset_interior_iff.mpr subset_closure hw
      exact hp.2 hi
    exact Prod.ext rfl (Subtype.ext (hoff t p.val hn))
  have hH0 (p : K) : H (0,p) = (0,p) := Prod.ext rfl (Subtype.ext (hL0 p.val))
  obtain ⟨I,-,-,-,hIo,hIbd,hIon⟩ :=
    CompressionSupportedAmbientHomeomorphFamily.compact_chart_family_topological_ambient_isotopy
      e K hWc hWs H (fun _ => rfl) hHf hH0 Z hZ hbd
  have hKclosed : IsClosed (e '' K) :=
    (hWc.image_of_continuousOn (e.continuousOn.mono hWs)).isClosed
  have hcl : closure (e '' W) ⊆ e '' K :=
    closure_minimal (image_mono subset_closure) hKclosed
  refine ⟨I,e.isOpen_image_of_subset_source hW (subset_closure.trans hWs),
    (hWc.image_of_continuousOn (e.continuousOn.mono hWs)).of_isClosed_subset isClosed_closure hcl,
    hZ.mono_left hcl,hbd.mono_left hcl,?_,hIbd,?_⟩
  · intro t x hx
    by_cases hxK : x ∈ e '' K
    · obtain ⟨p,hp,rfl⟩ := hxK
      have hpW : p ∉ W := fun hw => hx ⟨p,hw,rfl⟩
      rw [hIon t ⟨p,hp⟩]
      exact congrArg e (hoff t p hpW)
    · exact hIo t x (fun hi => hxK (image_mono interior_subset hi))
  · intro t x hx
    exact hIon t ⟨x,hx⟩

#print axioms supported_chart_ambient_isotopy
end CompressionActualSupportedChartAmbientIsotopyV846
