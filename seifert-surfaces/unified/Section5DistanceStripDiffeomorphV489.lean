import Section5DistanceInverseDataV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section

/-- Convert a smooth inverse of a positive radial coordinate into a genuine
half-collar diffeomorphism with open image. -/
theorem distance_strip_diffeomorph
    (a b : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b)
    (F tau : ℝ × (Circle × Circle) → ℝ)
    (e : PartialDiffeomorph (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1)))
      (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (ℝ × (Circle × Circle)) (ℝ × (Circle × Circle)) ∞)
    (hF : ContMDiff (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) ∞ F)
    (htau : ContMDiff (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) ∞ tau)
    (hF0 : ∀ p, F (0,p) = 0) (htau0 : ∀ p, tau (0,p) = 0)
    (he : (e : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) = fun q => (F q,q.2))
    (hsource : ({0} ×ˢ (univ : Set (Circle × Circle))) ⊆ e.source)
    (hFnonneg : ∀ p : Circle × Circle, ∀ t : Time, (t : ℝ) ≤ a → 0 ≤ F ((t : ℝ),p))
    (hright : ∀ s ∈ Icc (0 : ℝ) b, ∀ p,
      (tau (s,p),p) ∈ e.source ∧ tau (s,p) ∈ Ico (0 : ℝ) a ∧ F (tau (s,p),p) = s) :
    ∃ O : TopologicalSpace.Opens ((Circle × Circle) × Time),
    ∃ C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))
      (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) longitudeProductStrip O ∞,
      (∀ q : longitudeProductStrip, (C q).val.1 = q.val.1 ∧
        ((C q).val.2 : ℝ) = tau (b*(q.val.2 : ℝ),q.val.1)) ∧
      (∀ p : Circle × Circle, (p,(0 : Time)) ∈ O) ∧
      (∀ p, (C (longitudeBoundarySection p)).val = (p,0)) ∧
      (∀ q : O, (q.val.2 : ℝ) < a ∧ F ((q.val.2 : ℝ),q.val.1) < b) := by
  let Q : ((Circle × Circle) × Time) → ℝ × (Circle × Circle) := fun q => ((q.2 : ℝ),q.1)
  have hQ : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))
      (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) ∞ Q :=
    (contMDiff_subtypeVal_Icc.comp contMDiff_snd).prodMk contMDiff_fst
  let O : TopologicalSpace.Opens ((Circle × Circle) × Time) :=
    ⟨{q | (q.2 : ℝ) < a ∧ Q q ∈ e.source ∧ F (Q q) < b},
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const).inter
        ((e.open_source.preimage hQ.continuous).inter
          (isOpen_lt (hF.continuous.comp hQ.continuous) continuous_const))⟩
  have hscaled (q : longitudeProductStrip) : b*(q.val.2 : ℝ) ∈ Icc (0 : ℝ) b :=
    ⟨mul_nonneg hb.le q.val.2.property.1,by simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left q.val.2.property.2 hb.le)⟩
  have htime (q : longitudeProductStrip) : tau (b*(q.val.2 : ℝ),q.val.1) ∈ Icc (0 : ℝ) 1 :=
    ⟨(hright _ (hscaled q) _).2.1.1,((hright _ (hscaled q) _).2.1.2.trans ha1).le⟩
  let f : longitudeProductStrip → O := fun q =>
    ⟨(q.val.1,⟨tau (b*(q.val.2 : ℝ),q.val.1),htime q⟩),
      (hright _ (hscaled q) _).2.1.2,(hright _ (hscaled q) _).1,by
        change F (tau (b*(q.val.2 : ℝ),q.val.1),q.val.1) < b
        rw [(hright _ (hscaled q) _).2.2]
        simpa only [mul_one] using mul_lt_mul_of_pos_left q.property hb⟩
  have hinverse (q : O) : F (Q q.val)/b ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (hFnonneg q.val.1 q.val.2 q.property.1.le) hb.le,
      ((div_lt_one hb).mpr q.property.2.2).le⟩
  let inv : O → longitudeProductStrip := fun q =>
    ⟨(q.val.1,⟨F (Q q.val)/b,hinverse q⟩),(div_lt_one hb).mpr q.property.2.2⟩
  have hleft (q : longitudeProductStrip) : inv (f q) = q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply Subtype.ext
    change F (tau (b*(q.val.2 : ℝ),q.val.1),q.val.1)/b = (q.val.2 : ℝ)
    rw [(hright _ (hscaled q) _).2.2,mul_div_cancel_left₀ _ hb.ne']
  have hrightInv (q : O) : f (inv q) = q := by
    have hFs : F (Q q.val) ∈ Icc (0 : ℝ) b :=
      ⟨hFnonneg q.val.1 q.val.2 q.property.1.le,q.property.2.2.le⟩
    have hEq : e (tau (F (Q q.val),q.val.1),q.val.1) = e (Q q.val) := by
      rw [he]
      exact Prod.ext (hright _ hFs _).2.2 rfl
    have hInv := e.toPartialEquiv.injOn (hright _ hFs _).1 q.property.2.1 hEq
    have ht := congrArg Prod.fst hInv
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply Subtype.ext
    change tau (b*(F (Q q.val)/b),q.val.1) = (q.val.2 : ℝ)
    rw [mul_div_cancel₀ _ hb.ne']
    exact ht
  have hf : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))
      (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff O _).mp
    apply contMDiff_subtype_val.fst.prodMk
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    have ht : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
        (fun q : longitudeProductStrip => tau (b*(q.val.2 : ℝ),q.val.1)) :=
      htau.comp ((contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp
        contMDiff_subtype_val.snd)).prodMk contMDiff_subtype_val.fst)
    exact ⟨ht.continuous.subtype_mk _,ht⟩
  have hi : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))
      (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ∞ inv := by
    apply (ContMDiff.subtypeVal_comp_iff longitudeProductStrip _).mp
    apply contMDiff_subtype_val.fst.prodMk
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    have ht : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
        (fun q : O => F (Q q.val)/b) :=
      (hF.comp (hQ.comp contMDiff_subtype_val)).div_const b
    exact ⟨ht.continuous.subtype_mk _,ht⟩
  let C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))
      (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) longitudeProductStrip O ∞ :=
    ⟨⟨f,inv,hleft,hrightInv⟩,hf,hi⟩
  refine ⟨O,C,fun q => ⟨rfl,rfl⟩,?_,?_,fun q => ⟨q.property.1,q.property.2.2⟩⟩
  · intro p
    exact ⟨ha,hsource ⟨rfl,mem_univ p⟩,by change F (0,p) < b; rw [hF0]; exact hb⟩
  · intro p
    apply Prod.ext
    · rfl
    apply Subtype.ext
    change tau (b*0,p) = 0
    rw [mul_zero,htau0]

#print axioms distance_strip_diffeomorph
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
