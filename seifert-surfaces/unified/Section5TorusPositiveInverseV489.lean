import Section5TorusRadialInverseV489

noncomputable section
open Set Topology Function Filter Manifold
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Restricting the actual compact inverse to one side gives positive times
uniformly on the whole boundary torus. The side is chosen from the inverse, not
assumed as an orientation input. An arbitrary prescribed open source window
around the initial circle is retained. -/
theorem torus_positive_radial_inverse_v489 (f : ℝ × (Circle × Circle) → ℝ)
    (hzero : ∀ z, f (0,z) = 0)
    (e : PartialDiffeomorph (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1)))
      (ℝ × (Circle × Circle)) (ℝ × (Circle × Circle)) ∞)
    (he : (e : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) = fun q => (f q,q.2))
    (hsource : ({0} ×ˢ (univ : Set (Circle × Circle))) ⊆ e.source)
    (htarget : ({0} ×ˢ (univ : Set (Circle × Circle))) ⊆ e.target)
    (hinitial : ∀ z, (e.symm : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) (0,z) = (0,z))
    (R : Set (ℝ × (Circle × Circle))) (hR : IsOpen R)
    (hRzero : ({0} ×ˢ (univ : Set (Circle × Circle))) ⊆ R) :
    ∃ b sign : ℝ, 0 < b ∧ (sign = 1 ∨ sign = -1) ∧
      ∃ tau : ℝ × (Circle × Circle) → ℝ,
        ContMDiffOn (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) ∞ tau (Icc (0 : ℝ) b ×ˢ univ) ∧
        (∀ z, tau (0,z) = 0) ∧
        (∀ s ∈ Icc (0 : ℝ) b, ∀ z, (tau (s,z),z) ∈ R ∧ f (tau (s,z),z) = sign*s) ∧
        (∀ s ∈ Ioc (0 : ℝ) b, ∀ z, 0 < tau (s,z)) := by
  classical
  let N : Set (ℝ × (Circle × Circle)) := e.target ∩ (e.symm : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) ⁻¹' R
  have hN : IsOpen N :=
    e.symm.contMDiffOn.continuousOn.isOpen_inter_preimage e.open_target hR
  have hNzero : ({0} ×ˢ (univ : Set (Circle × Circle))) ⊆ N := by
    rintro ⟨s,z⟩ ⟨hs,hz⟩
    have hs0 : s = 0 := hs
    subst s
    exact ⟨htarget ⟨by simp,hz⟩,by rw [mem_preimage,hinitial]; exact hRzero ⟨by simp,hz⟩⟩
  obtain ⟨V,W,hV,hW,h0V,hUW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hN hNzero
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (show (0 : ℝ) ∈ V from h0V (by simp)))
  let c : ℝ := d/2
  have hc : 0 < c := half_pos hd
  have hcylinder : Icc (-c) c ×ˢ (univ : Set (Circle × Circle)) ⊆ N := by
    intro q hq
    apply hVW
    refine ⟨hball ?_,hUW hq.2⟩
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    exact (abs_le.mpr hq.1).trans_lt (half_lt_self hd)
  let A : Set (ℝ × (Circle × Circle)) :=
    (e.source ∩ (e : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) ⁻¹' (Ioo (-c) c ×ˢ univ)) ∩ R
  have hA : IsOpen A :=
    (e.contMDiffOn.continuousOn.isOpen_inter_preimage e.open_source
      (isOpen_Ioo.prod isOpen_univ)).inter hR
  have h0A : ((0 : ℝ),(1 : (Circle × Circle))) ∈ A := by
    refine ⟨⟨hsource ⟨by simp,mem_univ _⟩,?_⟩,hRzero ⟨by simp,mem_univ _⟩⟩
    rw [mem_preimage,he]
    exact ⟨⟨by simpa [hzero] using neg_lt_zero.mpr hc,by simpa [hzero] using hc⟩,mem_univ _⟩
  have hpre := (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hA.mem_nhds h0A)
  obtain ⟨eta,heta,hetaA⟩ := Metric.mem_nhds_iff.mp hpre
  let t : ℝ := eta/2
  have ht : 0 < t := half_pos heta
  have htA : (t,(1 : (Circle × Circle))) ∈ A := hetaA (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht]
    exact half_lt_self heta)
  let y : ℝ := f (t,1)
  have hybound : y ∈ Ioo (-c) c := by
    have h := htA.1.2
    rw [mem_preimage,he] at h
    exact h.1
  have hy : y ≠ 0 := by
    intro hy0
    have hsame : e (t,(1 : (Circle × Circle))) = e (0,(1 : (Circle × Circle))) := by simp only [he,y,hzero,hy0]
    have heq := e.toPartialEquiv.injOn htA.1.1 (hsource ⟨by simp,mem_univ _⟩) hsame
    exact ht.ne' (congrArg (fun q : ℝ × (Circle × Circle) => q.1) heq)
  let sign : ℝ := if 0 < y then 1 else -1
  have hsign : sign = 1 ∨ sign = -1 := by dsimp only [sign]; split <;> simp
  have hsignabs (s : ℝ) : |sign*s| = |s| := by
    rcases hsign with hs | hs <;> rw [hs] <;> simp
  have hsigny : sign*|y| = y := by
    dsimp only [sign]
    split_ifs with hp
    · simp [abs_of_pos hp]
    · have hn : y < 0 := lt_of_le_of_ne (le_of_not_gt hp) hy
      simp [abs_of_neg hn]
  let P : ℝ × (Circle × Circle) → ℝ × (Circle × Circle) := fun q => (sign*q.1,q.2)
  let tau : ℝ × (Circle × Circle) → ℝ := fun q => (e.symm (P q)).1
  have hP : ContMDiff (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) ∞ P :=
    (contMDiff_const.mul contMDiff_fst).prodMk contMDiff_snd
  have hPN (s : ℝ) (hs : |s| ≤ c) (z : (Circle × Circle)) : P (s,z) ∈ N :=
    hcylinder ⟨abs_le.mp (by rw [hsignabs]; exact hs),mem_univ z⟩
  have hright (s : ℝ) (hs : |s| ≤ c) (z : (Circle × Circle)) :
      (tau (s,z),z) ∈ R ∧ f (tau (s,z),z) = sign*s := by
    have hN' := hPN s hs z
    have heq := e.toPartialEquiv.right_inv hN'.1
    rw [he] at heq
    have hz : (e.symm (P (s,z))).2 = z := congrArg (fun q : ℝ × (Circle × Circle) => q.2) heq
    have hpair : e.symm (P (s,z)) = (tau (s,z),z) := Prod.ext rfl hz
    refine ⟨?_,?_⟩
    · rw [← hpair]
      exact hN'.2
    · have h := congrArg (fun q : ℝ × (Circle × Circle) => q.1) heq
      change f ((e.symm : ℝ × (Circle × Circle) → ℝ × (Circle × Circle)) (P (s,z))) = sign*s at h
      rw [hpair] at h
      exact h
  let D : Set (ℝ × (Circle × Circle)) := Ioo (0 : ℝ) c ×ˢ univ
  have hDc : ContinuousOn tau D :=
    (continuous_fst.comp_continuousOn e.symm.contMDiffOn.continuousOn).comp
      hP.continuous.continuousOn (fun q hq => (hPN q.1 (by rw [abs_of_pos hq.1.1]; exact hq.1.2.le) q.2).1)
  have hnonzero : ∀ q ∈ D, tau q ≠ 0 := by
    intro q hq hn
    have h := (hright q.1 (by rw [abs_of_pos hq.1.1]; exact hq.1.2.le) q.2).2
    rw [hn,hzero] at h
    have hsgn : sign ≠ 0 := by rcases hsign with hs | hs <;> rw [hs] <;> norm_num
    exact (mul_ne_zero hsgn hq.1.1.ne') h.symm
  have hanchor : ∃ q ∈ D, 0 < tau q := by
    have habs : |y| ∈ Ioo (0 : ℝ) c := ⟨abs_pos.mpr hy,abs_lt.mpr hybound⟩
    refine ⟨(|y|,(1 : (Circle × Circle))),⟨habs,mem_univ _⟩,?_⟩
    have hp : P (|y|,(1 : (Circle × Circle))) = e (t,(1 : (Circle × Circle))) := by
      rw [he]
      exact Prod.ext hsigny rfl
    change 0 < (e.symm (P (|y|,(1 : (Circle × Circle))))).1
    rw [hp]
    change 0 < (e.toPartialEquiv.symm (e.toPartialEquiv (t,(1 : (Circle × Circle))))).1
    rw [e.toPartialEquiv.left_inv htA.1.1]
    exact ht
  have hpositive : ∀ q ∈ D, 0 < tau q := by
    intro q hq
    exact (isPreconnected_Ioo.prod isPreconnected_univ).lt_of_ne hDc hnonzero hanchor hq
  have hb : 0 < c/2 := half_pos hc
  have hsmall (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (c/2)) : |s| ≤ c := by
    rw [abs_of_nonneg hs.1]
    exact hs.2.trans (half_le_self hc.le)
  refine ⟨c/2,sign,hb,hsign,tau,?_,?_,?_,?_⟩
  · exact (contMDiff_fst.comp_contMDiffOn e.symm.contMDiffOn).comp hP.contMDiffOn
      (fun q hq => (hPN q.1 (hsmall q.1 hq.1) q.2).1)
  · intro z
    change (e.symm (sign*0,z)).1 = 0
    rw [mul_zero,hinitial]
  · intro s hs z
    exact hright s (hsmall s hs) z
  · intro s hs z
    exact hpositive (s,z) ⟨⟨hs.1,hs.2.trans_lt (half_lt_self hc)⟩,mem_univ z⟩

#print axioms torus_positive_radial_inverse_v489
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
