import CurveComplexGenusTwo.Foundations.OctagonQuotient
import CurveComplexGenusTwo.Octagon.EdgeCollar

namespace CurveComplex.Octagon

theorem isOpenMap_domRestrict_of_open_saturated
    {U : Set Disk} (hU : IsOpen U)
    (hsat : mk ⁻¹' (mk '' U) = U)
    (hinj : Set.InjOn mk U) :
    IsOpenMap (U.domRestrict mk) := by
  intro s hs
  have hs' : IsOpen ((Subtype.val : U → Disk) '' s) :=
    hU.isOpenEmbedding_subtypeVal.isOpenMap s hs
  have himage : U.domRestrict mk '' s = mk ''
      ((Subtype.val : U → Disk) '' s) := by
    ext q
    simp [Set.mem_image]
  rw [himage]
  apply (quotient_mk.isCoinducing.isOpen_preimage).mp
  have hpre : mk ⁻¹' (mk '' ((Subtype.val : U → Disk) '' s)) =
      ((Subtype.val : U → Disk) '' s) := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, hxy⟩
      have hxU : x ∈ U := by
        rw [← hsat]
        exact ⟨(z : Disk), z.property, hxy⟩
      have heq : x = (z : Disk) :=
        hinj hxU z.property hxy.symm
      subst x
      exact ⟨z, hz, rfl⟩
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [hpre]
  exact hs'

noncomputable def homeomorph_image_of_open_saturated_inj
    {U : Set Disk} (hU : IsOpen U)
    (hsat : mk ⁻¹' (mk '' U) = U)
    (hinj : Set.InjOn mk U) :
    U ≃ₜ mk '' U := by
  have hcont : Continuous (U.domRestrict mk) :=
    continuous_mk.comp continuous_subtype_val
  have hinj' : Function.Injective (U.domRestrict mk) := by
    intro x y hxy
    exact Subtype.ext (hinj x.property y.property hxy)
  have hemb : Topology.IsOpenEmbedding (U.domRestrict mk) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      hcont hinj' (isOpenMap_domRestrict_of_open_saturated hU hsat hinj)
  exact hemb.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by ext q; simp [Set.range_domRestrict]))

theorem exists_open_saturated_neighborhood
    {U : Set Disk} (hU : IsOpen U) {a : Disk}
    (hclass : relationClass a ⊆ U) :
    ∃ V : Set Disk, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      mk ⁻¹' (mk '' V) = V := by
  let V : Set Disk := (saturation Uᶜ)ᶜ
  have hVopen : IsOpen V := saturation_compl_open hU
  have haV : a ∈ V :=
    relationClass_subset_of_saturatedOpen hclass
      (_root_.Relation.EqvGen.refl a)
  have hVU : V ⊆ U := by
    intro x hx
    change x ∉ saturation Uᶜ at hx
    by_contra hxU
    exact hx ⟨x, hxU, _root_.Relation.EqvGen.refl x⟩
  have hVsat : mk ⁻¹' (mk '' V) = V := by
    simpa [V] using saturatedOpen_preimage_image hU
  exact ⟨V, hVopen, haV, hVU, hVsat⟩

theorem exists_open_quotient_neighborhood_of_fiber
    {U : Set Disk} (hU : IsOpen U) {a : Disk}
    (hclass : relationClass a ⊆ U) :
    ∃ W : Set Surface, IsOpen W ∧ mk a ∈ W ∧ mk ⁻¹' W ⊆ U := by
  obtain ⟨V, hVopen, haV, hVU, hVsat⟩ :=
    exists_open_saturated_neighborhood hU hclass
  refine ⟨mk '' V, ?_, ⟨a, haV, rfl⟩, ?_⟩
  · apply (quotient_mk.isCoinducing.isOpen_preimage).mp
    simpa [hVsat] using hVopen
  · rw [hVsat]
    exact hVU

theorem exists_open_local_quotient_homeomorph
    {U : Set Disk} (hU : IsOpen U) (hUinj : Set.InjOn mk U)
    {a : Disk} (hclass : relationClass a ⊆ U) :
    ∃ (V : Set Disk) (W : Set Surface),
      IsOpen V ∧ IsOpen W ∧ a ∈ V ∧ mk a ∈ W ∧
      V ⊆ U ∧ W ⊆ mk '' U ∧
      mk ⁻¹' (mk '' V) = V ∧ Nonempty (V ≃ₜ W) := by
  obtain ⟨V, hVopen, haV, hVU, hVsat⟩ :=
    exists_open_saturated_neighborhood hU hclass
  let W : Set Surface := mk '' V
  have hWinj : Set.InjOn mk V := by
    intro x hx y hy hxy
    exact hUinj (hVU hx) (hVU hy) hxy
  have hWopen : IsOpen W := by
    apply (quotient_mk.isCoinducing.isOpen_preimage).mp
    simpa [W, hVsat] using hVopen
  have hWa : mk a ∈ W := ⟨a, haV, rfl⟩
  have hWsub : W ⊆ mk '' U := by
    rintro q ⟨x, hx, rfl⟩
    exact ⟨x, hVU hx, rfl⟩
  have hhomeo : V ≃ₜ W := by
    simpa [W] using
      homeomorph_image_of_open_saturated_inj hVopen hVsat hWinj
  exact ⟨V, W, hVopen, hWopen, haV, hWa, hVU, hWsub, hVsat, ⟨hhomeo⟩⟩

private noncomputable def collarBaseAngle (i : Side) : ℝ :=
  2 * Real.pi * (i.val : ℝ) / 8

private noncomputable def collarLocalAngle (t : ℝ) : ℝ :=
  2 * Real.pi * t / 8

private def openPolarParameters : Set (ℝ × ℝ) :=
  Set.Ioi (1 / 2 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 4)

private theorem openPolarParameters_isOpen : IsOpen openPolarParameters :=
  isOpen_Ioi.prod isOpen_Ioo

private theorem openPolarParameters_subset_target :
    openPolarParameters ⊆ Complex.polarCoord.target := by
  rintro ⟨r, θ⟩ ⟨hr, hθ⟩
  change (1 / 2 : ℝ) < r at hr
  change 0 < θ ∧ θ < Real.pi / 4 at hθ
  rw [Complex.polarCoord_target]
  constructor
  · change 0 < r
    linarith
  · change -Real.pi < θ ∧ θ < Real.pi
    constructor <;> nlinarith [Real.pi_pos]

private def ambientOpenCollar (i : Side) : Set ℂ :=
  ((Homeomorph.mulLeft₀
    (Circle.exp (collarBaseAngle i) : ℂ) (by simp) : ℂ ≃ₜ ℂ) ''
      (Complex.polarCoord.symm '' openPolarParameters))

def openCollar (i : Side) : Set Disk :=
  (Subtype.val : Disk → ℂ) ⁻¹' ambientOpenCollar i

theorem openCollar_isOpen (i : Side) : IsOpen (openCollar i) := by
  have hpolar : IsOpen (Complex.polarCoord.symm '' openPolarParameters) :=
    Complex.polarCoord.isOpen_image_symm_of_subset_target
      openPolarParameters_isOpen openPolarParameters_subset_target
  have hrot : IsOpen (ambientOpenCollar i) := by
    exact (Homeomorph.mulLeft₀
      (Circle.exp (collarBaseAngle i) : ℂ) (by simp)).isOpenMap
      _ hpolar
  exact hrot.preimage continuous_subtype_val

private theorem polarSymm_eq_real_mul_circleExp (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = (r : ℂ) * (Circle.exp θ : ℂ) := by
  simp [Complex.polarCoord_symm_apply, Circle.coe_exp, Complex.exp_mul_I,
    Complex.ofReal_cos, Complex.ofReal_sin]

theorem collarPoint_mem_openCollar (i : Side) (r : CollarRadius)
    (t : CollarAngle) : collarPoint i r t ∈ openCollar i := by
  have ht0 : 0 < collarLocalAngle (t : ℝ) := by
    unfold collarLocalAngle
    nlinarith [mul_pos Real.pi_pos t.property.1]
  have ht1 : collarLocalAngle (t : ℝ) < Real.pi / 4 := by
    unfold collarLocalAngle
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr t.property.2)]
  have hp : ((r : ℝ), collarLocalAngle (t : ℝ)) ∈ openPolarParameters :=
    ⟨r.property.1, ht0, ht1⟩
  have heq : (collarPoint i r t : ℂ) =
      (Circle.exp (collarBaseAngle i) : ℂ) *
        Complex.polarCoord.symm ((r : ℝ), collarLocalAngle (t : ℝ)) := by
    rw [polarSymm_eq_real_mul_circleExp]
    change ((r : ℝ) : ℂ) *
      (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (t : ℝ)) / 8) : ℂ) =
        (Circle.exp (collarBaseAngle i) : ℂ) *
          (((r : ℝ) : ℂ) * (Circle.exp (collarLocalAngle (t : ℝ)) : ℂ))
    have ha : 2 * Real.pi * ((i.val : ℝ) + (t : ℝ)) / 8 =
        collarBaseAngle i + collarLocalAngle (t : ℝ) := by
      unfold collarBaseAngle collarLocalAngle
      ring
    rw [ha, Circle.exp_add]
    simp only [Circle.coe_mul]
    ring
  change (collarPoint i r t : ℂ) ∈ ambientOpenCollar i
  refine ⟨Complex.polarCoord.symm ((r : ℝ), collarLocalAngle (t : ℝ)),
    ⟨((r : ℝ), collarLocalAngle (t : ℝ)), hp, rfl⟩, ?_⟩
  simpa [Homeomorph.coe_mulLeft₀] using heq.symm

theorem openCollar_eq_collarPoint_range (i : Side) :
    openCollar i =
      Set.range (fun p : CollarRadius × CollarAngle => collarPoint i p.1 p.2) := by
  ext x
  constructor
  · intro hx
    change (x : ℂ) ∈ ambientOpenCollar i at hx
    obtain ⟨z, ⟨p, hp, rfl⟩, hz⟩ := hx
    rcases p with ⟨r, θ⟩
    have hr : (1 / 2 : ℝ) < r := hp.1
    have hθ0 : 0 < θ := hp.2.1
    have hθ1 : θ < Real.pi / 4 := hp.2.2
    have hnorm : ‖(x : ℂ)‖ = r := by
      rw [← hz]
      simp [Homeomorph.coe_mulLeft₀, abs_of_pos (by linarith : 0 < r)]
    have hrle : r ≤ 1 := by
      have hxle : ‖(x : ℂ)‖ ≤ 1 := by
        have h := x.property
        rw [Metric.mem_closedBall, dist_zero_right] at h
        exact h
      linarith
    let r' : CollarRadius := ⟨r, hr, hrle⟩
    let t' : CollarAngle := ⟨4 * θ / Real.pi,
      by
        constructor
        · exact div_pos (by positivity) Real.pi_pos
        · apply (div_lt_iff₀ Real.pi_pos).2
          nlinarith⟩
    have hangle : collarLocalAngle (t' : ℝ) = θ := by
      unfold collarLocalAngle t'
      field_simp [ne_of_gt Real.pi_pos]
      ring
    have hpoint : (collarPoint i r' t' : ℂ) =
        (Circle.exp (collarBaseAngle i) : ℂ) *
          Complex.polarCoord.symm (r, θ) := by
      rw [polarSymm_eq_real_mul_circleExp]
      change ((r : ℝ) : ℂ) *
        (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (t' : ℝ)) / 8) : ℂ) =
          (Circle.exp (collarBaseAngle i) : ℂ) *
            (((r : ℝ) : ℂ) * (Circle.exp θ : ℂ))
      have ha : 2 * Real.pi * ((i.val : ℝ) + (t' : ℝ)) / 8 =
          collarBaseAngle i + θ := by
        rw [← hangle]
        unfold collarBaseAngle collarLocalAngle
        ring
      rw [ha, Circle.exp_add]
      simp only [Circle.coe_mul]
      ring
    refine ⟨(r', t'), ?_⟩
    apply Subtype.ext
    exact hpoint.trans (by simpa [Homeomorph.coe_mulLeft₀] using hz)
  · rintro ⟨⟨r, t⟩, rfl⟩
    exact collarPoint_mem_openCollar i r t

private noncomputable def reverseCollarAngle (t : CollarAngle) : CollarAngle :=
  ⟨1 - (t : ℝ), by
    constructor <;> linarith [t.property.1, t.property.2]⟩

private theorem reverseCollarAngle_toInterval (t : CollarAngle) :
    collarToInterval (reverseCollarAngle t) =
      unitInterval.symm (collarToInterval t) := by
  apply Subtype.ext
  rfl

private theorem collarToInterval_ne_zero (t : CollarAngle) :
    collarToInterval t ≠ 0 := by
  intro h
  have ht := congrArg (fun x : unitInterval => (x : ℝ)) h
  change (t : ℝ) = 0 at ht
  exact (ne_of_gt t.property.1) ht

private theorem collarToInterval_ne_one (t : CollarAngle) :
    collarToInterval t ≠ 1 := by
  intro h
  have ht := congrArg (fun x : unitInterval => (x : ℝ)) h
  change (t : ℝ) = 1 at ht
  exact (ne_of_lt t.property.2) ht

theorem pairedEdge_open_saturated_neighborhood (i : Side) (t : CollarAngle) :
    ∃ (V : Set Disk) (W : Set Surface),
      IsOpen V ∧ IsOpen W ∧
      collarPoint i ⟨1, by norm_num⟩ t ∈ V ∧
      mk (collarPoint i ⟨1, by norm_num⟩ t) ∈ W ∧
      V ⊆
        Set.range (fun p : CollarRadius × CollarAngle => collarPoint i p.1 p.2) ∪
        Set.range (fun p : CollarRadius × CollarAngle =>
          collarPoint (pair i) p.1 p.2) ∧
      mk ⁻¹' W = V ∧ mk ⁻¹' (mk '' V) = V := by
  let a : Disk := collarPoint i ⟨1, by norm_num⟩ t
  let U : Set Disk := openCollar i ∪ openCollar (pair i)
  have hUopen : IsOpen U :=
    (openCollar_isOpen i).union (openCollar_isOpen (pair i))
  have hfirst : side i (collarToInterval t) ∈ openCollar i := by
    simpa [collarPoint_boundary] using
      (collarPoint_mem_openCollar i ⟨1, by norm_num⟩ t)
  have hsecond :
      side (pair i) (unitInterval.symm (collarToInterval t)) ∈
        openCollar (pair i) := by
    simpa [collarPoint_boundary, reverseCollarAngle_toInterval] using
      (collarPoint_mem_openCollar (pair i) ⟨1, by norm_num⟩
        (reverseCollarAngle t))
  have hclass : relationClass a ⊆ U := by
    intro x hx
    have hmx : mk x = mk (side i (collarToInterval t)) := by
      change Relation.r x a at hx
      exact (Quotient.sound hx).trans (congrArg mk (collarPoint_boundary i t))
    have hxfiber : x ∈ mk ⁻¹' ({mk (side i (collarToInterval t))} : Set Surface) :=
      hmx
    rw [edge_interior_fiber_eq_pair i (collarToInterval t)
      (collarToInterval_ne_zero t) (collarToInterval_ne_one t)] at hxfiber
    rcases Set.mem_insert_iff.mp hxfiber with h | h
    · exact Or.inl (h ▸ hfirst)
    · exact Or.inr ((Set.mem_singleton_iff.mp h) ▸ hsecond)
  obtain ⟨W, hWopen, haW, hpre⟩ :=
    exists_open_quotient_neighborhood_of_fiber hUopen hclass
  let V : Set Disk := mk ⁻¹' W
  have hVsat : mk ⁻¹' (mk '' V) = V := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      change mk y ∈ W at hy
      change mk x ∈ W
      rw [← hxy]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hsource : V ⊆
      Set.range (fun p : CollarRadius × CollarAngle => collarPoint i p.1 p.2) ∪
      Set.range (fun p : CollarRadius × CollarAngle =>
        collarPoint (pair i) p.1 p.2) := by
    simpa [V, U, openCollar_eq_collarPoint_range] using hpre
  refine ⟨V, W, hWopen.preimage continuous_mk, hWopen, ?_, ?_, hsource, rfl, hVsat⟩
  · exact haW
  · exact haW

end CurveComplex.Octagon
