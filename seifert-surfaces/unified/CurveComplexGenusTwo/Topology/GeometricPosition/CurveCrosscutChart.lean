import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import CurveComplexGenusTwo.Topology.CompletedJordan
import CurveComplexGenusTwo.Topology.GluedArcBoundary
import Schoenflies.JordanSchoenflies
import Schoenflies.ModelCurve

open Set Topology Schoenflies
open scoped Manifold
namespace CurveComplex
/-- A source-curve-adapted square patch in any prescribed neighborhood.
The chart straightens the actual entire curve inside its source. -/
theorem position_curve_crosscut_chart
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (c : Curve S) (p : S) (hp : p ∈ c.image)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ E : OpenPartialHomeomorph S Schoenflies.Plane,
      p ∈ E.source ∧ E p = 0 ∧ E.source ⊆ W ∧
      Schoenflies.Plane.closedSquare 0 1 ⊆ E.target ∧
      (∀ x ∈ E.source, x ∈ c.image ↔ E x 1 = 0) := by
  classical
  haveI : T2Space S := inferInstance
  have hThreeArc :
      IsArcBetween (sideLeft ∪ (sideBottom ∪ sideRight)) cornerNW cornerNE := by
    apply isArcBetween_sideLeft.concatenate isArcBetween_lowerSides
    rintro z hz (hb | hr)
    · have hx := (mem_sideLeft.mp hz).1
      have hy := (mem_sideBottom.mp hb).1
      ext i
      fin_cases i
      · simpa [cornerSW] using hx
      · simpa [cornerSW] using hy
    · have hx := (mem_sideLeft.mp hz).1
      have hx' := (mem_sideRight.mp hr).1
      linarith
  
  have hThreeMeet :
      (sideLeft ∪ (sideBottom ∪ sideRight)) ∩ sideTop = {cornerNE,cornerNW} := by
    ext z
    constructor
    · rintro ⟨hl | hb | hr,ht⟩
      · right
        exact sideTop_meet_sideLeft z ht hl
      · have h1 := (mem_sideBottom.mp hb).1
        have h2 := (mem_sideTop.mp ht).1
        linarith
      · left
        have hx := (mem_sideRight.mp hr).1
        have hy := (mem_sideTop.mp ht).1
        ext i
        fin_cases i
        · simpa [cornerNE] using hx
        · simpa [cornerNE] using hy
    · rintro (rfl | rfl)
      · exact ⟨hThreeArc.right_mem,isArcBetween_sideTop.left_mem⟩
      · exact ⟨hThreeArc.left_mem,isArcBetween_sideTop.right_mem⟩
  have hplanarMatched {P : Set Schoenflies.Plane} {a b : Schoenflies.Plane}
      (hP : Schoenflies.IsArcBetween P a b) :
      ∃ F : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
        F '' P = Schoenflies.sideTop ∧ F a = Schoenflies.cornerNE ∧ F b = Schoenflies.cornerNW := by
    obtain ⟨A, hA, hmeet, hJ⟩ := Schoenflies.exists_jordan_completion_of_isArcBetween hP
    let B := Schoenflies.sideLeft ∪ (Schoenflies.sideBottom ∪ Schoenflies.sideRight)
    obtain ⟨e, heimage, hea, heb⟩ :=
      Schoenflies.exists_homeomorph_union_arcs_preserving_second hA hP
        hThreeArc.reverse Schoenflies.isArcBetween_sideTop
        hmeet hThreeMeet
    have hmodel : B ∪ Schoenflies.sideTop = Schoenflies.modelCurve := by
      rw [Schoenflies.modelCurve_eq_sides]
      dsimp [B]
      ext z
      simp only [Set.mem_union]
      tauto
    let eModel := e.trans (Homeomorph.setCongr hmodel)
    obtain ⟨F, hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph hJ
      Schoenflies.isJordanCurve_modelCurve eModel
    have hval (z : ↥(A ∪ P)) : F z.val = (e z).val := hF z
    refine ⟨F, ?_, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩
        rw [hval ⟨x, Or.inr hx⟩]
        have hm : (e ⟨x, Or.inr hx⟩).val ∈ Subtype.val ''
            (e '' {z : ↥(A ∪ P) | z.val ∈ P}) :=
          ⟨e ⟨x, Or.inr hx⟩, ⟨⟨x, Or.inr hx⟩, hx, rfl⟩, rfl⟩
        exact heimage.le hm
      · intro y hy
        rw [← heimage] at hy
        obtain ⟨z, ⟨x, hx, rfl⟩, hxy⟩ := hy
        exact ⟨x.val, hx, (hval x).trans hxy⟩
    · exact (hval ⟨a, Or.inl hA.left_mem⟩).trans (congrArg Subtype.val hea)
    · exact (hval ⟨b, Or.inl hA.right_mem⟩).trans (congrArg Subtype.val heb)
  have hplanarLocalFlat {P : Set Schoenflies.Plane} {a b p : Schoenflies.Plane}
      (hP : Schoenflies.IsArcBetween P a b) (hp : p ∈ P) (hpa : p ≠ a) (hpb : p ≠ b) :
      ∃ F : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
        ∃ W : Set Schoenflies.Plane, IsOpen W ∧ p ∈ W ∧
          ∀ z ∈ W, z ∈ P ↔ F z 1 = 1 := by
    obtain ⟨F, hFP, hFa, hFb⟩ := hplanarMatched hP
    have hpTop : F p ∈ Schoenflies.sideTop := hFP ▸ Set.mem_image_of_mem F hp
    have hp1 : F p 1 = 1 := (Schoenflies.mem_sideTop.mp hpTop).1
    have hpbound := abs_le.mp (Schoenflies.mem_sideTop.mp hpTop).2
    have hpstrict : |F p 0| < 1 := by
      apply abs_lt.mpr
      constructor
      · by_contra hn
        have hcoord : F p 0 = -1 := le_antisymm (not_lt.mp hn) hpbound.1
        have heq : F p = Schoenflies.cornerNW := by
          ext i
          fin_cases i
          · simpa [Schoenflies.cornerNW] using hcoord
          · simpa [Schoenflies.cornerNW] using hp1
        exact hpb (F.injective (heq.trans hFb.symm))
      · by_contra hn
        have hcoord : F p 0 = 1 := le_antisymm hpbound.2 (not_lt.mp hn)
        have heq : F p = Schoenflies.cornerNE := by
          ext i
          fin_cases i
          · simpa [Schoenflies.cornerNE] using hcoord
          · simpa [Schoenflies.cornerNE] using hp1
        exact hpa (F.injective (heq.trans hFa.symm))
    let W : Set Schoenflies.Plane := {z | |F z 0| < 1}
    refine ⟨F, W, ?_, hpstrict, ?_⟩
    · exact isOpen_lt ((EuclideanSpace.proj 0).continuous.comp F.continuous).abs continuous_const
    · intro z hz
      constructor
      · intro hzP
        exact (Schoenflies.mem_sideTop.mp (hFP ▸ Set.mem_image_of_mem F hzP)).1
      · intro hz1
        have hm : F z ∈ F '' P := by
          rw [hFP, Schoenflies.mem_sideTop]
          exact ⟨hz1, hz.le⟩
        obtain ⟨y, hy, heq⟩ := hm
        exact F.injective heq ▸ hy
  have hcircleArc (c : Curve S) (p : S) (hp : p ∈ c.image)
      (e : OpenPartialHomeomorph S Schoenflies.Plane) (hpe : p ∈ e.source) :
      ∃ f : ℝ → S, ContinuousOn f unitInterval ∧ Set.InjOn f unitInterval ∧
        Set.MapsTo f unitInterval e.source ∧ f (1/2) = p ∧
        ∃ W : Set S, IsOpen W ∧ p ∈ W ∧ W ⊆ e.source ∧
          ∀ x ∈ W, x ∈ c.image ↔ x ∈ f '' unitInterval := by
    obtain ⟨z, hz⟩ := hp
    let θ : ℝ := Complex.arg (z : ℂ)
    let A : ℝ → S := fun a => c.map (Circle.exp a)
    have hA : Continuous A := c.embedded.continuous.comp Circle.exp.continuous
    have hAθ : A θ = p := by simpa only [A, θ, Circle.exp_arg] using hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (e.open_source.preimage hA) θ (by change A θ ∈ e.source; rwa [hAθ])
    let δ : ℝ := min ε Real.pi / 4
    have hδ : 0 < δ := div_pos (lt_min hε Real.pi_pos) (by norm_num)
    have hδε : δ < ε := by dsimp [δ]; linarith [min_le_left ε Real.pi]
    have hδπ : 2 * δ < 2 * Real.pi := by dsimp [δ]; linarith [min_le_right ε Real.pi, Real.pi_pos]
    let f : ℝ → S := fun t => A (θ - δ + 2 * δ * t)
    have hf : Continuous f := hA.comp (by fun_prop)
    have hparam (t : ℝ) (ht : t ∈ unitInterval) : θ - δ + 2 * δ * t ∈ Set.Icc (θ-δ) (θ+δ) := by
      rcases ht with ⟨ht0, ht1⟩
      constructor <;> nlinarith
    have hfi : Set.InjOn f unitInterval := by
      intro t ht u hu heq
      have hexp := c.embedded.injective heq
      have harg := Circle.exp_injOn_Icc (a := θ-δ) (b := θ+δ) (by linarith)
        (hparam t ht) (hparam u hu) hexp
      nlinarith
    have hfs : Set.MapsTo f unitInterval e.source := by
      intro t ht
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      have hb := hparam t ht
      constructor <;> linarith [hb.1, hb.2]
    have hfm : f (1/2) = p := by
      have hm : θ - δ + 2 * δ * (1/2) = θ := by ring
      simpa only [f, hm] using hAθ
    let J : Set Circle := Circle.exp '' Set.Ioo (θ-δ) (θ+δ)
    have hJ : IsOpen J := isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo
    let bad : Set S := c.map '' Jᶜ
    have hbad : IsClosed bad := ((isCompact_univ : IsCompact (Set.univ : Set Circle)).of_isClosed_subset
      hJ.isClosed_compl (Set.subset_univ _)).image c.embedded.continuous |>.isClosed
    let W : Set S := e.source ∩ badᶜ
    have hpW : p ∈ W := by
      refine ⟨hpe, ?_⟩
      rintro ⟨w, hw, hwp⟩
      have hwz : w = z := c.embedded.injective (hwp.trans hz.symm)
      apply hw
      refine ⟨θ, ⟨by linarith, by linarith⟩, ?_⟩
      simpa only [θ, Circle.exp_arg] using hwz.symm
    refine ⟨f, hf.continuousOn, hfi, hfs, hfm, W, e.open_source.inter hbad.isOpen_compl,
      hpW, Set.inter_subset_left, ?_⟩
    intro x hx
    constructor
    · rintro ⟨w, hw⟩
      have hwJ : w ∈ J := by
        by_contra hn
        exact hx.2 ⟨w, hn, hw⟩
      obtain ⟨a, ha, rfl⟩ := hwJ
      let t : ℝ := (a - (θ-δ)) / (2*δ)
      have ht : t ∈ unitInterval := by
        constructor
        · exact div_nonneg (by linarith [ha.1]) (by positivity)
        · apply (div_le_one (by positivity : 0 < 2*δ)).mpr
          linarith [ha.2]
      refine ⟨t, ht, ?_⟩
      have heq : θ-δ+2*δ*t = a := by dsimp [t]; field_simp; ring
      simpa only [f, A, heq] using hw
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Circle.exp (θ-δ+2*δ*t), rfl⟩
  have hcurveFlatPartial (c : Curve S) (p : S) (hp : p ∈ c.image) :
      ∃ e : OpenPartialHomeomorph S Schoenflies.Plane,
        p ∈ e.source ∧ ∀ x ∈ e.source, x ∈ c.image ↔ e x 1 = 1 := by
    let e := chartAt Schoenflies.Plane p
    obtain ⟨f, hf, hfi, hfs, hfm, W, hW, hpW, hWe, hWcurve⟩ :=
      hcircleArc c p hp e (mem_chart_source _ p)
    let g : ℝ → Schoenflies.Plane := e ∘ f
    have hg : ContinuousOn g unitInterval := e.continuousOn.comp hf hfs
    have hgi : Set.InjOn g unitInterval := by
      intro t ht u hu heq
      exact hfi ht hu (e.injOn (hfs ht) (hfs hu) heq)
    have hArc : Schoenflies.IsArcBetween (g '' unitInterval) (g 0) (g 1) :=
      ⟨g, hg, hgi, rfl, rfl, rfl⟩
    have hmid : g (1/2) ∈ g '' unitInterval := ⟨1/2, by norm_num, rfl⟩
    have hleft : g (1/2) ≠ g 0 := by
      intro heq
      have hh := hgi (by norm_num : (1/2:ℝ) ∈ unitInterval) (by norm_num) heq
      norm_num at hh
    have hright : g (1/2) ≠ g 1 := by
      intro heq
      have hh := hgi (by norm_num : (1/2:ℝ) ∈ unitInterval) (by norm_num) heq
      norm_num at hh
    obtain ⟨F, V, hV, hpV, hflat⟩ := hplanarLocalFlat hArc hmid hleft hright
    let O : Set S := W ∩ (e.source ∩ e ⁻¹' V)
    have hO : IsOpen O := hW.inter (e.isOpen_inter_preimage hV)
    have hpO : p ∈ O := ⟨hpW, hWe hpW, by simpa only [g, Function.comp_apply, hfm, Set.mem_preimage] using hpV⟩
    let E := (e.trans F.toOpenPartialHomeomorph).restr O
    have hsource : E.source = e.source ∩ O := by
      simp only [E, OpenPartialHomeomorph.restr_source, OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ, hO.interior_eq]
    have hEval (x : S) : E x = F (e x) := rfl
    refine ⟨E, ?_, ?_⟩
    · rw [hsource]
      exact ⟨hWe hpW, hpO⟩
    · intro x hx
      rw [hsource] at hx
      rw [hEval]
      have hxW : x ∈ W := hx.2.1
      have hxV : e x ∈ V := hx.2.2.2
      rw [← hflat (e x) hxV, hWcurve x hxW]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, ht, rfl⟩
      · rintro ⟨t, ht, heq⟩
        exact ⟨t, ht, e.injOn (hfs ht) hx.1 heq⟩
  obtain ⟨e, hpe, hflat⟩ := hcurveFlatPartial c p hp
  let er := e.restr W
  have hers : er.source = e.source ∩ W := by
    rw [OpenPartialHomeomorph.restr_source, hW.interior_eq]
  have hper : p ∈ er.source := hers.symm ▸ ⟨hpe, hpW⟩
  let T : Plane ≃ₜ Plane := Homeomorph.addRight (-(e p))
  let E₀ := er.trans T.toOpenPartialHomeomorph
  have hE₀s : E₀.source = er.source := by
    simp [E₀, OpenPartialHomeomorph.trans_source]
  have hE₀val (x : S) : E₀ x = e x - e p := by rfl
  have hpE₀ : p ∈ E₀.source := hE₀s.symm ▸ hper
  have hE₀p : E₀ p = 0 := by rw [hE₀val]; simp
  have h0t : (0 : Plane) ∈ E₀.target := hE₀p ▸ E₀.map_source hpE₀
  obtain ⟨δ, hδ, hδt⟩ := Metric.isOpen_iff.mp E₀.open_target 0 h0t
  let r : ℝ := δ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let u : ℝˣ := Units.mk0 r hr.ne'
  let D : Plane ≃ₜ Plane := Homeomorph.smul u⁻¹
  let E := E₀.trans D.toOpenPartialHomeomorph
  have hEs : E.source = E₀.source := by
    simp [E, OpenPartialHomeomorph.trans_source]
  have hEval (x : S) : E x = r⁻¹ • (e x - e p) := by rfl
  refine ⟨E, hEs.symm ▸ hpE₀, ?_, ?_, ?_, ?_⟩
  · rw [hEval]
    simp
  · intro x hx
    exact (hers ▸ (hE₀s ▸ (hEs ▸ hx))).2
  · intro z hz
    have hzsup : Plane.supNorm z ≤ 1 := mem_closedSquare_zero_one.mp hz
    have hz0 := (Plane.abs_zero_le_supNorm z).trans hzsup
    have hz1 := (Plane.abs_one_le_supNorm z).trans hzsup
    have hzn : ‖z‖ ≤ 2 := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      apply Real.sqrt_le_iff.mpr
      constructor
      · norm_num
      · simp only [Real.norm_eq_abs]
        nlinarith [sq_nonneg (|z 0| - 1), sq_nonneg (|z 1| - 1), abs_nonneg (z 0), abs_nonneg (z 1)]
    have hrzt : r • z ∈ E₀.target := by
      apply hδt
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      calc
        r * ‖z‖ ≤ r * 2 := mul_le_mul_of_nonneg_left hzn hr.le
        _ < δ := by dsimp [r]; linarith
    have hEt : E.target = D '' E₀.target := by
      simp [E, Homeomorph.image_eq_preimage_symm]
    rw [hEt]
    refine ⟨r • z, hrzt, ?_⟩
    change r⁻¹ • (r • z) = z
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  · intro x hx
    have hxe : x ∈ e.source := (hers ▸ (hE₀s ▸ (hEs ▸ hx))).1
    rw [hEval, hflat x hxe]
    have hp1 : e p 1 = 1 := (hflat p hpe).mp hp
    simp only [PiLp.smul_apply, PiLp.sub_apply, hp1]
    constructor
    · intro h
      simp [h]
    · intro h
      have hh : e x 1 - 1 = 0 := (mul_eq_zero.mp h).resolve_left (inv_ne_zero hr.ne')
      exact sub_eq_zero.mp hh
end CurveComplex
