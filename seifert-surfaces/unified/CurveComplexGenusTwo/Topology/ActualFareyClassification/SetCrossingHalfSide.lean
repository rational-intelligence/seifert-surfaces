import CurveComplexGenusTwo.Topology.ActualFareyClassification.FiberBoundaryInterior
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import Mathlib.Analysis.Convex.PathConnected
open Set Topology Metric Schoenflies
namespace CurveComplex
set_option maxHeartbeats 2000000
theorem set_crossing_cannot_stay_in_one_half {S : Type} [TopologicalSpace S] [T2Space S]
    (c d : Set S) (p : S)
    (hc : ∃ (U : Set S) (V : Set (ℝ×ℝ)) (hpU : p∈U) (h : U ≃ₜ V),
      IsOpen U ∧ IsOpen V ∧ ((h ⟨p,hpU⟩ : V) : ℝ×ℝ)=(0,0) ∧
      (∀ (x : S) (hx : x∈U),
        (x∈c ↔ ((h ⟨x,hx⟩ : V) : ℝ×ℝ).1=0) ∧
        (x∈d ↔ ((h ⟨x,hx⟩ : V) : ℝ×ℝ).2=0)))
    (E : OpenPartialHomeomorph S Plane) (hpE : p ∈ E.source) (hEp : E p = 0)
    (ρ σ : ℝ) (hρ : 0 < ρ)
    (haxis : ∀ x ∈ E.source, ‖E x‖ < ρ → (x ∈ c ↔ E x 1 = 0))
    (hhalf : ∀ x ∈ E.source, ‖E x‖ < ρ → x ∈ d → x ≠ p → 0 < σ * E x 1) : False := by
  classical
  obtain ⟨U,V,hpU,h,hU,hV,hpH,haxes⟩ := hc
  have hQ : IsOpen (E.source ∩ U) := E.open_source.inter hU
  have hImageQ : IsOpen (E '' (E.source ∩ U)) := E.isOpen_image_of_subset_source hQ Set.inter_subset_left
  have h0ImageQ : (0 : Plane) ∈ E '' (E.source ∩ U) := ⟨p,⟨hpE,hpU⟩,hEp⟩
  obtain ⟨r₀,hr₀,hr₀Q⟩ := Metric.isOpen_iff.mp hImageQ 0 h0ImageQ
  let r := min r₀ ρ / 2
  have hr : 0 < r := half_pos (lt_min hr₀ hρ)
  have hrr₀ : r < r₀ := by dsimp [r]; linarith [min_le_left r₀ ρ]
  have hrρ : r < ρ := by dsimp [r]; linarith [min_le_right r₀ ρ]
  have hBallData (y : Plane) (hy : y ∈ Metric.ball (0 : Plane) r) :
      y ∈ E.target ∧ E.symm y ∈ U ∧ E.symm y ∈ E.source := by
    obtain ⟨x,hx,hxy⟩ := hr₀Q (Metric.ball_subset_ball hrr₀.le hy)
    have hyT : y ∈ E.target := hxy ▸ E.map_source hx.1
    have he : E.symm y = x := by rw [← hxy]; exact E.left_inv hx.1
    exact ⟨hyT,he ▸ hx.2,he ▸ hx.1⟩
  let P : Set Plane := Metric.ball (0 : Plane) r ∩ {y | 0 < σ * y 1}
  have hP : IsPreconnected P := (convex_ball (0 : Plane) r).inter
    (convex_halfSpace_gt (𝕜 := ℝ) (f := fun y : Plane => σ * y 1)
      ⟨by intros x y; change σ * (x 1 + y 1) = σ*x 1 + σ*y 1; ring,
       by intros a x; change σ * (a*x 1) = a*(σ*x 1); ring⟩ 0) |>.isPreconnected
  have hPU (y : P) : E.symm y.val ∈ U := (hBallData y.val y.property.1).2.1
  let Q : P → U := fun y => ⟨E.symm y.val,hPU y⟩
  have hQc : Continuous Q := (E.symm.continuousOn.comp_continuous continuous_subtype_val
    (fun y => (hBallData y.val y.property.1).1)).subtype_mk _
  let F : P → ℝ := fun y => ((h (Q y) : V) : ℝ × ℝ).1
  have hF : Continuous F := continuous_fst.comp
    (continuous_subtype_val.comp (h.continuous.comp hQc))
  have hFne (y : P) : F y ≠ 0 := by
    intro he
    have hcX : E.symm y.val ∈ c := (haxes _ (hPU y)).1.mpr he
    have hxy : E (E.symm y.val) = y.val := E.right_inv (hBallData y.val y.property.1).1
    have hyρ : ‖E (E.symm y.val)‖ < ρ := by
      rw [hxy]
      have hh : ‖y.val‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using y.property.1
      exact hh.trans hrρ
    have hy0 := (haxis _ (hBallData y.val y.property.1).2.2 hyρ).mp hcX
    rw [hxy] at hy0
    have hh := y.property.2
    change 0 < σ * y.val 1 at hh
    rw [hy0,mul_zero] at hh
    exact (lt_irrefl 0) hh
  let O : Set V := (fun y : V => (h.symm y : S)) ⁻¹'
    (E.source ∩ E ⁻¹' Metric.ball (0 : Plane) r)
  have hO : IsOpen O := (E.isOpen_inter_preimage isOpen_ball).preimage
    (continuous_subtype_val.comp h.symm.continuous)
  have hGlobalO : IsOpen (Subtype.val '' O : Set (ℝ × ℝ)) := hV.isOpenEmbedding_subtypeVal.isOpenMap _ hO
  have h0O : ((0,0) : ℝ × ℝ) ∈ Subtype.val '' O := by
    refine ⟨h ⟨p,hpU⟩,?_,hpH⟩
    change (h.symm (h ⟨p,hpU⟩) : S) ∈ E.source ∩ E ⁻¹' Metric.ball (0 : Plane) r
    simp only [h.symm_apply_apply]
    exact ⟨hpE,by change E p ∈ Metric.ball (0 : Plane) r; rw [hEp]; simpa using hr⟩
  obtain ⟨δ,hδ,hδO⟩ := Metric.isOpen_iff.mp hGlobalO (0,0) h0O
  have hpm (s : ℝ) (hs : s = -δ/2 ∨ s = δ/2) : (s,0) ∈ Metric.ball (0 : ℝ × ℝ) δ := by
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    constructor
    · rw [Real.dist_eq]
      change |s-0| < δ
      rw [sub_zero]
      rcases hs with rfl | rfl <;> rw [abs_div] <;> simp [abs_of_pos hδ,abs_of_neg (neg_neg_of_pos hδ)] <;> linarith
    · simpa using hδ
  have hPoint (s : ℝ) (hs : s = -δ/2 ∨ s = δ/2) :
      ∃ y : P, F y = s := by
    obtain ⟨v,hv,hvs⟩ := hδO (hpm s hs)
    have hxE : (h.symm v : S) ∈ E.source := hv.1
    have hxBall : E (h.symm v : S) ∈ Metric.ball (0 : Plane) r := hv.2
    have hxNr : ‖E (h.symm v : S)‖ < r := by
      simpa only [Metric.mem_ball,dist_zero_right] using hxBall
    have hxN : ‖E (h.symm v : S)‖ < ρ := hxNr.trans hrρ
    have hHvalue : ((h ⟨(h.symm v : S),(h.symm v).property⟩ : V) : ℝ × ℝ) = (s,0) := by
      simpa using hvs
    have hxd : (h.symm v : S) ∈ d := (haxes _ (h.symm v).property).2.mpr (by rw [hHvalue])
    have hxp : (h.symm v : S) ≠ p := by
      intro he
      have hv0 : ((h ⟨(h.symm v : S),(h.symm v).property⟩ : V) : ℝ × ℝ) = (0,0) := by
        convert hpH using 1
        congr 2
        exact Subtype.ext he
      have hs0 : s = 0 := congrArg Prod.fst (hHvalue.symm.trans hv0)
      rcases hs with hs | hs <;> linarith
    have hxUp := hhalf _ hxE hxN hxd hxp
    let y : P := ⟨E (h.symm v : S),⟨hxBall,hxUp⟩⟩
    refine ⟨y,?_⟩
    have hQy : Q y = h.symm v := by
      apply Subtype.ext
      exact E.left_inv hxE
    change ((h (Q y) : V) : ℝ × ℝ).1 = s
    rw [hQy]
    simpa using congrArg Prod.fst hvs
  obtain ⟨yn,hyn⟩ := hPoint (-δ/2) (Or.inl rfl)
  obtain ⟨yp,hyp⟩ := hPoint (δ/2) (Or.inr rfl)
  have hRangeConn : IsPreconnected (Set.range F) := by
    have : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp hP
    exact isPreconnected_range hF
  have hRangeSub : Set.range F ⊆ Set.Iio 0 ∪ Set.Ioi 0 := by
    rintro x ⟨y,rfl⟩
    exact lt_or_gt_of_ne (hFne y)
  have hLeft : Set.range F ⊆ Set.Iio 0 :=
    hRangeConn.subset_left_of_subset_union isOpen_Iio isOpen_Ioi
      (Set.disjoint_left.mpr (by intro x hx hy; change x < 0 at hx; change 0 < x at hy; linarith)) hRangeSub
      ⟨F yn,⟨⟨yn,rfl⟩,by change F yn < 0; rw [hyn]; linarith⟩⟩
  have hbad := hLeft ⟨yp,rfl⟩
  change F yp < 0 at hbad
  rw [hyp] at hbad
  linarith
end CurveComplex

#print axioms CurveComplex.set_crossing_cannot_stay_in_one_half
