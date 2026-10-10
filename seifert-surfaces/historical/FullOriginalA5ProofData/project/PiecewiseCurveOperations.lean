import DiagramGeometry
import Mathlib.Geometry.Manifold.Instances.Icc

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers
open Foundations
noncomputable section

/-! C1--C4 from plan_longitude_rounding/PLAN.md. All proof fields and theorem
proofs are pending review/proof obligations. The operative maps are explicit. -/

structure AffineTimeWindow where
  left : ℝ
  right : ℝ
  left_nonneg : 0 ≤ left
  right_le_one : right ≤ 1
  increasing : left < right

def affineTime (w : AffineTimeWindow) (t : Time) : Time :=
  ⟨w.left + (w.right - w.left) * (t : ℝ), by
    have hp : 0 ≤ w.right - w.left := sub_nonneg.mpr w.increasing.le
    have h₀ := mul_nonneg hp t.property.1
    have h₁ := mul_le_mul_of_nonneg_left t.property.2 hp
    constructor <;> linarith [w.left_nonneg, w.right_le_one]⟩

def reflectTime (t : Time) : Time := ⟨1 - (t : ℝ), by
  constructor <;> linarith [t.property.1, t.property.2]⟩

def firstHalfWindow : AffineTimeWindow where
  left := 0
  right := 1 / 2
  left_nonneg := by norm_num
  right_le_one := by norm_num
  increasing := by norm_num

def secondHalfWindow : AffineTimeWindow where
  left := 1 / 2
  right := 1
  left_nonneg := by norm_num
  right_le_one := by norm_num
  increasing := by norm_num

def affineCylinder {Y : Type*} (w : AffineTimeWindow) (p : Time × Y) : Time × Y :=
  (affineTime w p.1, p.2)

def reflectCylinder {Y : Type*} (p : Time × Y) : Time × Y :=
  (reflectTime p.1, p.2)

theorem affineTime_properties (w : AffineTimeWindow) :
    IsEmbedding (affineTime w) ∧ ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ (affineTime w) ∧
    (∀ t, Function.Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1) (affineTime w) t)) ∧
    (∀ t : ℝ, HasDerivAt (fun u => w.left + (w.right - w.left) * u)
      (w.right - w.left) t) ∧ w.right - w.left ≠ 0 ∧
    (Set.range (fun t : Time => (affineTime w t : ℝ))) = Icc w.left w.right := by
  have hc : 0 < w.right - w.left := sub_pos.mpr w.increasing
  have hv : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (Subtype.val : Time → ℝ) :=
    contMDiff_subtypeVal_Icc
  have ha : Continuous (affineTime w) := by
    unfold affineTime
    fun_prop
  have hs : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ (affineTime w) := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨ha, ?_⟩
    have hr : ContDiff ℝ ∞ (fun x : ℝ => w.left + (w.right - w.left) * x) := by fun_prop
    exact hr.comp_contMDiff hv
  have hi : Function.Injective (affineTime w) := by
    intro s t he
    apply Subtype.ext
    have he' := congrArg Subtype.val he
    change w.left + (w.right - w.left) * (s : ℝ) =
      w.left + (w.right - w.left) * (t : ℝ) at he'
    nlinarith
  refine ⟨(ha.isClosedEmbedding hi).isEmbedding, hs, ?_, ?_, ne_of_gt hc, ?_⟩
  · intro t
    have hd := (hv.mdifferentiableAt (by simp) (x := t)).hasMFDerivAt
    have hda := (hasMFDerivAt_const w.left t).add (hd.const_smul (w.right - w.left))
    have hdv := (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1)
      (n := ∞)).isImmersion.mfderiv_injective (by simp) t
    intro u v he
    apply hdv
    have he' := congrArg
      (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Time → ℝ) (affineTime w t)) he
    have hcomp := mfderiv_comp t (hv.mdifferentiableAt (by simp))
      (hs.mdifferentiableAt (by simp))
    have hf : (Subtype.val : Time → ℝ) ∘ affineTime w =
        (fun _ : Time => w.left) + (w.right - w.left) • (Subtype.val : Time → ℝ) := rfl
    rw [hf, hda.mfderiv] at hcomp
    let D : TangentSpace (𝓡∂ 1) t →L[ℝ] ℝ := by
      exact mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Time → ℝ) t
    change D u = D v
    have he'' : (0 + (w.right - w.left) • D) u =
        (0 + (w.right - w.left) • D) v := by
      exact
        (congrArg (fun L => L u) hcomp).trans (he'.trans (congrArg (fun L => L v) hcomp).symm)
    apply mul_left_cancel₀ (ne_of_gt hc)
    simpa using he''
  · intro t
    simpa using ((hasDerivAt_id t).const_mul (w.right - w.left)).const_add w.left
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      have h₀ := mul_nonneg hc.le t.property.1
      have h₁ := mul_le_mul_of_nonneg_left t.property.2 hc.le
      constructor <;> dsimp [affineTime] <;> linarith
    · intro hx
      refine ⟨⟨(x - w.left) / (w.right - w.left), ?_⟩, ?_⟩
      · constructor
        · exact div_nonneg (sub_nonneg.mpr hx.1) hc.le
        · apply (div_le_iff₀ hc).mpr
          linarith [hx.2]
      · dsimp [affineTime]
        field_simp
        ring

theorem reflectTime_properties :
    IsEmbedding reflectTime ∧ ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ reflectTime ∧
    (∀ t, Function.Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1) reflectTime t)) ∧
    (∀ t, reflectTime (reflectTime t) = t) ∧
    reflectTime 0 = 1 ∧ reflectTime 1 = 0 ∧
    (∀ t : ℝ, HasDerivAt (fun u => 1 - u) (-1) t) := by
  have hv : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (Subtype.val : Time → ℝ) :=
    contMDiff_subtypeVal_Icc
  have ha : Continuous reflectTime := by unfold reflectTime; fun_prop
  have hs : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ reflectTime := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    exact ⟨ha, contMDiff_const.sub hv⟩
  have hr : ∀ t, reflectTime (reflectTime t) = t := by
    intro t
    apply Subtype.ext
    dsimp [reflectTime]
    ring
  have hi : Function.Injective reflectTime := Function.LeftInverse.injective hr
  refine ⟨(ha.isClosedEmbedding hi).isEmbedding, hs, ?_, hr, ?_, ?_, ?_⟩
  · intro t u v he
    have hcomp := mfderiv_comp t (hs.mdifferentiableAt (by simp))
      (hs.mdifferentiableAt (by simp))
    have hfun : reflectTime ∘ reflectTime = id := funext hr
    rw [hfun, mfderiv_id] at hcomp
    have he' := congrArg (mfderiv (𝓡∂ 1) (𝓡∂ 1) reflectTime (reflectTime t)) he
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      (congrArg (fun L => L u) hcomp).trans (he'.trans (congrArg (fun L => L v) hcomp).symm)
  · apply Subtype.ext
    norm_num [reflectTime]
  · apply Subtype.ext
    norm_num [reflectTime]
  · intro t
    convert! (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) using 1 <;> simp

theorem affineCylinder_circle_properties (w : AffineTimeWindow) :
    IsEmbedding (affineCylinder (Y := Circle) w) ∧
    ContMDiff ((𝓡∂ 1).prod (𝓡 1)) ((𝓡∂ 1).prod (𝓡 1)) ∞
      (affineCylinder (Y := Circle) w) ∧
    (∀ p, Function.Injective (mfderiv ((𝓡∂ 1).prod (𝓡 1))
      ((𝓡∂ 1).prod (𝓡 1)) (affineCylinder (Y := Circle) w) p)) := by
  rcases affineTime_properties w with ⟨he, hs, hi, _⟩
  refine ⟨he.prodMap IsEmbedding.id, hs.prodMap contMDiff_id, ?_⟩
  intro p
  change Function.Injective (mfderiv _ _ (Prod.map (affineTime w) id) p)
  rw [mfderiv_prodMap (hs.mdifferentiableAt (by simp)) mdifferentiableAt_id, mfderiv_id]
  intro u v huv
  apply Prod.ext
  · apply hi p.1
    exact congrArg Prod.fst huv
  · exact congrArg (fun x => x.2) huv

theorem affineCylinder_euclidean_properties (w : AffineTimeWindow) :
    IsEmbedding (affineCylinder (Y := Euc 3) w) ∧
    ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) ∞
      (affineCylinder (Y := Euc 3) w) ∧
    (∀ p, Function.Injective (mfderiv ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3))
      ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) (affineCylinder (Y := Euc 3) w) p)) := by
  rcases affineTime_properties w with ⟨he, hs, hi, _⟩
  refine ⟨he.prodMap IsEmbedding.id, hs.prodMap contMDiff_id, ?_⟩
  intro p
  change Function.Injective (mfderiv _ _ (Prod.map (affineTime w) id) p)
  rw [mfderiv_prodMap (hs.mdifferentiableAt (by simp)) mdifferentiableAt_id, mfderiv_id]
  intro u v huv
  apply Prod.ext
  · apply hi p.1
    exact congrArg Prod.fst huv
  · exact congrArg (fun x => x.2) huv

theorem reflectCylinder_circle_properties :
    IsEmbedding (reflectCylinder (Y := Circle)) ∧
    ContMDiff ((𝓡∂ 1).prod (𝓡 1)) ((𝓡∂ 1).prod (𝓡 1)) ∞
      (reflectCylinder (Y := Circle)) ∧
    (∀ p, Function.Injective (mfderiv ((𝓡∂ 1).prod (𝓡 1))
      ((𝓡∂ 1).prod (𝓡 1)) (reflectCylinder (Y := Circle)) p)) := by
  rcases reflectTime_properties with ⟨he, hs, hi, _⟩
  refine ⟨he.prodMap IsEmbedding.id, hs.prodMap contMDiff_id, ?_⟩
  intro p
  change Function.Injective (mfderiv _ _ (Prod.map reflectTime id) p)
  rw [mfderiv_prodMap (hs.mdifferentiableAt (by simp)) mdifferentiableAt_id, mfderiv_id]
  intro u v huv
  apply Prod.ext
  · apply hi p.1
    exact congrArg Prod.fst huv
  · exact congrArg (fun x => x.2) huv

theorem reflectCylinder_euclidean_properties :
    IsEmbedding (reflectCylinder (Y := Euc 3)) ∧
    ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) ∞
      (reflectCylinder (Y := Euc 3)) ∧
    (∀ p, Function.Injective (mfderiv ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3))
      ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) (reflectCylinder (Y := Euc 3)) p)) := by
  rcases reflectTime_properties with ⟨he, hs, hi, _⟩
  refine ⟨he.prodMap IsEmbedding.id, hs.prodMap contMDiff_id, ?_⟩
  intro p
  change Function.Injective (mfderiv _ _ (Prod.map reflectTime id) p)
  rw [mfderiv_prodMap (hs.mdifferentiableAt (by simp)) mdifferentiableAt_id, mfderiv_id]
  intro u v huv
  apply Prod.ext
  · apply hi p.1
    exact congrArg Prod.fst huv
  · exact congrArg (fun x => x.2) huv

namespace PiecewiseCurveIsotopy

def reverse {f g : Circle → Euc 3} (H : PiecewiseCurveIsotopy f g) :
    PiecewiseCurveIsotopy g f where
  stage t := H.stage (reflectTime t)
  embedding := by exact fun t => H.embedding (reflectTime t)
  continuous_family := by
    exact H.continuous_family.comp reflectCylinder_circle_properties.1.continuous
  initial := by
    change (H.stage (reflectTime 0) : Circle → Euc 3) = g
    rw [reflectTime_properties.2.2.2.2.1]
    exact H.terminal
  terminal := by
    change (H.stage (reflectTime 1) : Circle → Euc 3) = f
    rw [reflectTime_properties.2.2.2.2.2.1]
    exact H.initial
  count := H.count
  coordinate i := ⟨reflectCylinder ∘ H.coordinate i, by
    exact reflectCylinder_circle_properties.1.continuous.comp (H.coordinate i).continuous⟩
  coordinate_embedding := by
    intro i
    exact reflectCylinder_circle_properties.1.comp (H.coordinate_embedding i)
  source_regular := by
    intro i
    exact (reflectCylinder_circle_properties.2.1.of_le (by simp)).comp (H.source_regular i)
  source_injective := by
    intro i p
    change Function.Injective (mfderiv _ _ (reflectCylinder ∘ H.coordinate i) p)
    rw [mfderiv_comp p (reflectCylinder_circle_properties.2.1.mdifferentiableAt (by simp))
      ((H.source_regular i).mdifferentiableAt (by simp))]
    exact (reflectCylinder_circle_properties.2.2 (H.coordinate i p)).comp (H.source_injective i p)
  covers := by
    apply Set.eq_univ_of_forall
    intro p
    have hp : reflectCylinder p ∈ ⋃ i, Set.range (H.coordinate i) := by rw [H.covers]; trivial
    rcases Set.mem_iUnion.mp hp with ⟨i, q, hq⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, q, ?_⟩
    change reflectCylinder (H.coordinate i q) = p
    rw [hq]
    apply Prod.ext
    · exact reflectTime_properties.2.2.2.1 p.1
    · rfl
  target_regular := by
    intro i
    have heq : (fun p : Time × Time =>
        ((reflectCylinder (H.coordinate i p)).1,
          H.stage (reflectTime (reflectCylinder (H.coordinate i p)).1)
            (reflectCylinder (H.coordinate i p)).2)) =
        reflectCylinder ∘ (fun p => ((H.coordinate i p).1,
          H.stage (H.coordinate i p).1 (H.coordinate i p).2)) := by
      funext p
      dsimp [reflectCylinder]
      rw [reflectTime_properties.2.2.2.1]
    dsimp only [ContinuousMap.coe_mk, Function.comp_apply]
    rw [heq]
    exact (reflectCylinder_euclidean_properties.2.1.of_le (by simp)).comp (H.target_regular i)
  target_injective := by
    intro i p
    have heq : (fun q : Time × Time =>
        ((reflectCylinder (H.coordinate i q)).1,
          H.stage (reflectTime (reflectCylinder (H.coordinate i q)).1)
            (reflectCylinder (H.coordinate i q)).2)) =
        reflectCylinder ∘ (fun q => ((H.coordinate i q).1,
          H.stage (H.coordinate i q).1 (H.coordinate i q).2)) := by
      funext q
      dsimp [reflectCylinder]
      rw [reflectTime_properties.2.2.2.1]
    dsimp only [ContinuousMap.coe_mk, Function.comp_apply]
    rw [heq, mfderiv_comp p (reflectCylinder_euclidean_properties.2.1.mdifferentiableAt (by simp))
      ((H.target_regular i).mdifferentiableAt (by simp))]
    exact (reflectCylinder_euclidean_properties.2.2 _).comp (H.target_injective i p)
  smooth_interiors := by
    intro i
    have heq : (fun p : Time × Time =>
        ((reflectCylinder (H.coordinate i p)).1,
          H.stage (reflectTime (reflectCylinder (H.coordinate i p)).1)
            (reflectCylinder (H.coordinate i p)).2)) =
        reflectCylinder ∘ (fun p => ((H.coordinate i p).1,
          H.stage (H.coordinate i p).1 (H.coordinate i p).2)) := by
      funext p
      dsimp [reflectCylinder]
      rw [reflectTime_properties.2.2.2.1]
    dsimp only [ContinuousMap.coe_mk, Function.comp_apply]
    rw [heq]
    exact reflectCylinder_euclidean_properties.2.1.comp_contMDiffOn (H.smooth_interiors i)

def concatenateStage {f g h : Circle → Euc 3}
    (H : PiecewiseCurveIsotopy f g) (J : PiecewiseCurveIsotopy g h)
    (t : Time) : C(Circle, Euc 3) :=
  if ht : (t : ℝ) ≤ 1 / 2 then H.stage ⟨2 * (t : ℝ), by
    constructor <;> linarith [t.property.1, t.property.2]⟩
  else J.stage ⟨2 * (t : ℝ) - 1, by
    constructor <;> linarith [t.property.1, t.property.2]⟩

def concatenate {f g h : Circle → Euc 3}
    (H : PiecewiseCurveIsotopy f g) (J : PiecewiseCurveIsotopy g h) :
    PiecewiseCurveIsotopy f h where
  stage := concatenateStage H J
  embedding := by
    intro t
    unfold concatenateStage
    split_ifs
    · exact H.embedding _
    · exact J.embedding _
  continuous_family := by
    let A (p : Time × Circle) := H.stage (Set.projIcc 0 1 zero_le_one (2 * (p.1 : ℝ))) p.2
    let B (p : Time × Circle) := J.stage (Set.projIcc 0 1 zero_le_one (2 * (p.1 : ℝ) - 1)) p.2
    have hA : Continuous A := by
      change Continuous ((fun p : Time × Circle => H.stage p.1 p.2) ∘
        (fun p : Time × Circle => (Set.projIcc 0 1 zero_le_one (2 * (p.1 : ℝ)), p.2)))
      exact H.continuous_family.comp (by fun_prop)
    have hB : Continuous B := by
      change Continuous ((fun p : Time × Circle => J.stage p.1 p.2) ∘
        (fun p : Time × Circle => (Set.projIcc 0 1 zero_le_one (2 * (p.1 : ℝ) - 1), p.2)))
      exact J.continuous_family.comp (by fun_prop)
    have hjoin : ∀ p : Time × Circle, (p.1 : ℝ) = 1 / 2 → A p = B p := by
      intro p hp
      have ht1 : Set.projIcc 0 1 zero_le_one (2 * (p.1 : ℝ)) = (1 : Time) := by
        apply Subtype.ext
        norm_num [hp, Set.projIcc]
      have ht0 : Set.projIcc 0 1 zero_le_one (2 * (p.1 : ℝ) - 1) = (0 : Time) := by
        apply Subtype.ext
        norm_num [hp, Set.projIcc]
      dsimp [A, B]
      rw [ht1, ht0]
      exact congrFun (H.terminal.trans J.initial.symm) p.2
    have hcont := Continuous.if_le hA hB
      (continuous_subtype_val.comp continuous_fst) continuous_const hjoin
    apply hcont.congr
    intro p
    change (if (p.1 : ℝ) ≤ 1 / 2 then A p else B p) = concatenateStage H J p.1 p.2
    unfold concatenateStage
    split_ifs with ht
    · dsimp [A]
      have hm : 2 * (p.1 : ℝ) ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [p.1.property.1]
      rw [Set.projIcc_of_mem zero_le_one hm]
    · dsimp [B]
      have hm : 2 * (p.1 : ℝ) - 1 ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [p.1.property.2]
      rw [Set.projIcc_of_mem zero_le_one hm]
  initial := by
    change (concatenateStage H J 0 : Circle → Euc 3) = f
    simpa [concatenateStage] using H.initial
  terminal := by
    change (concatenateStage H J 1 : Circle → Euc 3) = h
    unfold concatenateStage
    split_ifs with ht
    · norm_num at ht
    · convert J.terminal using 1
      congr 2
      apply Subtype.ext
      norm_num
  count := H.count + J.count
  coordinate i := Fin.addCases
    (fun j => ⟨affineCylinder firstHalfWindow ∘ H.coordinate j, by
      change Continuous (affineCylinder (Y := Circle) firstHalfWindow ∘ H.coordinate j)
      exact (affineCylinder_circle_properties firstHalfWindow).1.continuous.comp
        (H.coordinate j).continuous⟩)
    (fun j => ⟨affineCylinder secondHalfWindow ∘ J.coordinate j, by
      change Continuous (affineCylinder (Y := Circle) secondHalfWindow ∘ J.coordinate j)
      exact (affineCylinder_circle_properties secondHalfWindow).1.continuous.comp
        (J.coordinate j).continuous⟩) i
  coordinate_embedding := by
    run_tac
      let pending ← Lean.Meta.getMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)
      let pending ← pending.mapM Lean.getDelayedMVarRoot
      (do
        modify fun s => { s with pendingMVars := pending.toList ++ s.pendingMVars }
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
        : Lean.Elab.TermElabM Unit)
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left, ContinuousMap.coe_mk]
      change IsEmbedding (affineCylinder firstHalfWindow ∘ H.coordinate j)
      exact (affineCylinder_circle_properties firstHalfWindow).1.comp (H.coordinate_embedding j)
    · simp only [Fin.addCases_right, ContinuousMap.coe_mk]
      change IsEmbedding (affineCylinder secondHalfWindow ∘ J.coordinate j)
      exact (affineCylinder_circle_properties secondHalfWindow).1.comp (J.coordinate_embedding j)
  source_regular := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left, ContinuousMap.coe_mk]
      change ContMDiff _ _ 1 (affineCylinder firstHalfWindow ∘ H.coordinate j)
      exact ((affineCylinder_circle_properties firstHalfWindow).2.1.of_le (by simp)).comp
          (H.source_regular j)
    · simp only [Fin.addCases_right, ContinuousMap.coe_mk]
      change ContMDiff _ _ 1 (affineCylinder secondHalfWindow ∘ J.coordinate j)
      exact ((affineCylinder_circle_properties secondHalfWindow).2.1.of_le (by simp)).comp
          (J.source_regular j)
  source_injective := by
    let A (j : Fin H.count) : C(Time × Time, Time × Circle) :=
      ⟨affineCylinder firstHalfWindow ∘ H.coordinate j,
        (affineCylinder_circle_properties firstHalfWindow).1.continuous.comp (H.coordinate j).continuous⟩
    let B (j : Fin J.count) : C(Time × Time, Time × Circle) :=
      ⟨affineCylinder secondHalfWindow ∘ J.coordinate j,
        (affineCylinder_circle_properties secondHalfWindow).1.continuous.comp (J.coordinate j).continuous⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · intro p
      have hcoord : (Fin.addCases A B (Fin.castAdd J.count j) : C(Time × Time, Time × Circle)) = A j :=
        Fin.addCases_left j
      have hd := mfderiv_congr (I := ((𝓡∂ 1).prod (𝓡∂ 1)))
        (I' := ((𝓡∂ 1).prod (𝓡 1))) (x := p)
        (congrArg (fun c : C(Time × Time, Time × Circle) => (c : Time × Time → Time × Circle)) hcoord)
      change Function.Injective
        (mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) ((𝓡∂ 1).prod (𝓡 1))
          (show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.castAdd J.count j)) p)
      rw [hd]
      change Function.Injective
        (mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) ((𝓡∂ 1).prod (𝓡 1))
          (affineCylinder firstHalfWindow ∘ H.coordinate j) p)
      rw [mfderiv_comp p
        ((affineCylinder_circle_properties firstHalfWindow).2.1.mdifferentiableAt (by simp))
        ((H.source_regular j).mdifferentiableAt (by simp))]
      exact ((affineCylinder_circle_properties firstHalfWindow).2.2 _).comp
        (H.source_injective j p)
    · intro p
      have hcoord : (Fin.addCases A B (Fin.natAdd H.count j) : C(Time × Time, Time × Circle)) = B j :=
        Fin.addCases_right j
      have hd := mfderiv_congr (I := ((𝓡∂ 1).prod (𝓡∂ 1)))
        (I' := ((𝓡∂ 1).prod (𝓡 1))) (x := p)
        (congrArg (fun c : C(Time × Time, Time × Circle) => (c : Time × Time → Time × Circle)) hcoord)
      change Function.Injective
        (mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) ((𝓡∂ 1).prod (𝓡 1))
          (show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.natAdd H.count j)) p)
      rw [hd]
      change Function.Injective
        (mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) ((𝓡∂ 1).prod (𝓡 1))
          (affineCylinder secondHalfWindow ∘ J.coordinate j) p)
      rw [mfderiv_comp p
        ((affineCylinder_circle_properties secondHalfWindow).2.1.mdifferentiableAt (by simp))
        ((J.source_regular j).mdifferentiableAt (by simp))]
      exact ((affineCylinder_circle_properties secondHalfWindow).2.2 _).comp
        (J.source_injective j p)
  covers := by
    apply Set.eq_univ_of_forall
    intro p
    by_cases ht : (p.1 : ℝ) ≤ 1 / 2
    · let t : Time := ⟨2 * (p.1 : ℝ), by
        constructor <;> linarith [p.1.property.1]⟩
      have hp : (t, p.2) ∈ ⋃ i, Set.range (H.coordinate i) := by rw [H.covers]; trivial
      rcases Set.mem_iUnion.mp hp with ⟨i, q, hq⟩
      apply Set.mem_iUnion.mpr
      refine ⟨Fin.castAdd J.count i, q, ?_⟩
      try simp only [Fin.addCases_left, ContinuousMap.coe_mk, Function.comp_apply]
      change affineCylinder firstHalfWindow (H.coordinate i q) = p
      rw [hq]
      apply Prod.ext
      · apply Subtype.ext
        dsimp [affineCylinder, affineTime, firstHalfWindow, t]
        ring
      · rfl
    · let t : Time := ⟨2 * (p.1 : ℝ) - 1, by
        constructor <;> linarith [p.1.property.2]⟩
      have hp : (t, p.2) ∈ ⋃ i, Set.range (J.coordinate i) := by rw [J.covers]; trivial
      rcases Set.mem_iUnion.mp hp with ⟨i, q, hq⟩
      apply Set.mem_iUnion.mpr
      refine ⟨Fin.natAdd H.count i, q, ?_⟩
      try simp only [Fin.addCases_right, ContinuousMap.coe_mk, Function.comp_apply]
      change affineCylinder secondHalfWindow (J.coordinate i q) = p
      rw [hq]
      apply Prod.ext
      · apply Subtype.ext
        dsimp [affineCylinder, affineTime, secondHalfWindow, t]
        ring
      · rfl
  target_regular := by
    have hfirst : ∀ t : Time, concatenateStage H J (affineTime firstHalfWindow t) = H.stage t := by
      intro t
      have ht : (affineTime firstHalfWindow t : ℝ) ≤ 1 / 2 := by
        dsimp [affineTime, firstHalfWindow]
        linarith [t.property.2]
      unfold concatenateStage
      rw [dif_pos ht]
      congr 1
      apply Subtype.ext
      dsimp [affineTime, firstHalfWindow]
      ring
    have hsecond : ∀ t : Time, concatenateStage H J (affineTime secondHalfWindow t) = J.stage t := by
      intro t
      unfold concatenateStage
      split_ifs with ht
      · have ht0 : t = 0 := by
          apply Subtype.ext
          change (t : ℝ) = 0
          dsimp [affineTime, secondHalfWindow] at ht
          linarith [t.property.1]
        have ht1 : (⟨2 * (affineTime secondHalfWindow t : ℝ), by
            constructor <;> dsimp [affineTime, secondHalfWindow] at ht ⊢ <;>
              linarith [t.property.1, t.property.2]⟩ : Time) = 1 := by
          apply Subtype.ext
          change 2 * (affineTime secondHalfWindow t : ℝ) = 1
          have ht0' : (t : ℝ) = 0 := congrArg Subtype.val ht0
          norm_num [affineTime, secondHalfWindow, ht0']
        rw [ht1, ht0]
        apply DFunLike.ext
        intro z
        exact congrFun (H.terminal.trans J.initial.symm) z
      · congr 1
        apply Subtype.ext
        dsimp [affineTime, secondHalfWindow]
        ring
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have heq : (fun q : Time × Time =>
          ((affineCylinder firstHalfWindow (H.coordinate j q)).1,
            concatenateStage H J (affineCylinder firstHalfWindow (H.coordinate j q)).1
              (affineCylinder firstHalfWindow (H.coordinate j q)).2)) =
          affineCylinder firstHalfWindow ∘ (fun q => ((H.coordinate j q).1,
            H.stage (H.coordinate j q).1 (H.coordinate j q).2)) := by
        funext q
        dsimp only [affineCylinder, Function.comp_apply]
        rw [hfirst]
      try simp only [Fin.addCases_left, ContinuousMap.coe_mk, Function.comp_apply]
      rw [heq]
      exact ((affineCylinder_euclidean_properties firstHalfWindow).2.1.of_le (by simp)).comp
        (H.target_regular j)
    · have heq : (fun q : Time × Time =>
          ((affineCylinder secondHalfWindow (J.coordinate j q)).1,
            concatenateStage H J (affineCylinder secondHalfWindow (J.coordinate j q)).1
              (affineCylinder secondHalfWindow (J.coordinate j q)).2)) =
          affineCylinder secondHalfWindow ∘ (fun q => ((J.coordinate j q).1,
            J.stage (J.coordinate j q).1 (J.coordinate j q).2)) := by
        funext q
        dsimp only [affineCylinder, Function.comp_apply]
        rw [hsecond]
      try simp only [Fin.addCases_right, ContinuousMap.coe_mk, Function.comp_apply]
      rw [heq]
      exact ((affineCylinder_euclidean_properties secondHalfWindow).2.1.of_le (by simp)).comp
        (J.target_regular j)
  target_injective := by
    let A (j : Fin H.count) : C(Time × Time, Time × Circle) :=
      ⟨affineCylinder firstHalfWindow ∘ H.coordinate j,
        (affineCylinder_circle_properties firstHalfWindow).1.continuous.comp (H.coordinate j).continuous⟩
    let B (j : Fin J.count) : C(Time × Time, Time × Circle) :=
      ⟨affineCylinder secondHalfWindow ∘ J.coordinate j,
        (affineCylinder_circle_properties secondHalfWindow).1.continuous.comp (J.coordinate j).continuous⟩
    have hfirst : ∀ t : Time, concatenateStage H J (affineTime firstHalfWindow t) = H.stage t := by
      intro t
      have ht : (affineTime firstHalfWindow t : ℝ) ≤ 1 / 2 := by
        dsimp [affineTime, firstHalfWindow]
        linarith [t.property.2]
      unfold concatenateStage
      rw [dif_pos ht]
      congr 1
      apply Subtype.ext
      dsimp [affineTime, firstHalfWindow]
      ring
    have hsecond : ∀ t : Time, concatenateStage H J (affineTime secondHalfWindow t) = J.stage t := by
      intro t
      unfold concatenateStage
      split_ifs with ht
      · have ht0 : t = 0 := by
          apply Subtype.ext
          change (t : ℝ) = 0
          dsimp [affineTime, secondHalfWindow] at ht
          linarith [t.property.1]
        have ht1 : (⟨2 * (affineTime secondHalfWindow t : ℝ), by
            constructor <;> dsimp [affineTime, secondHalfWindow] at ht ⊢ <;>
              linarith [t.property.1, t.property.2]⟩ : Time) = 1 := by
          apply Subtype.ext
          change 2 * (affineTime secondHalfWindow t : ℝ) = 1
          have ht0' : (t : ℝ) = 0 := congrArg Subtype.val ht0
          norm_num [affineTime, secondHalfWindow, ht0']
        rw [ht1, ht0]
        apply DFunLike.ext
        intro z
        exact congrFun (H.terminal.trans J.initial.symm) z
      · congr 1
        apply Subtype.ext
        dsimp [affineTime, secondHalfWindow]
        ring
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · intro p
      have heq : (fun q : Time × Time =>
          ((affineCylinder firstHalfWindow (H.coordinate j q)).1,
            concatenateStage H J (affineCylinder firstHalfWindow (H.coordinate j q)).1
              (affineCylinder firstHalfWindow (H.coordinate j q)).2)) =
          affineCylinder firstHalfWindow ∘ (fun q => ((H.coordinate j q).1,
            H.stage (H.coordinate j q).1 (H.coordinate j q).2)) := by
        funext q
        dsimp only [affineCylinder, Function.comp_apply]
        rw [hfirst]
      have hchart : (fun q : Time × Time =>
          (((show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.castAdd J.count j)) q).1,
            concatenateStage H J ((show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.castAdd J.count j)) q).1
              ((show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.castAdd J.count j)) q).2)) =
          affineCylinder firstHalfWindow ∘ (fun q => ((H.coordinate j q).1,
            H.stage (H.coordinate j q).1 (H.coordinate j q).2)) := by
        simpa only [Fin.addCases_left, A, B, ContinuousMap.coe_mk, Function.comp_apply] using heq
      have hd := mfderiv_congr (I := ((𝓡∂ 1).prod (𝓡∂ 1)))
        (I' := ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3))) (x := p) hchart
      change Function.Injective
        (mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3))
          (fun q => (((show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.castAdd J.count j)) q).1,
            concatenateStage H J ((show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.castAdd J.count j)) q).1
              ((show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.castAdd J.count j)) q).2)) p)
      rw [hd, mfderiv_comp p
        ((affineCylinder_euclidean_properties firstHalfWindow).2.1.mdifferentiableAt (by simp))
        ((H.target_regular j).mdifferentiableAt (by simp))]
      exact ((affineCylinder_euclidean_properties firstHalfWindow).2.2 _).comp
        (H.target_injective j p)
    · intro p
      have heq : (fun q : Time × Time =>
          ((affineCylinder secondHalfWindow (J.coordinate j q)).1,
            concatenateStage H J (affineCylinder secondHalfWindow (J.coordinate j q)).1
              (affineCylinder secondHalfWindow (J.coordinate j q)).2)) =
          affineCylinder secondHalfWindow ∘ (fun q => ((J.coordinate j q).1,
            J.stage (J.coordinate j q).1 (J.coordinate j q).2)) := by
        funext q
        dsimp only [affineCylinder, Function.comp_apply]
        rw [hsecond]
      have hchart : (fun q : Time × Time =>
          (((show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.natAdd H.count j)) q).1,
            concatenateStage H J ((show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.natAdd H.count j)) q).1
              ((show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.natAdd H.count j)) q).2)) =
          affineCylinder secondHalfWindow ∘ (fun q => ((J.coordinate j q).1,
            J.stage (J.coordinate j q).1 (J.coordinate j q).2)) := by
        simpa only [Fin.addCases_right, A, B, ContinuousMap.coe_mk, Function.comp_apply] using heq
      have hd := mfderiv_congr (I := ((𝓡∂ 1).prod (𝓡∂ 1)))
        (I' := ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3))) (x := p) hchart
      change Function.Injective
        (mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3))
          (fun q => (((show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.natAdd H.count j)) q).1,
            concatenateStage H J ((show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.natAdd H.count j)) q).1
              ((show C(Time × Time, Time × Circle) from Fin.addCases A B (Fin.natAdd H.count j)) q).2)) p)
      rw [hd, mfderiv_comp p
        ((affineCylinder_euclidean_properties secondHalfWindow).2.1.mdifferentiableAt (by simp))
        ((J.target_regular j).mdifferentiableAt (by simp))]
      exact ((affineCylinder_euclidean_properties secondHalfWindow).2.2 _).comp
        (J.target_injective j p)
  smooth_interiors := by
    have hfirst : ∀ t : Time, concatenateStage H J (affineTime firstHalfWindow t) = H.stage t := by
      intro t
      have ht : (affineTime firstHalfWindow t : ℝ) ≤ 1 / 2 := by
        dsimp [affineTime, firstHalfWindow]
        linarith [t.property.2]
      unfold concatenateStage
      rw [dif_pos ht]
      congr 1
      apply Subtype.ext
      dsimp [affineTime, firstHalfWindow]
      ring
    have hsecond : ∀ t : Time, concatenateStage H J (affineTime secondHalfWindow t) = J.stage t := by
      intro t
      unfold concatenateStage
      split_ifs with ht
      · have ht0 : t = 0 := by
          apply Subtype.ext
          change (t : ℝ) = 0
          dsimp [affineTime, secondHalfWindow] at ht
          linarith [t.property.1]
        have ht1 : (⟨2 * (affineTime secondHalfWindow t : ℝ), by
            constructor <;> dsimp [affineTime, secondHalfWindow] at ht ⊢ <;>
              linarith [t.property.1, t.property.2]⟩ : Time) = 1 := by
          apply Subtype.ext
          change 2 * (affineTime secondHalfWindow t : ℝ) = 1
          have ht0' : (t : ℝ) = 0 := congrArg Subtype.val ht0
          norm_num [affineTime, secondHalfWindow, ht0']
        rw [ht1, ht0]
        apply DFunLike.ext
        intro z
        exact congrFun (H.terminal.trans J.initial.symm) z
      · congr 1
        apply Subtype.ext
        dsimp [affineTime, secondHalfWindow]
        ring
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have heq : (fun q : Time × Time =>
          ((affineCylinder firstHalfWindow (H.coordinate j q)).1,
            concatenateStage H J (affineCylinder firstHalfWindow (H.coordinate j q)).1
              (affineCylinder firstHalfWindow (H.coordinate j q)).2)) =
          affineCylinder firstHalfWindow ∘ (fun q => ((H.coordinate j q).1,
            H.stage (H.coordinate j q).1 (H.coordinate j q).2)) := by
        funext q
        dsimp only [affineCylinder, Function.comp_apply]
        rw [hfirst]
      try simp only [Fin.addCases_left, ContinuousMap.coe_mk, Function.comp_apply]
      rw [heq]
      exact (affineCylinder_euclidean_properties firstHalfWindow).2.1.comp_contMDiffOn
        (H.smooth_interiors j)
    · have heq : (fun q : Time × Time =>
          ((affineCylinder secondHalfWindow (J.coordinate j q)).1,
            concatenateStage H J (affineCylinder secondHalfWindow (J.coordinate j q)).1
              (affineCylinder secondHalfWindow (J.coordinate j q)).2)) =
          affineCylinder secondHalfWindow ∘ (fun q => ((J.coordinate j q).1,
            J.stage (J.coordinate j q).1 (J.coordinate j q).2)) := by
        funext q
        dsimp only [affineCylinder, Function.comp_apply]
        rw [hsecond]
      try simp only [Fin.addCases_right, ContinuousMap.coe_mk, Function.comp_apply]
      rw [heq]
      exact (affineCylinder_euclidean_properties secondHalfWindow).2.1.comp_contMDiffOn
        (J.smooth_interiors j)

def endpointCongr {f g f' g' : Circle → Euc 3}
    (hf : f = f') (hg : g = g') (H : PiecewiseCurveIsotopy f g) :
    PiecewiseCurveIsotopy f' g' where
  stage := H.stage
  embedding := H.embedding
  continuous_family := H.continuous_family
  initial := by exact H.initial.trans hf
  terminal := by exact H.terminal.trans hg
  count := H.count
  coordinate := H.coordinate
  coordinate_embedding := H.coordinate_embedding
  source_regular := H.source_regular
  source_injective := H.source_injective
  covers := H.covers
  target_regular := H.target_regular
  target_injective := H.target_injective
  smooth_interiors := H.smooth_interiors

theorem reverse_stage {f g : Circle → Euc 3} (H : PiecewiseCurveIsotopy f g)
    (t : Time) (z : Circle) : H.reverse.stage t z = H.stage (reflectTime t) z := by
  rfl

theorem reverse_coordinate {f g : Circle → Euc 3} (H : PiecewiseCurveIsotopy f g)
    (i : Fin H.count) (p : Time × Time) :
    H.reverse.coordinate i p = reflectCylinder (H.coordinate i p) := by
  rfl

theorem reverse_graph {f g : Circle → Euc 3} (H : PiecewiseCurveIsotopy f g)
    (i : Fin H.count) (p : Time × Time) :
    ((H.reverse.coordinate i p).1,
      H.reverse.stage (H.reverse.coordinate i p).1 (H.reverse.coordinate i p).2) =
    reflectCylinder ((H.coordinate i p).1,
      H.stage (H.coordinate i p).1 (H.coordinate i p).2) := by
  change (reflectTime (H.coordinate i p).1,
    H.stage (reflectTime (reflectTime (H.coordinate i p).1)) (H.coordinate i p).2) = _
  rw [reflectTime_properties.2.2.2.1]
  rfl

theorem concatenate_first_stage {f g h : Circle → Euc 3}
    (H : PiecewiseCurveIsotopy f g) (J : PiecewiseCurveIsotopy g h)
    (t : Time) (z : Circle) :
    (H.concatenate J).stage (affineTime firstHalfWindow t) z = H.stage t z := by
  change concatenateStage H J (affineTime firstHalfWindow t) z = H.stage t z
  have ht : (affineTime firstHalfWindow t : ℝ) ≤ 1 / 2 := by
    dsimp [affineTime, firstHalfWindow]
    linarith [t.property.2]
  unfold concatenateStage
  rw [dif_pos ht]
  congr 2
  apply Subtype.ext
  dsimp [affineTime, firstHalfWindow]
  ring

theorem concatenate_second_stage {f g h : Circle → Euc 3}
    (H : PiecewiseCurveIsotopy f g) (J : PiecewiseCurveIsotopy g h)
    (t : Time) (z : Circle) :
    (H.concatenate J).stage (affineTime secondHalfWindow t) z = J.stage t z := by
  change concatenateStage H J (affineTime secondHalfWindow t) z = J.stage t z
  unfold concatenateStage
  split_ifs with ht
  · have ht0 : t = 0 := by
      apply Subtype.ext
      change (t : ℝ) = 0
      dsimp [affineTime, secondHalfWindow] at ht
      linarith [t.property.1]
    have ht1 : (⟨2 * (affineTime secondHalfWindow t : ℝ), by
        constructor <;> dsimp [affineTime, secondHalfWindow] at ht ⊢ <;>
          linarith [t.property.1, t.property.2]⟩ : Time) = 1 := by
      apply Subtype.ext
      change 2 * (affineTime secondHalfWindow t : ℝ) = 1
      have ht0' : (t : ℝ) = 0 := congrArg Subtype.val ht0
      norm_num [affineTime, secondHalfWindow, ht0']
    rw [ht1, ht0]
    exact congrFun (H.terminal.trans J.initial.symm) z
  · congr 2
    apply Subtype.ext
    dsimp [affineTime, secondHalfWindow]
    ring

theorem concatenate_midpoint {f g h : Circle → Euc 3}
    (H : PiecewiseCurveIsotopy f g) (J : PiecewiseCurveIsotopy g h) (z : Circle) :
    (H.concatenate J).stage (affineTime firstHalfWindow 1) z = g z := by
  rw [concatenate_first_stage]
  exact congrFun H.terminal z

theorem concatenate_first_coordinate {f g h : Circle → Euc 3}
    (H : PiecewiseCurveIsotopy f g) (J : PiecewiseCurveIsotopy g h)
    (i : Fin H.count) (p : Time × Time) :
    (H.concatenate J).coordinate (Fin.castAdd J.count i) p =
      affineCylinder firstHalfWindow (H.coordinate i p) := by
  change (Fin.addCases _ _ (Fin.castAdd J.count i) : C(Time × Time, Time × Circle)) p = _
  rw [Fin.addCases_left]
  rfl

theorem concatenate_second_coordinate {f g h : Circle → Euc 3}
    (H : PiecewiseCurveIsotopy f g) (J : PiecewiseCurveIsotopy g h)
    (i : Fin J.count) (p : Time × Time) :
    (H.concatenate J).coordinate (Fin.natAdd H.count i) p =
      affineCylinder secondHalfWindow (J.coordinate i p) := by
  change (Fin.addCases _ _ (Fin.natAdd H.count i) : C(Time × Time, Time × Circle)) p = _
  rw [Fin.addCases_right]
  rfl

theorem concatenate_first_graph {f g h : Circle → Euc 3}
    (H : PiecewiseCurveIsotopy f g) (J : PiecewiseCurveIsotopy g h)
    (i : Fin H.count) (p : Time × Time) :
    (((H.concatenate J).coordinate (Fin.castAdd J.count i) p).1,
      (H.concatenate J).stage ((H.concatenate J).coordinate (Fin.castAdd J.count i) p).1
        ((H.concatenate J).coordinate (Fin.castAdd J.count i) p).2) =
      affineCylinder firstHalfWindow ((H.coordinate i p).1,
        H.stage (H.coordinate i p).1 (H.coordinate i p).2) := by
  rw [concatenate_first_coordinate]
  change (affineTime firstHalfWindow (H.coordinate i p).1,
    (H.concatenate J).stage (affineTime firstHalfWindow (H.coordinate i p).1)
      (H.coordinate i p).2) = _
  rw [concatenate_first_stage]
  rfl

theorem concatenate_second_graph {f g h : Circle → Euc 3}
    (H : PiecewiseCurveIsotopy f g) (J : PiecewiseCurveIsotopy g h)
    (i : Fin J.count) (p : Time × Time) :
    (((H.concatenate J).coordinate (Fin.natAdd H.count i) p).1,
      (H.concatenate J).stage ((H.concatenate J).coordinate (Fin.natAdd H.count i) p).1
        ((H.concatenate J).coordinate (Fin.natAdd H.count i) p).2) =
      affineCylinder secondHalfWindow ((J.coordinate i p).1,
        J.stage (J.coordinate i p).1 (J.coordinate i p).2) := by
  rw [concatenate_second_coordinate]
  change (affineTime secondHalfWindow (J.coordinate i p).1,
    (H.concatenate J).stage (affineTime secondHalfWindow (J.coordinate i p).1)
      (J.coordinate i p).2) = _
  rw [concatenate_second_stage]
  rfl

theorem endpointCongr_retains {f g f' g' : Circle → Euc 3}
    (hf : f = f') (hg : g = g') (H : PiecewiseCurveIsotopy f g) :
    (H.endpointCongr hf hg).stage = H.stage ∧
    (H.endpointCongr hf hg).coordinate = H.coordinate := by
  exact ⟨rfl, rfl⟩

end PiecewiseCurveIsotopy
end
end SeifertSurfaces.LongitudeProducers
