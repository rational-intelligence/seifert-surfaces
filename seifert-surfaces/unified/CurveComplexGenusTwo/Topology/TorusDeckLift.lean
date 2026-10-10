import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Normed.Group.CocompactMap
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Algebra.Field.Periodic
namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
open CurveComplex Filter Set

abbrev Torus := Circle × Circle

theorem torus_curve_has_deck_lift (c : Curve Torus) :
    ∃ (m n : ℤ) (F : C(ℝ, ℝ × ℝ)),
      (∀ x, (Circle.exp (F x).1, Circle.exp (F x).2) = c.map (Circle.exp x)) ∧
      (∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * (2 * Real.pi)) =
        ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
         (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi))) ∧
      ((m ≠ 0 ∨ n ≠ 0) → Function.Injective F) ∧
      (∀ (x y : ℝ) (a b : ℤ),
        F x = ((F y).1 + (a : ℝ) * (2 * Real.pi), (F y).2 + (b : ℝ) * (2 * Real.pi)) →
        ∃ k : ℤ, a = k * m ∧ b = k * n) := by
  have lifting (f : C(Circle, Circle)) :
      ∃ (k : ℤ) (F : C(ℝ, ℝ)),
        (∀ x : ℝ, Circle.exp (F x) = f (Circle.exp x)) ∧
        (∀ x : ℝ, F (x + 2 * Real.pi) = F x + (k : ℝ) * (2 * Real.pi)) := by
    let g : C(ℝ, Circle) := f.comp ⟨Circle.exp, by fun_prop⟩
    obtain ⟨r, hr⟩ := Circle.exp_surjective (g 0)
    obtain ⟨F, hF, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g 0 r hr
    have hFexp (x : ℝ) : Circle.exp (F x) = f (Circle.exp x) := congrFun hF.2 x
    have hperiod : Circle.exp (F (2 * Real.pi)) = Circle.exp (F 0) := by
      rw [hFexp, hFexp]
      simp
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hperiod
    let F₁ : C(ℝ, ℝ) := ⟨fun x => F (x + 2 * Real.pi), by fun_prop⟩
    let F₂ : C(ℝ, ℝ) := ⟨fun x => F x + (k : ℝ) * (2 * Real.pi), by fun_prop⟩
    have he : Circle.exp ∘ F₁ = Circle.exp ∘ F₂ := by
      funext x
      change Circle.exp (F (x + 2 * Real.pi)) = Circle.exp (F x + (k : ℝ) * (2 * Real.pi))
      rw [hFexp, Circle.exp_add, Circle.exp_two_pi, mul_one,
        Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one, hFexp]
    have hzero : F₁ 0 = F₂ 0 := by simpa [F₁, F₂] using hk
    have hEq : F₁ = F₂ := DFunLike.coe_injective
      (Circle.isCoveringMap_exp.eq_of_comp_eq F₁.continuous F₂.continuous he 0 hzero)
    refine ⟨k, F, hFexp, ?_⟩
    intro x
    exact congrArg (fun A : C(ℝ, ℝ) => A x) hEq
  let f₁ : C(Circle, Circle) := ⟨fun z => (c.map z).1, continuous_fst.comp c.embedded.continuous⟩
  let f₂ : C(Circle, Circle) := ⟨fun z => (c.map z).2, continuous_snd.comp c.embedded.continuous⟩
  obtain ⟨m, A, hA, hpA⟩ := lifting f₁
  obtain ⟨n, B, hB, hpB⟩ := lifting f₂
  have all_period (k : ℤ) (F : C(ℝ, ℝ))
      (hp : ∀ x, F (x + 2 * Real.pi) = F x + (k : ℝ) * (2 * Real.pi)) :
      ∀ (j : ℤ) (x : ℝ), F (x + (j : ℝ) * (2 * Real.pi)) =
        F x + (j : ℝ) * (k : ℝ) * (2 * Real.pi) := by
    have h : Function.Periodic (fun x => F x - (k : ℝ) * x) (2 * Real.pi) := by
      intro x
      dsimp
      rw [hp]
      ring
    intro j x
    have hj := h.int_mul j x
    change F (x + (j : ℝ) * (2 * Real.pi)) - (k : ℝ) * (x + (j : ℝ) * (2 * Real.pi)) = F x - (k : ℝ) * x at hj
    linarith
  let F : C(ℝ, ℝ × ℝ) := A.prodMk B
  have hproj (x : ℝ) : (Circle.exp (F x).1, Circle.exp (F x).2) = c.map (Circle.exp x) :=
    Prod.ext (hA x) (hB x)
  have hperiod (k : ℤ) (x : ℝ) : F (x + (k : ℝ) * (2 * Real.pi)) =
      ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
       (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi)) :=
    Prod.ext (all_period m A hpA k x) (all_period n B hpB k x)
  refine ⟨m, n, F, hproj, hperiod, ?_⟩
  constructor
  · intro hnonzero x y hxy
    have he : Circle.exp x = Circle.exp y := c.embedded.injective
      ((hproj x).symm.trans ((congrArg (fun v : ℝ × ℝ => (Circle.exp v.1, Circle.exp v.2)) hxy).trans (hproj y)))
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
    have hper := hperiod k y
    rw [← hk, hxy] at hper
    have h1 := congrArg Prod.fst hper
    have h2 := congrArg Prod.snd hper
    dsimp at h1 h2
    have hk0 : (k : ℝ) = 0 := by
      rcases hnonzero with hm | hn
      · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
        have hz : (k : ℝ) * (m : ℝ) * (2 * Real.pi) = 0 := by linarith
        rcases mul_eq_zero.mp hz with h | h
        · exact (mul_eq_zero.mp h).resolve_right hm'
        · exact False.elim ((ne_of_gt (mul_pos (by norm_num) Real.pi_pos)) h)
      · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        have hz : (k : ℝ) * (n : ℝ) * (2 * Real.pi) = 0 := by linarith
        rcases mul_eq_zero.mp hz with h | h
        · exact (mul_eq_zero.mp h).resolve_right hn'
        · exact False.elim ((ne_of_gt (mul_pos (by norm_num) Real.pi_pos)) h)
    simpa [hk0] using hk
  · intro x y a b hxy
    have he : Circle.exp x = Circle.exp y := by
      apply c.embedded.injective
      rw [← hproj x, ← hproj y, hxy]
      simp only [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
    have hp := hperiod k y
    rw [← hk, hxy] at hp
    have h1 := congrArg Prod.fst hp
    have h2 := congrArg Prod.snd hp
    dsimp at h1 h2
    refine ⟨k, ?_, ?_⟩
    · have ha : (a : ℝ) = (k : ℝ) * (m : ℝ) := by
        nlinarith [Real.pi_pos]
      exact_mod_cast ha
    · have hb : (b : ℝ) = (k : ℝ) * (n : ℝ) := by
        nlinarith [Real.pi_pos]
      exact_mod_cast hb

theorem torus_period_lift_isProperMap (F : C(ℝ, ℝ × ℝ)) (m n : ℤ)
    (hp : ∀ x : ℝ, F (x + 2 * Real.pi) =
      ((F x).1 + (m : ℝ) * (2 * Real.pi),
       (F x).2 + (n : ℝ) * (2 * Real.pi)))
    (hnonzero : m ≠ 0 ∨ n ≠ 0) :
    IsProperMap F ∧ (Function.Injective F → Topology.IsClosedEmbedding F) := by
  have hproper : IsProperMap F := by
    have scalar (f : C(ℝ, ℝ)) (a : ℝ) (ha : a ≠ 0)
        (hperiod : ∀ x, f (x + 2 * Real.pi) = f x + a * (2 * Real.pi)) :
        IsProperMap f := by
      let B : ℝ → ℝ := fun x => f x - a * x
      have hB : Continuous B := by dsimp [B]; fun_prop
      have hper : Function.Periodic B (2 * Real.pi) := by
        intro x
        dsimp [B]
        rw [hperiod]
        ring
      have hrange : IsCompact (Set.range B) := by
        rw [← hper.image_Icc (mul_pos (by norm_num) Real.pi_pos) 0]
        exact isCompact_Icc.image hB
      obtain ⟨M, hM⟩ := (hrange.image continuous_norm).bddAbove
      have hbound (x : ℝ) : ‖B x‖ ≤ M := hM ⟨B x, ⟨x, rfl⟩, rfl⟩
      have hlinear (x : ℝ) : ‖a‖ * ‖x‖ ≤ ‖f x‖ + M := by
        have h := norm_sub_le (f x) (B x)
        have he : f x - B x = a * x := by dsimp [B]; ring
        rw [he, norm_mul] at h
        linarith [hbound x]
      apply isProperMap_iff_tendsto_cocompact.mpr
      refine ⟨f.continuous, Filter.tendsto_cocompact_cocompact_of_norm ?_⟩
      intro ε
      refine ⟨(ε + M) / ‖a‖, ?_⟩
      intro x hx
      have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
      have hh := (div_lt_iff₀ ha').mp hx
      have hb := hlinear x
      nlinarith
    rcases hnonzero with hm | hn
    · let f : C(ℝ, ℝ) := ⟨fun x => (F x).1, continuous_fst.comp F.continuous⟩
      apply isProperMap_of_comp_of_t2 F.continuous continuous_fst
      apply scalar f (m : ℝ) (by exact_mod_cast hm)
      intro x
      exact congrArg Prod.fst (hp x)
    · let f : C(ℝ, ℝ) := ⟨fun x => (F x).2, continuous_snd.comp F.continuous⟩
      apply isProperMap_of_comp_of_t2 F.continuous continuous_snd
      apply scalar f (n : ℝ) (by exact_mod_cast hn)
      intro x
      exact congrArg Prod.snd (hp x)
  exact ⟨hproper, fun hinj =>
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      F.continuous hinj hproper.isClosedMap⟩

theorem torus_curve_has_proper_deck_lift (c : Curve Torus) :
    ∃ (m n : ℤ) (F : C(ℝ, ℝ × ℝ)),
      (∀ x, (Circle.exp (F x).1, Circle.exp (F x).2) = c.map (Circle.exp x)) ∧
      (∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * (2 * Real.pi)) =
        ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
         (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi))) ∧
      ((m ≠ 0 ∨ n ≠ 0) → IsProperMap F ∧ Topology.IsClosedEmbedding F) ∧
      (∀ (x y : ℝ) (a b : ℤ),
        F x = ((F y).1 + (a : ℝ) * (2 * Real.pi), (F y).2 + (b : ℝ) * (2 * Real.pi)) →
        ∃ k : ℤ, a = k * m ∧ b = k * n) := by
  have hlift :
      ∃ (m n : ℤ) (F : C(ℝ, ℝ × ℝ)),
        (∀ x, (Circle.exp (F x).1, Circle.exp (F x).2) = c.map (Circle.exp x)) ∧
        (∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * (2 * Real.pi)) =
          ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
           (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi))) ∧
        ((m ≠ 0 ∨ n ≠ 0) → Function.Injective F) ∧
        (∀ (x y : ℝ) (a b : ℤ),
          F x = ((F y).1 + (a : ℝ) * (2 * Real.pi), (F y).2 + (b : ℝ) * (2 * Real.pi)) →
          ∃ k : ℤ, a = k * m ∧ b = k * n) := by
    have lifting (f : C(Circle, Circle)) :
        ∃ (k : ℤ) (F : C(ℝ, ℝ)),
          (∀ x : ℝ, Circle.exp (F x) = f (Circle.exp x)) ∧
          (∀ x : ℝ, F (x + 2 * Real.pi) = F x + (k : ℝ) * (2 * Real.pi)) := by
      let g : C(ℝ, Circle) := f.comp ⟨Circle.exp, by fun_prop⟩
      obtain ⟨r, hr⟩ := Circle.exp_surjective (g 0)
      obtain ⟨F, hF, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g 0 r hr
      have hFexp (x : ℝ) : Circle.exp (F x) = f (Circle.exp x) := congrFun hF.2 x
      have hperiod : Circle.exp (F (2 * Real.pi)) = Circle.exp (F 0) := by
        rw [hFexp, hFexp]
        simp
      obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hperiod
      let F₁ : C(ℝ, ℝ) := ⟨fun x => F (x + 2 * Real.pi), by fun_prop⟩
      let F₂ : C(ℝ, ℝ) := ⟨fun x => F x + (k : ℝ) * (2 * Real.pi), by fun_prop⟩
      have he : Circle.exp ∘ F₁ = Circle.exp ∘ F₂ := by
        funext x
        change Circle.exp (F (x + 2 * Real.pi)) = Circle.exp (F x + (k : ℝ) * (2 * Real.pi))
        rw [hFexp, Circle.exp_add, Circle.exp_two_pi, mul_one,
          Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one, hFexp]
      have hzero : F₁ 0 = F₂ 0 := by simpa [F₁, F₂] using hk
      have hEq : F₁ = F₂ := DFunLike.coe_injective
        (Circle.isCoveringMap_exp.eq_of_comp_eq F₁.continuous F₂.continuous he 0 hzero)
      refine ⟨k, F, hFexp, ?_⟩
      intro x
      exact congrArg (fun A : C(ℝ, ℝ) => A x) hEq
    let f₁ : C(Circle, Circle) := ⟨fun z => (c.map z).1, continuous_fst.comp c.embedded.continuous⟩
    let f₂ : C(Circle, Circle) := ⟨fun z => (c.map z).2, continuous_snd.comp c.embedded.continuous⟩
    obtain ⟨m, A, hA, hpA⟩ := lifting f₁
    obtain ⟨n, B, hB, hpB⟩ := lifting f₂
    have all_period (k : ℤ) (F : C(ℝ, ℝ))
        (hp : ∀ x, F (x + 2 * Real.pi) = F x + (k : ℝ) * (2 * Real.pi)) :
        ∀ (j : ℤ) (x : ℝ), F (x + (j : ℝ) * (2 * Real.pi)) =
          F x + (j : ℝ) * (k : ℝ) * (2 * Real.pi) := by
      have h : Function.Periodic (fun x => F x - (k : ℝ) * x) (2 * Real.pi) := by
        intro x
        dsimp
        rw [hp]
        ring
      intro j x
      have hj := h.int_mul j x
      change F (x + (j : ℝ) * (2 * Real.pi)) - (k : ℝ) * (x + (j : ℝ) * (2 * Real.pi)) = F x - (k : ℝ) * x at hj
      linarith
    let F : C(ℝ, ℝ × ℝ) := A.prodMk B
    have hproj (x : ℝ) : (Circle.exp (F x).1, Circle.exp (F x).2) = c.map (Circle.exp x) :=
      Prod.ext (hA x) (hB x)
    have hperiod (k : ℤ) (x : ℝ) : F (x + (k : ℝ) * (2 * Real.pi)) =
        ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
         (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi)) :=
      Prod.ext (all_period m A hpA k x) (all_period n B hpB k x)
    refine ⟨m, n, F, hproj, hperiod, ?_⟩
    constructor
    · intro hnonzero x y hxy
      have he : Circle.exp x = Circle.exp y := c.embedded.injective
        ((hproj x).symm.trans ((congrArg (fun v : ℝ × ℝ => (Circle.exp v.1, Circle.exp v.2)) hxy).trans (hproj y)))
      obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
      have hper := hperiod k y
      rw [← hk, hxy] at hper
      have h1 := congrArg Prod.fst hper
      have h2 := congrArg Prod.snd hper
      dsimp at h1 h2
      have hk0 : (k : ℝ) = 0 := by
        rcases hnonzero with hm | hn
        · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
          have hz : (k : ℝ) * (m : ℝ) * (2 * Real.pi) = 0 := by linarith
          rcases mul_eq_zero.mp hz with h | h
          · exact (mul_eq_zero.mp h).resolve_right hm'
          · exact False.elim ((ne_of_gt (mul_pos (by norm_num) Real.pi_pos)) h)
        · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
          have hz : (k : ℝ) * (n : ℝ) * (2 * Real.pi) = 0 := by linarith
          rcases mul_eq_zero.mp hz with h | h
          · exact (mul_eq_zero.mp h).resolve_right hn'
          · exact False.elim ((ne_of_gt (mul_pos (by norm_num) Real.pi_pos)) h)
      simpa [hk0] using hk
    · intro x y a b hxy
      have he : Circle.exp x = Circle.exp y := by
        apply c.embedded.injective
        rw [← hproj x, ← hproj y, hxy]
        simp only [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
      obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
      have hp := hperiod k y
      rw [← hk, hxy] at hp
      have h1 := congrArg Prod.fst hp
      have h2 := congrArg Prod.snd hp
      dsimp at h1 h2
      refine ⟨k, ?_, ?_⟩
      · have ha : (a : ℝ) = (k : ℝ) * (m : ℝ) := by
          nlinarith [Real.pi_pos]
        exact_mod_cast ha
      · have hb : (b : ℝ) = (k : ℝ) * (n : ℝ) := by
          nlinarith [Real.pi_pos]
        exact_mod_cast hb
  have proper (F : C(ℝ, ℝ × ℝ)) (m n : ℤ)
      (hp : ∀ x : ℝ, F (x + 2 * Real.pi) =
        ((F x).1 + (m : ℝ) * (2 * Real.pi),
         (F x).2 + (n : ℝ) * (2 * Real.pi)))
      (hnonzero : m ≠ 0 ∨ n ≠ 0) :
      IsProperMap F ∧ (Function.Injective F → Topology.IsClosedEmbedding F) := by
    have hproper : IsProperMap F := by
      have scalar (f : C(ℝ, ℝ)) (a : ℝ) (ha : a ≠ 0)
          (hperiod : ∀ x, f (x + 2 * Real.pi) = f x + a * (2 * Real.pi)) :
          IsProperMap f := by
        let B : ℝ → ℝ := fun x => f x - a * x
        have hB : Continuous B := by dsimp [B]; fun_prop
        have hper : Function.Periodic B (2 * Real.pi) := by
          intro x
          dsimp [B]
          rw [hperiod]
          ring
        have hrange : IsCompact (Set.range B) := by
          rw [← hper.image_Icc (mul_pos (by norm_num) Real.pi_pos) 0]
          exact isCompact_Icc.image hB
        obtain ⟨M, hM⟩ := (hrange.image continuous_norm).bddAbove
        have hbound (x : ℝ) : ‖B x‖ ≤ M := hM ⟨B x, ⟨x, rfl⟩, rfl⟩
        have hlinear (x : ℝ) : ‖a‖ * ‖x‖ ≤ ‖f x‖ + M := by
          have h := norm_sub_le (f x) (B x)
          have he : f x - B x = a * x := by dsimp [B]; ring
          rw [he, norm_mul] at h
          linarith [hbound x]
        apply isProperMap_iff_tendsto_cocompact.mpr
        refine ⟨f.continuous, Filter.tendsto_cocompact_cocompact_of_norm ?_⟩
        intro ε
        refine ⟨(ε + M) / ‖a‖, ?_⟩
        intro x hx
        have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
        have hh := (div_lt_iff₀ ha').mp hx
        have hb := hlinear x
        nlinarith
      rcases hnonzero with hm | hn
      · let f : C(ℝ, ℝ) := ⟨fun x => (F x).1, continuous_fst.comp F.continuous⟩
        apply isProperMap_of_comp_of_t2 F.continuous continuous_fst
        apply scalar f (m : ℝ) (by exact_mod_cast hm)
        intro x
        exact congrArg Prod.fst (hp x)
      · let f : C(ℝ, ℝ) := ⟨fun x => (F x).2, continuous_snd.comp F.continuous⟩
        apply isProperMap_of_comp_of_t2 F.continuous continuous_snd
        apply scalar f (n : ℝ) (by exact_mod_cast hn)
        intro x
        exact congrArg Prod.snd (hp x)
    exact ⟨hproper, fun hinj =>
      Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
        F.continuous hinj hproper.isClosedMap⟩
  obtain ⟨m, n, F, hproj, hperiod, hinj, hcollision⟩ := hlift
  refine ⟨m, n, F, hproj, hperiod, ?_, hcollision⟩
  intro hnonzero
  have hp (x : ℝ) : F (x + 2 * Real.pi) =
      ((F x).1 + (m : ℝ) * (2 * Real.pi), (F x).2 + (n : ℝ) * (2 * Real.pi)) := by
    simpa using hperiod 1 x
  obtain ⟨hproper, hclosed⟩ := proper F m n hp hnonzero
  exact ⟨hproper, hclosed (hinj hnonzero)⟩

theorem torus_lift_disjoint_root_translate (F : ℝ → ℝ × ℝ) (m n : ℤ)
    (hcollision : ∀ (x y : ℝ) (a b : ℤ),
      F x = ((F y).1 + (a : ℝ) * (2 * Real.pi),
        (F y).2 + (b : ℝ) * (2 * Real.pi)) →
      ∃ k : ℤ, a = k * m ∧ b = k * n)
    (hnonzero : m ≠ 0 ∨ n ≠ 0)
    (d a b : ℤ) (hd : 1 < d) (hm : m = d * a) (hn : n = d * b) :
    Disjoint (Set.range F)
      (Set.range (fun x => ((F x).1 + (a : ℝ) * (2 * Real.pi),
        (F x).2 + (b : ℝ) * (2 * Real.pi)))) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  obtain ⟨k, hka, hkb⟩ := hcollision x y a b hy.symm
  have heq : k * d = 1 := by
    rcases hnonzero with hm0 | hn0
    · have ha : a ≠ 0 := by intro h; simp [h] at hm; exact hm0 hm
      have hz : (k * d - 1) * a = 0 := by rw [hm] at hka; nlinarith
      have := (mul_eq_zero.mp hz).resolve_right ha
      omega
    · have hb : b ≠ 0 := by intro h; simp [h] at hn; exact hn0 hn
      have hz : (k * d - 1) * b = 0 := by rw [hn] at hkb; nlinarith
      have := (mul_eq_zero.mp hz).resolve_right hb
      omega
  by_cases hk : k ≤ 0
  · nlinarith
  · have : 1 ≤ k := by omega
    nlinarith

theorem torus_lift_range_period (F : ℝ → ℝ × ℝ) (m n : ℤ)
    (hp : ∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * (2 * Real.pi)) =
      ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
       (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi))) :
    Set.range (fun x => ((F x).1 + (m : ℝ) * (2 * Real.pi),
      (F x).2 + (n : ℝ) * (2 * Real.pi))) = Set.range F := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨x + 2 * Real.pi, by simpa using hp 1 x⟩
  · rintro z ⟨x, rfl⟩
    refine ⟨x - 2 * Real.pi, ?_⟩
    have h := hp 1 (x - 2 * Real.pi)
    simpa using h.symm

theorem torus_lift_disjoint_intermediate_translate (F : ℝ → ℝ × ℝ) (m n : ℤ)
    (hcollision : ∀ (x y : ℝ) (a b : ℤ),
      F x = ((F y).1 + (a : ℝ) * (2 * Real.pi),
        (F y).2 + (b : ℝ) * (2 * Real.pi)) →
      ∃ k : ℤ, a = k * m ∧ b = k * n)
    (hnonzero : m ≠ 0 ∨ n ≠ 0)
    (d a b r : ℤ) (hr : 0 < r) (hrd : r < d) (hm : m = d * a) (hn : n = d * b) :
    Disjoint (Set.range F)
      (Set.range (fun x => ((F x).1 + ((r * a : ℤ) : ℝ) * (2 * Real.pi),
        (F x).2 + ((r * b : ℤ) : ℝ) * (2 * Real.pi)))) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  obtain ⟨k, hka, hkb⟩ := hcollision x y (r * a) (r * b) hy.symm
  have heq : k * d = r := by
    rcases hnonzero with hm0 | hn0
    · have ha : a ≠ 0 := by intro h; simp [h] at hm; exact hm0 hm
      have hz : (k * d - r) * a = 0 := by rw [hm] at hka; nlinarith
      have := (mul_eq_zero.mp hz).resolve_right ha
      omega
    · have hb : b ≠ 0 := by intro h; simp [h] at hn; exact hn0 hn
      have hz : (k * d - r) * b = 0 := by rw [hn] at hkb; nlinarith
      have := (mul_eq_zero.mp hz).resolve_right hb
      omega
  by_cases hk : k ≤ 0
  · nlinarith
  · have : 1 ≤ k := by omega
    nlinarith

end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
