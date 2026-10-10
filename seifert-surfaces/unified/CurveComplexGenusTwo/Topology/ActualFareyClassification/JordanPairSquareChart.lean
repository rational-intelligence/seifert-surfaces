import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualReplacementJordan
import Schoenflies.JordanSchoenflies
import CurveComplexGenusTwo.Topology.GluedArcBoundary

open Set Topology Schoenflies

theorem jordan_pair_has_full_endpoint_square_chart
    {A P : Set Plane} {a b : Plane}
    (hA : IsArcBetween A a b) (hP : IsArcBetween P a b)
    (hmeet : A ∩ P = {a, b})
    (hJ : IsJordanCurve (A ∪ P)) :
    ∃ F : Plane ≃ₜ Plane, F '' P = sideBottom ∪ sideRight ∧
      F a = cornerNE ∧ F b = cornerSW ∧
      F '' (A ∪ P) = modelCurve := by
  let B : Set Plane := sideTop ∪ sideLeft
  let Q : Set Plane := sideBottom ∪ sideRight
  have hB : IsArcBetween B cornerNE cornerSW := by
    simpa [B] using isArcBetween_upperSides
  have hQ : IsArcBetween Q cornerNE cornerSW := by
    simpa [Q] using isArcBetween_lowerSides.reverse
  have hmeetTarget : B ∩ Q = {cornerNE, cornerSW} := by
    apply Subset.antisymm
    · intro z hz
      have hmem : z ∈ sideTop ∪ sideLeft ∧ z ∈ sideBottom ∪ sideRight := by
        simpa [B, Q] using hz
      rcases upperSides_meet_lowerSides z hmem.1 hmem.2 with rfl | rfl
      · simp
      · simp
    · intro z hz
      have hz' : z = cornerNE ∨ z = cornerSW := by simpa using hz
      rcases hz' with rfl | rfl
      · exact ⟨hB.left_mem, hQ.left_mem⟩
      · exact ⟨hB.right_mem, hQ.right_mem⟩
  obtain ⟨e, hArcImage, hleft, hright⟩ :=
    exists_homeomorph_union_arcs_preserving_second hA hP hB hQ hmeet hmeetTarget
  have hModel : B ∪ Q = modelCurve := by
    dsimp [B, Q]
    exact modelCurve_eq_sides.symm
  let eModel : ↥(A ∪ P) ≃ₜ ↥modelCurve := e.trans (Homeomorph.setCongr hModel)
  obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hJ isJordanCurve_modelCurve eModel
  have hImage : F '' P = Q := by
    ext y
    constructor
    · rintro ⟨x, hxP, rfl⟩
      have hxJ : x ∈ A ∪ P := Or.inr hxP
      have hxArc : (e ⟨x, hxJ⟩ : Plane) ∈ Q := by
        have hmem : (e ⟨x, hxJ⟩ : ↥(B ∪ Q)) ∈ e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P} :=
          ⟨⟨x, hxJ⟩, hxP, rfl⟩
        have hval : (e ⟨x, hxJ⟩ : Plane) ∈ Subtype.val ''
            (e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P}) := Set.mem_image_of_mem _ hmem
        rw [hArcImage] at hval
        exact hval
      have hfx : F x = (eModel ⟨x, hxJ⟩ : Plane) := hF ⟨x, hxJ⟩
      have hEmodel : (eModel ⟨x, hxJ⟩ : Plane) = (e ⟨x, hxJ⟩ : Plane) := by rfl
      rw [hfx, hEmodel]
      simpa [Q] using hxArc
    · intro hy
      have hyQ : y ∈ Q := by simpa [Q] using hy
      have hyImage : y ∈ Subtype.val ''
          (e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P}) := by rw [hArcImage]; exact hyQ
      obtain ⟨z, hzImage, hzy⟩ := hyImage
      obtain ⟨x, hxP, hzx⟩ := hzImage
      have hxJ : (x : Plane) ∈ A ∪ P := x.property
      refine ⟨(x : Plane), hxP, ?_⟩
      have hFz : F (x : Plane) = (eModel ⟨(x : Plane), hxJ⟩ : Plane) :=
        hF ⟨(x : Plane), hxJ⟩
      have hEmodel : (eModel ⟨(x : Plane), hxJ⟩ : Plane) =
          (e ⟨(x : Plane), hxJ⟩ : Plane) := rfl
      have hzx' : (e ⟨(x : Plane), hxJ⟩ : Plane) = (z : Plane) :=
        congrArg Subtype.val hzx
      calc
        F (x : Plane) = (eModel ⟨(x : Plane), hxJ⟩ : Plane) := hFz
        _ = (e ⟨(x : Plane), hxJ⟩ : Plane) := hEmodel
        _ = (z : Plane) := hzx'
        _ = y := hzy
  have hFa : F a = cornerNE := by
    let x : ↥(A ∪ P) := ⟨a, Or.inl hA.left_mem⟩
    have hxF : F (x : Plane) = (eModel x : Plane) := hF x
    have hxE : (eModel x : Plane) = (e x : Plane) := rfl
    have hxe : (e x : Plane) = cornerNE := by
      have h := congrArg Subtype.val hleft
      exact h
    calc
      F a = F (x : Plane) := rfl
      _ = (eModel x : Plane) := hxF
      _ = (e x : Plane) := hxE
      _ = cornerNE := hxe
  have hFb : F b = cornerSW := by
    let x : ↥(A ∪ P) := ⟨b, Or.inl hA.right_mem⟩
    have hxF : F (x : Plane) = (eModel x : Plane) := hF x
    have hxE : (eModel x : Plane) = (e x : Plane) := rfl
    have hxe : (e x : Plane) = cornerSW := by
      have h := congrArg Subtype.val hright
      exact h
    calc
      F b = F (x : Plane) := rfl
      _ = (eModel x : Plane) := hxF
      _ = (e x : Plane) := hxE
      _ = cornerSW := hxe
  have hwhole : F '' (A ∪ P) = modelCurve := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hF ⟨x, hx⟩]
      exact (eModel ⟨x, hx⟩).property
    · intro hy
      obtain ⟨x, hx⟩ := eModel.surjective ⟨y, hy⟩
      refine ⟨x.val, x.property, ?_⟩
      rw [hF x]
      exact congrArg Subtype.val hx
  exact ⟨F, hImage, hFa, hFb, hwhole⟩



theorem model_corner_diamond_homeomorph : ∃ L : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ),
    (∀ x, L x 0 = (x 0 + x 1) / 2 ∧ L x 1 = (x 0 - x 1) / 4) ∧
    (∀ x, ‖x‖ ≤ 1 → x ≠ ![1, 1] → x ≠ ![-1, -1] → ‖L x‖ < 1) ∧
    (∀ x, 4 < ‖x‖ → 1 < ‖L x‖) := by
  let f : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x => ![(x 0 + x 1) / 2, (x 0 - x 1) / 4]
  let g : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x => ![x 0 + 2 * x 1, x 0 - 2 * x 1]
  let L : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) := {
    toFun := f
    invFun := g
    left_inv := by intro x; ext i; fin_cases i <;> simp [f, g] <;> ring
    right_inv := by
      intro x
      ext i
      fin_cases i <;> simp [f,g]
      all_goals ring
    continuous_toFun := by apply continuous_pi; intro i; fin_cases i <;> dsimp [f] <;> fun_prop
    continuous_invFun := by apply continuous_pi; intro i; fin_cases i <;> dsimp [g] <;> fun_prop }
  refine ⟨L, (fun x => ⟨rfl, rfl⟩), ?_, ?_⟩
  · intro x hx hne hsw
    have hx0 : |x 0| ≤ 1 := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x 0 |>.trans hx
    have hx1 : |x 1| ≤ 1 := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x 1 |>.trans hx
    rw [abs_le] at hx0 hx1
    have hs : -2 < x 0 + x 1 ∧ x 0 + x 1 < 2 := by
      constructor
      · by_contra hn
        have h0 : x 0 = -1 := by linarith
        have h1 : x 1 = -1 := by linarith
        apply hsw
        ext i; fin_cases i <;> simp [h0, h1]
      · by_contra hn
        have h0 : x 0 = 1 := by linarith
        have h1 : x 1 = 1 := by linarith
        apply hne
        ext i; fin_cases i <;> simp [h0, h1]
    apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
    intro i
    fin_cases i
    · change ‖(x 0 + x 1) / 2‖ < 1
      rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
    · change ‖(x 0 - x 1) / 4‖ < 1
      rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  · intro x hx
    by_contra hn
    have hy : ‖L x‖ ≤ 1 := le_of_not_gt hn
    have hy0 : |L x 0| ≤ 1 := by simpa [Real.norm_eq_abs] using norm_le_pi_norm (L x) 0 |>.trans hy
    have hy1 : |L x 1| ≤ 1 := by simpa [Real.norm_eq_abs] using norm_le_pi_norm (L x) 1 |>.trans hy
    change |(x 0 + x 1) / 2| ≤ 1 at hy0
    change |(x 0 - x 1) / 4| ≤ 1 at hy1
    rw [abs_le] at hy0 hy1
    have hb : ‖x‖ ≤ 3 := (pi_norm_le_iff_of_nonneg (x := x) (by norm_num : (0 : ℝ) ≤ 3)).mpr (by
      intro i; fin_cases i
      · change ‖x 0‖ ≤ 3
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
      · change ‖x 1‖ ≤ 3
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
    linarith

#print axioms jordan_pair_has_full_endpoint_square_chart
#print axioms model_corner_diamond_homeomorph
