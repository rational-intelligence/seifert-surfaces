import Mathlib

/-!
Based-loop obligations used in Theorem B's limit argument, PDF p. 6.
`GenLoop.Homotopic` fixes the cube boundary throughout the homotopy.
An arbitrary contraction need not fix its basepoint; the first theorem repairs
the resulting uniform boundary path rather than treating it as fixed.
-/

namespace SeifertSurfaces.WhiteheadSupport

universe u v

open Topology Set
open scoped unitInterval

/-- Universe-polymorphic version of the existing uniform-boundary-path repair.
The hypotheses are actual endpoint and boundary equations for a continuous map. -/
theorem cube_loop_nullhomotopy_uniform_boundary_path
    {Y : Type u} [TopologicalSpace Y] (n : ℕ) (hn : 1 ≤ n)
    (y z : Y) (p : Path y z) (f : GenLoop (Fin n) Y y)
    (H : C(unitInterval × (Fin n → unitInterval), Y))
    (H0 : ∀ a, H (0, a) = f a)
    (H1 : ∀ a, H (1, a) = z)
    (Hb : ∀ t a, a ∈ Cube.boundary (Fin n) → H (t, a) = p t) :
    GenLoop.Homotopic f (GenLoop.const (N := Fin n) (X := Y) (x := y)) := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let v (a : Fin n → I) : Fin n → ℝ := fun i => 2*(a i:ℝ)-1
  let r (a : Fin n → I) := ‖v a‖
  have hr : Continuous r := by unfold r v; fun_prop
  let c : C((Fin n → I),(Fin n → I)) :=
    ⟨fun a i => projIcc 0 1 zero_le_one (2*(a i:ℝ)-1/2),by fun_prop⟩
  have hrle (a : Fin n → I) : r a ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    rw [Real.norm_eq_abs,abs_le]
    dsimp [v]
    constructor <;> nlinarith [(a i).property.1,(a i).property.2]
  have hcb (a : Fin n → I) (ha : 1/2 ≤ r a) : c a ∈ Cube.boundary (Fin n) := by
    obtain ⟨i,hi⟩ := (IsGreatest.pi_norm (v a)).1
    have h : 1/2 ≤ |2*(a i:ℝ)-1| := by
      change ‖v a i‖ = ‖v a‖ at hi
      rw [← Real.norm_eq_abs]
      exact hi.symm ▸ ha
    rcases le_abs.mp h with h|h
    · refine ⟨i,Or.inr ?_⟩
      change projIcc 0 1 zero_le_one _ = 1
      exact projIcc_of_right_le zero_le_one (by linarith)
    · refine ⟨i,Or.inl ?_⟩
      change projIcc 0 1 zero_le_one _ = 0
      exact projIcc_of_le_left zero_le_one (by linarith)
  have hrb (a : Fin n → I) (ha : a ∈ Cube.boundary (Fin n)) : r a = 1 := by
    rcases ha with ⟨i,hi|hi⟩
    all_goals
      apply le_antisymm (hrle a)
      have h := norm_le_pi_norm (v a) i
      dsimp [v] at h
      norm_num [hi,r,v] at h ⊢
      exact h
  let d : C((Fin n → I),I) :=
    ⟨fun a => projIcc 0 1 zero_le_one (2-2*r a),continuous_projIcc.comp (by fun_prop)⟩
  have hdhalf (a) (ha : r a = 1/2) : d a = 1 := by
    apply Subtype.ext
    norm_num [d,ha,coe_projIcc]
  have hdone (a) (ha : r a = 1) : d a = 0 := by
    apply Subtype.ext
    norm_num [d,ha,coe_projIcc]
  have hdinner (a) (ha : r a ≤ 1/2) : d a = 1 := by
    change projIcc 0 1 zero_le_one (2-2*r a) = 1
    exact projIcc_of_right_le zero_le_one (by linarith)
  have hcb' (a) (ha : a ∈ Cube.boundary (Fin n)) : c a ∈ Cube.boundary (Fin n) :=
    hcb a (by rw [hrb a ha]; norm_num)
  let fpad : GenLoop (Fin n) Y y := ⟨f.val.comp c,fun a ha => GenLoop.boundary f _ (hcb' a ha)⟩
  let w : GenLoop (Fin n) Y y := ⟨p.toContinuousMap.comp d,by
    intro a ha
    change p (d a) = y
    rw [hdone a (hrb a ha)]
    exact p.source⟩
  let G (ta : I × (Fin n → I)) :=
    if r ta.2 ≤ 1/2 then H (ta.1,c ta.2) else p (projIcc 0 1 zero_le_one ((ta.1:ℝ)*(d ta.2:ℝ)))
  have hG : Continuous G := by
    apply Continuous.if ?_ (H.continuous.comp (by fun_prop))
      (p.continuous.comp (continuous_projIcc.comp (by fun_prop)))
    intro ta ha
    have he := frontier_le_subset_eq (hr.comp continuous_snd)
      (continuous_const : Continuous (fun _ : I × (Fin n → I) => (1/2:ℝ))) ha
    change r ta.2 = 1/2 at he
    change H (ta.1,c ta.2) = p (projIcc 0 1 zero_le_one ((ta.1:ℝ)*(d ta.2:ℝ)))
    rw [Hb _ _ (hcb ta.2 he.ge),hdhalf ta.2 he]
    simp [projIcc_val]
  have hGb (t : I) (a : Fin n → I) (ha : a ∈ Cube.boundary (Fin n)) : G (t,a) = y := by
    dsimp only [G]
    rw [ite_eq_right (by rw [hrb a ha]; norm_num),hdone a (hrb a ha)]
    simp [p.source,projIcc_left]
  have hGw : GenLoop.Homotopic fpad w := by
    exact ⟨{
      toFun := G
      continuous_toFun := hG
      map_zero_left := by
        intro a
        dsimp only [G]
        split_ifs with ha
        · exact H0 (c a)
        · change p (projIcc 0 1 zero_le_one (((0:I):ℝ) * (d a:ℝ))) = f (c a)
          change p (projIcc 0 1 zero_le_one (0 * (d a:ℝ))) = f (c a)
          simp only [zero_mul]
          have hz : projIcc 0 1 zero_le_one (0:ℝ) = (0:I) := by
            apply Subtype.ext
            norm_num [coe_projIcc]
          rw [hz,p.source]
          exact (GenLoop.boundary f _ (hcb a (le_of_not_ge ha))).symm
      map_one_left := by
        intro a
        dsimp only [G]
        split_ifs with ha
        · change H (1,c a) = p (d a)
          rw [H1,hdinner a ha,p.target]
        · change p (projIcc 0 1 zero_le_one (1*(d a:ℝ))) = p (d a)
          simp [projIcc_val]
      prop' := by
        intro t a ha
        change G (t,a) = fpad a
        exact (hGb t a ha).trans (GenLoop.boundary fpad a ha).symm
    }⟩
  have hw : GenLoop.Homotopic w (GenLoop.const (N := Fin n) (X := Y) (x := y)) := by
    exact ⟨{
      toFun := fun ta => p (projIcc 0 1 zero_le_one ((1-(ta.1:ℝ))*(d ta.2:ℝ)))
      continuous_toFun := p.continuous.comp (continuous_projIcc.comp (by fun_prop))
      map_zero_left := by intro a; simp [projIcc_val]; rfl
      map_one_left := by intro a; simp [projIcc_left]
      prop' := by
        intro t a ha
        change p (projIcc 0 1 zero_le_one ((1-(t:ℝ))*(d a:ℝ))) = p (d a)
        rw [hdone a (hrb a ha)]
        simp [projIcc_left]
    }⟩
  have hfpad : GenLoop.Homotopic f fpad := by
    let d₀ : C(I,I) := ⟨fun t => projIcc 0 1 zero_le_one (2*(t:ℝ)-1/2),
      continuous_projIcc.comp (by fun_prop)⟩
    have hd0 : d₀ 0 = 0 := by apply Subtype.ext; norm_num [d₀,coe_projIcc]
    have hd1 : d₀ 1 = 1 := by apply Subtype.ext; norm_num [d₀,coe_projIcc]
    let A : C(I × (Fin n → I),(Fin n → I)) :=
      ⟨fun ta i => projIcc 0 1 zero_le_one
        ((1-(ta.1:ℝ))*(ta.2 i:ℝ)+(ta.1:ℝ)*(c ta.2 i:ℝ)),by fun_prop⟩
    have A0 (a) : A (0,a) = a := by funext i; simp [A,projIcc_val]
    have A1 (a) : A (1,a) = c a := by funext i; simp [A,projIcc_val]
    have Ab (t : I) (a : Fin n → I) (ha : a ∈ Cube.boundary (Fin n)) :
        A (t,a) ∈ Cube.boundary (Fin n) := by
      rcases ha with ⟨i,hi|hi⟩
      · refine ⟨i,Or.inl ?_⟩
        have hc : c a i = 0 := by change d₀ (a i) = 0; rw [hi,hd0]
        change projIcc 0 1 zero_le_one _ = 0
        simp [hi,hc,projIcc_left]
      · refine ⟨i,Or.inr ?_⟩
        have hc : c a i = 1 := by change d₀ (a i) = 1; rw [hi,hd1]
        change projIcc 0 1 zero_le_one _ = 1
        simp only [hi,hc]
        change projIcc 0 1 zero_le_one ((1-(t:ℝ))*1+(t:ℝ)*1) = 1
        have ht : (1-(t:ℝ))*1+(t:ℝ)*1 = 1 := by ring
        rw [ht]
        exact projIcc_right zero_le_one
    exact ⟨{
      toFun := fun ta => f (A ta)
      continuous_toFun := f.val.continuous.comp A.continuous
      map_zero_left := by intro a; rw [A0]; rfl
      map_one_left := by intro a; rw [A1]; rfl
      prop' := by
        intro t a ha
        exact (GenLoop.boundary f _ (Ab t a ha)).trans (GenLoop.boundary f a ha).symm
    }⟩
  exact hfpad.trans (hGw.trans hw)

/-- Every positive-dimensional based loop in a contractible space admits a
nullhomotopy relative to its boundary, even when the contraction moves `y`. -/
theorem cube_loop_nullhomotopic_of_contractible
    {Y : Type u} [TopologicalSpace Y] [ContractibleSpace Y]
    (n : ℕ) (hn : 1 ≤ n) (y : Y) (f : GenLoop (Fin n) Y y) :
    GenLoop.Homotopic f (GenLoop.const (N := Fin n) (X := Y) (x := y)) := by
  obtain ⟨z, ⟨K⟩⟩ := id_nullhomotopic Y
  let p : Path y z := {
    toFun := fun t => K (t, y)
    continuous_toFun := K.continuous.comp (by fun_prop)
    source' := K.apply_zero y
    target' := K.apply_one y }
  let H : C(unitInterval × (Fin n → unitInterval), Y) :=
    ⟨fun ta => K (ta.1, f ta.2), K.continuous.comp (by fun_prop)⟩
  apply cube_loop_nullhomotopy_uniform_boundary_path n hn y z p f H
  · exact fun a => K.apply_zero (f a)
  · exact fun a => K.apply_one (f a)
  · intro t a ha
    change K (t, f a) = K (t, y)
    rw [GenLoop.boundary f a ha]

/-- The relative-nullhomotopy result implies trivial positive homotopy groups. -/
theorem pi_subsingleton_of_contractible
    {Y : Type u} [TopologicalSpace Y] [ContractibleSpace Y]
    (n : ℕ) (hn : 1 ≤ n) (y : Y) :
    Subsingleton (HomotopyGroup.Pi n Y y) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn with
  | h f =>
    induction b using Quotient.inductionOn with
    | h g =>
      exact Quotient.sound
        ((cube_loop_nullhomotopic_of_contractible n hn y f).trans
          (cube_loop_nullhomotopic_of_contractible n hn y g).symm)

/-- A based loop factoring through a contractible space is relatively null.
The inclusion is an actual continuous map, with both its basepoint and map
equations exposed. This is a proved transport obligation, not assumed data. -/
theorem cube_loop_nullhomotopic_of_contractible_factor
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    [ContractibleSpace Z]
    (n : ℕ) (hn : 1 ≤ n) (y : Y) (z : Z) (j : C(Z, Y))
    (hj : j z = y)
    (f : GenLoop (Fin n) Y y) (g : GenLoop (Fin n) Z z)
    (hfactor : ∀ a, j (g a) = f a) :
    GenLoop.Homotopic f (GenLoop.const (N := Fin n) (X := Y) (x := y)) := by
  obtain ⟨K⟩ := cube_loop_nullhomotopic_of_contractible n hn z g
  refine ⟨{
    toFun := fun ta => j (K ta)
    continuous_toFun := j.continuous.comp K.continuous
    map_zero_left := fun a => (congrArg j (K.apply_zero a)).trans (hfactor a)
    map_one_left := fun a => (congrArg j (K.apply_one a)).trans hj
    prop' := ?_ }⟩
  intro t a ha
  change j (K (t, a)) = f a
  exact (congrArg j (K.prop t a ha)).trans (hfactor a)

end SeifertSurfaces.WhiteheadSupport
