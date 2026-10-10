import CurveComplexGenusTwo.Octagon.WindowEdgeSlab
import CurveComplexGenusTwo.Octagon.GeneralEdgeNeighborhoodWave10

namespace CurveComplex.Octagon

theorem windowAngle_surjective_on (w : EdgeAngleWindow) (t : CollarAngle)
    (ht : w.lo ≤ (t : ℝ) ∧ (t : ℝ) ≤ w.hi) :
    ∃ s : ClosedCollarAngle, windowAngle w s = t := by
  have hd : 0 < w.hi - w.lo := sub_pos.mpr w.lo_lt_hi
  have hdne : w.hi - w.lo ≠ 0 := ne_of_gt hd
  have hq0 : 0 ≤ ((t : ℝ) - w.lo) / (w.hi - w.lo) :=
    div_nonneg (sub_nonneg.mpr ht.1) (le_of_lt hd)
  have hq1 : ((t : ℝ) - w.lo) / (w.hi - w.lo) ≤ 1 :=
    (div_le_iff₀ hd).2 (by linarith [ht.2])
  let s : ClosedCollarAngle :=
    ⟨1 / 4 + (((t : ℝ) - w.lo) / (w.hi - w.lo)) / 2, by
      constructor <;> linarith⟩
  refine ⟨s, Subtype.ext ?_⟩
  dsimp [windowAngle, s]
  field_simp [hdne]
  ring

private theorem windowRadius_eq_of_bound (r : CollarRadius)
    (hr : (3 / 4 : ℝ) ≤ (r : ℝ)) :
    ∃ s : ClosedCollarRadius, windowRadius s = r := by
  let s : ClosedCollarRadius := ⟨(r : ℝ), hr, r.2.2⟩
  exact ⟨s, Subtype.ext rfl⟩

private theorem reverseAngle_involutive (t : CollarAngle) :
    collarReverseAngle (collarReverseAngle t) = t := by
  apply Subtype.ext
  dsimp [collarReverseAngle]
  ring

theorem pairedLocalOpenCollars_subset_windowSlab
    (i : Side) (u : unitInterval) (δ : ℝ)
    (hδ0 : 0 < δ) (hδlo : δ < (u : ℝ))
    (hδhi : δ < 1 - (u : ℝ)) :
    ∃ w : EdgeAngleWindow,
      w.lo = (u : ℝ) - δ ∧ w.hi = (u : ℝ) + δ ∧
      pairedLocalOpenCollars i u (3 / 4) δ ⊆
        mk ⁻¹' Set.range (windowSlabMap w i) := by
  let w : EdgeAngleWindow :=
    ⟨(u : ℝ) - δ, (u : ℝ) + δ, by linarith,
      by linarith, by linarith⟩
  refine ⟨w, rfl, rfl, ?_⟩
  intro x hx
  rcases pairedLocalOpenCollars_parameters_in_closed_intervals
      i u (3 / 4) δ hx with hleft | hright
  · obtain ⟨p, hpx, hr, ht⟩ := hleft
    obtain ⟨r, hrp⟩ := windowRadius_eq_of_bound p.1 hr.1
    obtain ⟨t, htp⟩ := windowAngle_surjective_on w p.2 ht
    refine ⟨Sum.inl (r,t), ?_⟩
    change mk (collarPoint i (windowRadius r) (windowAngle w t)) = mk x
    rw [hrp, htp, hpx]
  · obtain ⟨p, hpx, hr, ht⟩ := hright
    obtain ⟨r, hrp⟩ := windowRadius_eq_of_bound p.1 hr.1
    have htr : w.lo ≤ (collarReverseAngle p.2 : ℝ) ∧
        (collarReverseAngle p.2 : ℝ) ≤ w.hi := by
      dsimp [w, collarReverseAngle]
      constructor <;> linarith [ht.1, ht.2]
    obtain ⟨t, htp⟩ := windowAngle_surjective_on w
      (collarReverseAngle p.2) htr
    refine ⟨Sum.inr (r,t), ?_⟩
    change mk (collarPoint (pair i) (windowRadius r)
      (collarReverseAngle (windowAngle w t))) = mk x
    rw [hrp, htp, reverseAngle_involutive, hpx]

private def nestedSubtypeHomeomorphWindow {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hts : t ⊆ s) :
    {x : s // (x : X) ∈ t} ≃ₜ t where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, hts y.2⟩, y.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro y; cases y; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem windowSlab_open_chart (w : EdgeAngleWindow) (i : Side)
    (W : Set Surface) (hWopen : IsOpen W)
    (hWsub : W ⊆ Set.range (windowSlabMap w i)) :
    ∃ U : Set SignedCollarRectangle, IsOpen U ∧ Nonempty (U ≃ₜ W) := by
  let e := windowSlabChart w i
  let U : Set SignedCollarRectangle :=
    e ⁻¹' ((Subtype.val : Set.range (windowSlabMap w i) → Surface) ⁻¹' W)
  have hU : IsOpen U :=
    (hWopen.preimage continuous_subtype_val).preimage e.continuous
  let e₁ : U ≃ₜ
      {q : Set.range (windowSlabMap w i) // (q : Surface) ∈ W} :=
    e.sets rfl
  let e₂ : {q : Set.range (windowSlabMap w i) // (q : Surface) ∈ W} ≃ₜ W :=
    nestedSubtypeHomeomorphWindow hWsub
  exact ⟨U, hU, ⟨e₁.trans e₂⟩⟩

/-- Every point in the interior of a paired octagon edge has an actual
ambient-open quotient chart in a signed rectangle. -/
theorem pairedEdge_every_interior_point_open_chart
    (i : Side) (u : unitInterval)
    (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1) :
    ∃ (_w : EdgeAngleWindow) (W : Set Surface)
      (U : Set SignedCollarRectangle),
      IsOpen W ∧ mk (side i u) ∈ W ∧
      IsOpen U ∧ Nonempty (U ≃ₜ W) := by
  obtain ⟨δ, W, hδ0, hδlo, hδhi, hWopen, hmid, hpre⟩ :=
    pairedEdge_every_interior_point_has_localCollarNeighborhood
      i u hu0 hu1 (3 / 4) (by norm_num) (by norm_num)
  obtain ⟨w, hlo, hhi, hlocal⟩ :=
    pairedLocalOpenCollars_subset_windowSlab i u δ hδ0 hδlo hδhi
  have hWsub : W ⊆ Set.range (windowSlabMap w i) := by
    intro q hq
    induction q using Quotient.inductionOn with
    | _ x => exact hlocal (hpre hq)
  obtain ⟨U, hU, hchart⟩ := windowSlab_open_chart w i W hWopen hWsub
  exact ⟨w, W, U, hWopen, hmid, hU, hchart⟩

end CurveComplex.Octagon
