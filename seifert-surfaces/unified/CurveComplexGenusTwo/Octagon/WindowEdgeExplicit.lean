import CurveComplexGenusTwo.Octagon.WindowEdgeOpenChart
import CurveComplexGenusTwo.Octagon.EdgeGlueExplicit

namespace CurveComplex.Octagon

private instance : CompactSpace PairedClosedCollars := by infer_instance
private instance (i : Side) : CompactSpace (Quotient (pairedSeamSetoid i)) :=
  Quotient.compactSpace
private instance : T2Space Surface := quotient_t2

noncomputable def windowSeamToRange (w : EdgeAngleWindow) (i : Side) :
    Quotient (pairedSeamSetoid i) → Set.range (windowSlabMap w i) :=
  Quotient.lift (fun a => (⟨windowSlabMap w i a, ⟨a, rfl⟩⟩ :
    Set.range (windowSlabMap w i))) (by
      intro a b hab
      apply Subtype.ext
      exact (windowSlabMap_kernel_iff w i a b).2
        ((pairedSeamSetoid_iff i a b).1 hab))

theorem windowSeamToRange_mk (w : EdgeAngleWindow) (i : Side)
    (a : PairedClosedCollars) :
    ((windowSeamToRange w i
      (Quotient.mk (pairedSeamSetoid i) a)) : Surface) =
      windowSlabMap w i a := rfl

theorem continuous_windowSeamToRange (w : EdgeAngleWindow) (i : Side) :
    Continuous (windowSeamToRange w i) := by
  apply Continuous.quotient_lift
  exact (continuous_windowSlabMap w i).subtype_mk _

theorem windowSeamToRange_bijective (w : EdgeAngleWindow) (i : Side) :
    Function.Bijective (windowSeamToRange w i) := by
  constructor
  · intro x y h
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        have hh : windowSlabMap w i a = windowSlabMap w i b :=
          congrArg Subtype.val h
        exact Quotient.sound
          ((pairedSeamSetoid_iff i a b).2
            ((windowSlabMap_kernel_iff w i a b).1 hh))
  · rintro ⟨q, ⟨a, ha⟩⟩
    refine ⟨Quotient.mk (pairedSeamSetoid i) a, ?_⟩
    apply Subtype.ext
    exact ha

noncomputable def windowSeamToRangeHomeomorph (w : EdgeAngleWindow) (i : Side) :
    Quotient (pairedSeamSetoid i) ≃ₜ Set.range (windowSlabMap w i) := by
  let f := windowSeamToRange w i
  have hclosed : IsClosedMap f := by
    intro s hs
    exact (hs.isCompact.image (continuous_windowSeamToRange w i)).isClosed
  exact (Equiv.ofBijective f (windowSeamToRange_bijective w i)).toHomeomorphOfContinuousClosed
    (continuous_windowSeamToRange w i) hclosed

theorem windowSeamToRangeHomeomorph_mk (w : EdgeAngleWindow) (i : Side)
    (a : PairedClosedCollars) :
    ((windowSeamToRangeHomeomorph w i
      (Quotient.mk (pairedSeamSetoid i) a)) : Surface) =
      windowSlabMap w i a :=
  windowSeamToRange_mk w i a

noncomputable def windowExplicitSlabChart (w : EdgeAngleWindow) (i : Side) :
    SignedCollarRectangle ≃ₜ Set.range (windowSlabMap w i) :=
  (seamToRectangleHomeomorph i).symm.trans
    (windowSeamToRangeHomeomorph w i)

theorem windowExplicitSlabChart_apply (w : EdgeAngleWindow) (i : Side)
    (a : PairedClosedCollars) :
    ((windowExplicitSlabChart w i (signedRectangleMap a)) : Surface) =
      windowSlabMap w i a := by
  have hinv : (seamToRectangleHomeomorph i).symm (signedRectangleMap a) =
      Quotient.mk (pairedSeamSetoid i) a := by
    apply (seamToRectangleHomeomorph i).injective
    simpa using (seamToRectangleHomeomorph_mk i a).symm
  simpa [windowExplicitSlabChart, hinv] using
    windowSeamToRangeHomeomorph_mk w i a

theorem windowAngle_surjective_on_strict (w : EdgeAngleWindow)
    (t : CollarAngle)
    (hlo : w.lo < (t : ℝ)) (hhi : (t : ℝ) < w.hi) :
    ∃ s : ClosedCollarAngle,
      (1 / 4 : ℝ) < (s : ℝ) ∧ (s : ℝ) < (3 / 4 : ℝ) ∧
      windowAngle w s = t := by
  have hd : 0 < w.hi - w.lo := sub_pos.mpr w.lo_lt_hi
  have hq0 : 0 < ((t : ℝ) - w.lo) / (w.hi - w.lo) :=
    div_pos (sub_pos.mpr hlo) hd
  have hq1 : ((t : ℝ) - w.lo) / (w.hi - w.lo) < 1 :=
    (div_lt_iff₀ hd).2 (by linarith)
  obtain ⟨s, hs⟩ := windowAngle_surjective_on w t
    ⟨le_of_lt hlo, le_of_lt hhi⟩
  have hval := congrArg (fun z : CollarAngle => (z : ℝ)) hs
  have hformula : (s : ℝ) = 1 / 4 +
      (((t : ℝ) - w.lo) / (w.hi - w.lo)) / 2 := by
    dsimp [windowAngle] at hval
    have hdne : w.hi - w.lo ≠ 0 := ne_of_gt hd
    field_simp [hdne] at *
    nlinarith
  exact ⟨s, by linarith, by linarith, hs⟩

theorem windowExplicitSlabChart_seam (w : EdgeAngleWindow)
    (i : Side) (u : unitInterval)
    (hu0 : w.lo < (u : ℝ)) (hu1 : (u : ℝ) < w.hi) :
    ∃ s : ClosedCollarAngle,
      (1 / 4 : ℝ) < (s : ℝ) ∧ (s : ℝ) < (3 / 4 : ℝ) ∧
      ((windowExplicitSlabChart w i
        (⟨0, by constructor <;> norm_num⟩, s)) : Surface) =
          mk (side i u) := by
  let t : CollarAngle := ⟨(u : ℝ),
    lt_trans w.lo_pos hu0,
    lt_trans hu1 w.hi_lt_one⟩
  obtain ⟨s, hslo, hshi, hs⟩ :=
    windowAngle_surjective_on_strict w t hu0 hu1
  refine ⟨s, hslo, hshi, ?_⟩
  let a : PairedClosedCollars :=
    Sum.inl ((⟨1, by norm_num⟩ : ClosedCollarRadius), s)
  have hparam : signedRectangleMap a =
      (⟨0, by constructor <;> norm_num⟩, s) := by
    apply Prod.ext
    · apply Subtype.ext
      norm_num [signedRectangleMap, signedLeft, a]
    · rfl
  rw [← hparam]
  rw [windowExplicitSlabChart_apply]
  change mk (collarPoint i (windowRadius ⟨1, by norm_num⟩)
    (windowAngle w s)) = mk (side i u)
  rw [hs]
  have hr : windowRadius (⟨1, by norm_num⟩ : ClosedCollarRadius) =
      (⟨1, by norm_num⟩ : CollarRadius) := rfl
  rw [hr, collarPoint_boundary]
  congr 1

end CurveComplex.Octagon
