import CurveComplexGenusTwo.Octagon.EdgeGlueRectangle

namespace CurveComplex.Octagon

private instance : CompactSpace ClosedCollarRadius := by infer_instance
private instance : CompactSpace ClosedCollarAngle := by infer_instance
private instance : CompactSpace PairedClosedCollars := by infer_instance
private instance (i : Side) : CompactSpace (Quotient (pairedSeamSetoid i)) :=
  Quotient.compactSpace
private instance : T2Space Surface := quotient_t2

noncomputable def seamToRectangle (i : Side) :
    Quotient (pairedSeamSetoid i) → SignedCollarRectangle :=
  Quotient.lift signedRectangleMap (by
    intro a b hab
    exact (signedRectangleMap_kernel_iff a b).2
      ((pairedSeamSetoid_iff i a b).1 hab))

theorem seamToRectangle_mk (i : Side) (a : PairedClosedCollars) :
    seamToRectangle i (Quotient.mk (pairedSeamSetoid i) a) =
      signedRectangleMap a := rfl

theorem continuous_seamToRectangle (i : Side) :
    Continuous (seamToRectangle i) :=
  continuous_signedRectangleMap.quotient_lift _

theorem seamToRectangle_bijective (i : Side) :
    Function.Bijective (seamToRectangle i) := by
  constructor
  · intro x y h
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        exact Quotient.sound
          ((pairedSeamSetoid_iff i a b).2
            ((signedRectangleMap_kernel_iff a b).1 h))
  · intro p
    obtain ⟨a, ha⟩ := signedRectangleMap_surjective p
    exact ⟨Quotient.mk (pairedSeamSetoid i) a, ha⟩

noncomputable def seamToRectangleHomeomorph (i : Side) :
    Quotient (pairedSeamSetoid i) ≃ₜ SignedCollarRectangle := by
  let f := seamToRectangle i
  have hclosed : IsClosedMap f := by
    intro s hs
    exact (hs.isCompact.image (continuous_seamToRectangle i)).isClosed
  exact (Equiv.ofBijective f (seamToRectangle_bijective i)).toHomeomorphOfContinuousClosed
    (continuous_seamToRectangle i) hclosed

theorem seamToRectangleHomeomorph_mk (i : Side) (a : PairedClosedCollars) :
    seamToRectangleHomeomorph i (Quotient.mk (pairedSeamSetoid i) a) =
      signedRectangleMap a :=
  seamToRectangle_mk i a

noncomputable def seamToSurfaceRange (i : Side) :
    Quotient (pairedSeamSetoid i) → Set.range (pairedClosedCollarMap i) :=
  Quotient.lift (fun a => (⟨pairedClosedCollarMap i a, ⟨a, rfl⟩⟩ :
    Set.range (pairedClosedCollarMap i))) (by
      intro a b hab
      apply Subtype.ext
      exact (pairedClosedCollar_kernel_iff i a b).2
        ((pairedSeamSetoid_iff i a b).1 hab))

theorem seamToSurfaceRange_mk (i : Side) (a : PairedClosedCollars) :
    ((seamToSurfaceRange i (Quotient.mk (pairedSeamSetoid i) a)) : Surface) =
      pairedClosedCollarMap i a := rfl

theorem continuous_seamToSurfaceRange (i : Side) :
    Continuous (seamToSurfaceRange i) := by
  apply Continuous.quotient_lift
  exact (continuous_pairedClosedCollarMap i).subtype_mk _

theorem seamToSurfaceRange_bijective (i : Side) :
    Function.Bijective (seamToSurfaceRange i) := by
  constructor
  · intro x y h
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        have hh : pairedClosedCollarMap i a = pairedClosedCollarMap i b :=
          congrArg Subtype.val h
        exact Quotient.sound
          ((pairedSeamSetoid_iff i a b).2
            ((pairedClosedCollar_kernel_iff i a b).1 hh))
  · rintro ⟨q, ⟨a, ha⟩⟩
    refine ⟨Quotient.mk (pairedSeamSetoid i) a, ?_⟩
    apply Subtype.ext
    exact ha

noncomputable def seamToSurfaceRangeHomeomorph (i : Side) :
    Quotient (pairedSeamSetoid i) ≃ₜ Set.range (pairedClosedCollarMap i) := by
  let f := seamToSurfaceRange i
  have hclosed : IsClosedMap f := by
    intro s hs
    exact (hs.isCompact.image (continuous_seamToSurfaceRange i)).isClosed
  exact (Equiv.ofBijective f (seamToSurfaceRange_bijective i)).toHomeomorphOfContinuousClosed
    (continuous_seamToSurfaceRange i) hclosed

theorem seamToSurfaceRangeHomeomorph_mk (i : Side) (a : PairedClosedCollars) :
    ((seamToSurfaceRangeHomeomorph i
      (Quotient.mk (pairedSeamSetoid i) a)) : Surface) =
      pairedClosedCollarMap i a :=
  seamToSurfaceRange_mk i a

noncomputable def pairedEdgeExplicitClosedSlabChart (i : Side) :
    SignedCollarRectangle ≃ₜ Set.range (pairedClosedCollarMap i) :=
  (seamToRectangleHomeomorph i).symm.trans
    (seamToSurfaceRangeHomeomorph i)

theorem pairedEdgeExplicitClosedSlabChart_apply (i : Side)
    (a : PairedClosedCollars) :
    ((pairedEdgeExplicitClosedSlabChart i (signedRectangleMap a)) : Surface) =
      pairedClosedCollarMap i a := by
  have hinv : (seamToRectangleHomeomorph i).symm (signedRectangleMap a) =
      Quotient.mk (pairedSeamSetoid i) a := by
    apply (seamToRectangleHomeomorph i).injective
    simpa using (seamToRectangleHomeomorph_mk i a).symm
  simpa [pairedEdgeExplicitClosedSlabChart, hinv] using
    seamToSurfaceRangeHomeomorph_mk i a

noncomputable def edgeMidAngle : ClosedCollarAngle := ⟨1 / 2, by constructor <;> norm_num⟩

noncomputable def signedEdgeMidpoint : SignedCollarRectangle :=
  (⟨0, by constructor <;> norm_num⟩, edgeMidAngle)

theorem pairedEdgeExplicitClosedSlabChart_midpoint (i : Side) :
    ((pairedEdgeExplicitClosedSlabChart i signedEdgeMidpoint) : Surface) =
      mk (side i (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval)) := by
  let a : PairedClosedCollars :=
    Sum.inl ((⟨1, by norm_num⟩ : ClosedCollarRadius), edgeMidAngle)
  have hparam : signedRectangleMap a = signedEdgeMidpoint := by
    apply Prod.ext
    · apply Subtype.ext
      norm_num [signedRectangleMap, signedLeft, a, signedEdgeMidpoint]
    · rfl
  rw [← hparam]
  have h := pairedEdgeExplicitClosedSlabChart_apply i a
  have hpoint : pairedClosedCollarMap i a =
      mk (side i (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval)) := by
    change mk (collarPoint i (⟨1, by norm_num⟩ : CollarRadius)
      (⟨1 / 2, by constructor <;> norm_num⟩ : CollarAngle)) = _
    rw [collarPoint_boundary]
    rfl
  exact h.trans hpoint

end CurveComplex.Octagon
