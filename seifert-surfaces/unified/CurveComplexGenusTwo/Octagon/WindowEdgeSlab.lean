import CurveComplexGenusTwo.Octagon.UniversalEdgeCollar

namespace CurveComplex.Octagon

/-- A compact angular interval strictly inside an octagon side. -/
structure EdgeAngleWindow where
  lo : ℝ
  hi : ℝ
  lo_pos : 0 < lo
  lo_lt_hi : lo < hi
  hi_lt_one : hi < 1

noncomputable def windowRadius (r : ClosedCollarRadius) : CollarRadius :=
  ⟨r.1, by
    constructor
    · linarith [r.2.1]
    · exact r.2.2⟩

noncomputable def windowAngle (w : EdgeAngleWindow)
    (t : ClosedCollarAngle) : CollarAngle := by
  let ell : ℝ := 2 * (t : ℝ) - 1 / 2
  have hell0 : 0 ≤ ell := by
    dsimp [ell]
    linarith [t.2.1]
  have hell1 : ell ≤ 1 := by
    dsimp [ell]
    linarith [t.2.2]
  have hd : 0 < w.hi - w.lo := sub_pos.mpr w.lo_lt_hi
  have hlower : w.lo ≤ w.lo + (w.hi - w.lo) * ell := by
    nlinarith [mul_nonneg (le_of_lt hd) hell0]
  have hupper : w.lo + (w.hi - w.lo) * ell ≤ w.hi := by
    nlinarith [mul_nonneg (le_of_lt hd) (sub_nonneg.mpr hell1)]
  exact ⟨w.lo + (w.hi - w.lo) * ell, by
    constructor <;> linarith [w.lo_pos, w.hi_lt_one]⟩

theorem windowAngle_injective (w : EdgeAngleWindow) :
    Function.Injective (windowAngle w) := by
  intro t u h
  have hh := congrArg (fun z : CollarAngle => (z : ℝ)) h
  dsimp [windowAngle] at hh
  have hd : w.hi - w.lo ≠ 0 := ne_of_gt (sub_pos.mpr w.lo_lt_hi)
  have hmul : (w.hi - w.lo) * (2 * (t : ℝ) - 1 / 2) =
      (w.hi - w.lo) * (2 * (u : ℝ) - 1 / 2) := by
    linarith
  have hell := mul_left_cancel₀ hd hmul
  apply Subtype.ext
  linarith

noncomputable def windowCollarEmbedding (w : EdgeAngleWindow) :
    PairedClosedCollars → UniversalPairedCollars
  | Sum.inl p => Sum.inl (windowRadius p.1, windowAngle w p.2)
  | Sum.inr p => Sum.inr (windowRadius p.1, windowAngle w p.2)

theorem windowCollarEmbedding_injective (w : EdgeAngleWindow) :
    Function.Injective (windowCollarEmbedding w) := by
  rintro (⟨r,t⟩ | ⟨r,t⟩) (⟨s,u⟩ | ⟨s,u⟩) h
  · have hh : (windowRadius r, windowAngle w t) =
        (windowRadius s, windowAngle w u) := Sum.inl.inj h
    have hr : r = s := Subtype.ext (by
      simpa [windowRadius] using congrArg (fun z : CollarRadius => (z : ℝ))
        (congrArg Prod.fst hh))
    have ht : t = u := windowAngle_injective w (congrArg Prod.snd hh)
    exact congrArg Sum.inl (Prod.ext hr ht)
  · cases h
  · cases h
  · have hh : (windowRadius r, windowAngle w t) =
        (windowRadius s, windowAngle w u) := Sum.inr.inj h
    have hr : r = s := Subtype.ext (by
      simpa [windowRadius] using congrArg (fun z : CollarRadius => (z : ℝ))
        (congrArg Prod.fst hh))
    have ht : t = u := windowAngle_injective w (congrArg Prod.snd hh)
    exact congrArg Sum.inr (Prod.ext hr ht)

noncomputable def windowSlabMap (w : EdgeAngleWindow) (i : Side) :
    PairedClosedCollars → Surface :=
  universalCollarMap i ∘ windowCollarEmbedding w

theorem continuous_windowSlabMap (w : EdgeAngleWindow) (i : Side) :
    Continuous (windowSlabMap w i) := by
  apply continuous_sum_dom.mpr
  constructor
  · have hr : Continuous windowRadius :=
      Continuous.subtype_mk continuous_subtype_val _
    have ht : Continuous (windowAngle w) := by
      apply Continuous.subtype_mk
      fun_prop
    have hp : Continuous (fun p : ClosedCollarRadius × ClosedCollarAngle =>
        (windowRadius p.1, windowAngle w p.2)) :=
      (hr.comp continuous_fst).prodMk (ht.comp continuous_snd)
    exact continuous_mk.comp ((collarPoint_continuous i).comp hp)
  · have hr : Continuous windowRadius :=
      Continuous.subtype_mk continuous_subtype_val _
    have ht : Continuous (windowAngle w) := by
      apply Continuous.subtype_mk
      fun_prop
    have hp : Continuous (fun p : ClosedCollarRadius × ClosedCollarAngle =>
        (windowRadius p.1, collarReverseAngle (windowAngle w p.2))) :=
      (hr.comp continuous_fst).prodMk
        ((Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _ :
          Continuous collarReverseAngle).comp (ht.comp continuous_snd))
    exact continuous_mk.comp ((collarPoint_continuous (pair i)).comp hp)

theorem windowSlabMap_kernel_iff (w : EdgeAngleWindow) (i : Side)
    (a b : PairedClosedCollars) :
    windowSlabMap w i a = windowSlabMap w i b ↔ PairedSeam a b := by
  change universalCollarMap i (windowCollarEmbedding w a) =
    universalCollarMap i (windowCollarEmbedding w b) ↔ PairedSeam a b
  rw [universalCollarMap_kernel_iff]
  constructor
  · intro h
    rcases h with h | ⟨t, h | h⟩
    · exact Or.inl (windowCollarEmbedding_injective w h)
    · rcases a with ⟨r,u⟩ | ⟨r,u⟩ <;>
      rcases b with ⟨s,v⟩ | ⟨s,v⟩
      · cases h.2
      · obtain ⟨hr, ht⟩ := h
        have hr' : r = (⟨1, by norm_num⟩ : ClosedCollarRadius) :=
          Subtype.ext (congrArg (fun z : CollarRadius => (z : ℝ))
            (congrArg Prod.fst (Sum.inl.inj hr)))
        have hs' : s = (⟨1, by norm_num⟩ : ClosedCollarRadius) :=
          Subtype.ext (congrArg (fun z : CollarRadius => (z : ℝ))
            (congrArg Prod.fst (Sum.inr.inj ht)))
        have hu : u = v := windowAngle_injective w (by
          calc
            windowAngle w u = t := congrArg Prod.snd (Sum.inl.inj hr)
            _ = windowAngle w v := (congrArg Prod.snd (Sum.inr.inj ht)).symm)
        subst r; subst s; subst v
        exact Or.inr ⟨u, Or.inl ⟨rfl,rfl⟩⟩
      · cases h.2
      · cases h.1
    · rcases a with ⟨r,u⟩ | ⟨r,u⟩ <;>
      rcases b with ⟨s,v⟩ | ⟨s,v⟩
      · cases h.1
      · cases h.1
      · obtain ⟨hr, ht⟩ := h
        have hr' : r = (⟨1, by norm_num⟩ : ClosedCollarRadius) :=
          Subtype.ext (congrArg (fun z : CollarRadius => (z : ℝ))
            (congrArg Prod.fst (Sum.inr.inj hr)))
        have hs' : s = (⟨1, by norm_num⟩ : ClosedCollarRadius) :=
          Subtype.ext (congrArg (fun z : CollarRadius => (z : ℝ))
            (congrArg Prod.fst (Sum.inl.inj ht)))
        have hu : u = v := windowAngle_injective w (by
          calc
            windowAngle w u = t := congrArg Prod.snd (Sum.inr.inj hr)
            _ = windowAngle w v := (congrArg Prod.snd (Sum.inl.inj ht)).symm)
        subst r; subst s; subst v
        exact Or.inr ⟨u, Or.inr ⟨rfl,rfl⟩⟩
      · cases h.2
  · intro h
    rcases h with rfl | ⟨t, h | h⟩
    · exact Or.inl rfl
    · rcases h with ⟨rfl,rfl⟩
      exact Or.inr ⟨windowAngle w t, Or.inl ⟨rfl,rfl⟩⟩
    · rcases h with ⟨rfl,rfl⟩
      exact Or.inr ⟨windowAngle w t, Or.inr ⟨rfl,rfl⟩⟩

private instance : CompactSpace PairedClosedCollars := by infer_instance
private instance : T2Space Surface := quotient_t2

theorem windowSlabMap_isStrictMap (w : EdgeAngleWindow) (i : Side) :
    Topology.IsStrictMap (windowSlabMap w i) := by
  have hclosed : IsClosedMap (windowSlabMap w i) := by
    intro s hs
    exact (hs.isCompact.image (continuous_windowSlabMap w i)).isClosed
  exact hclosed.isStrictMap (continuous_windowSlabMap w i)

noncomputable def windowSlabChart (w : EdgeAngleWindow) (i : Side) :
    SignedCollarRectangle ≃ₜ Set.range (windowSlabMap w i) := by
  have hsetoid : Setoid.ker (windowSlabMap w i) = pairedSeamSetoid i := by
    apply Setoid.ext
    intro a b
    exact (windowSlabMap_kernel_iff w i a b).trans
      (pairedSeamSetoid_iff i a b).symm
  let e : Quotient (Setoid.ker (windowSlabMap w i)) ≃ₜ
      Set.range (windowSlabMap w i) :=
    Homeomorph.quotientKerEquivRange (windowSlabMap_isStrictMap w i)
  rw [hsetoid] at e
  exact (pairedSeam_quotientRectangle i).symm.trans e

end CurveComplex.Octagon
