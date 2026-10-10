import CurveComplexGenusTwo.Octagon.EdgeGlueCompact

namespace CurveComplex.Octagon

abbrev SignedCollarRadius := Set.Icc (-1 / 4 : ℝ) (1 / 4)
abbrev SignedCollarRectangle := SignedCollarRadius × ClosedCollarAngle

private instance : CompactSpace ClosedCollarRadius := by infer_instance
private instance : CompactSpace ClosedCollarAngle := by infer_instance
private instance : T2Space Surface := quotient_t2

noncomputable def signedLeft (r : ClosedCollarRadius) : SignedCollarRadius :=
  ⟨1 - r.1, by
    constructor <;> have h₁ := r.2.1 <;> have h₂ := r.2.2 <;> linarith⟩

noncomputable def signedRight (r : ClosedCollarRadius) : SignedCollarRadius :=
  ⟨r.1 - 1, by
    constructor <;> have h₁ := r.2.1 <;> have h₂ := r.2.2 <;> linarith⟩

noncomputable def signedRectangleMap : PairedClosedCollars → SignedCollarRectangle
  | Sum.inl p => (signedLeft p.1, p.2)
  | Sum.inr p => (signedRight p.1, p.2)

theorem continuous_signedRectangleMap : Continuous signedRectangleMap := by
  apply continuous_sum_dom.mpr
  constructor
  · have hleft : Continuous signedLeft :=
      Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _
    exact (hleft.comp continuous_fst).prodMk continuous_snd
  · have hright : Continuous signedRight :=
      Continuous.subtype_mk (continuous_subtype_val.sub continuous_const) _
    exact (hright.comp continuous_fst).prodMk continuous_snd

theorem signedRectangleMap_surjective : Function.Surjective signedRectangleMap := by
  rintro ⟨s, t⟩
  by_cases hs : 0 ≤ (s : ℝ)
  · let r : ClosedCollarRadius := ⟨1 - s.1, by
      constructor <;> have h₁ := s.2.1 <;> have h₂ := s.2.2 <;> linarith⟩
    refine ⟨Sum.inl (r, t), ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      dsimp [signedRectangleMap, signedLeft, r]
      ring
    · rfl
  · let r : ClosedCollarRadius := ⟨1 + s.1, by
      constructor <;> have h₁ := s.2.1 <;> have h₂ := s.2.2 <;> linarith⟩
    refine ⟨Sum.inr (r, t), ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      dsimp [signedRectangleMap, signedRight, r]
      ring
    · rfl

theorem signedRectangleMap_kernel_iff (a b : PairedClosedCollars) :
    signedRectangleMap a = signedRectangleMap b ↔ PairedSeam a b := by
  constructor
  · intro h
    rcases a with ⟨p⟩ | ⟨p⟩ <;> rcases b with ⟨q⟩ | ⟨q⟩
    · rcases p with ⟨r, t⟩
      rcases q with ⟨s, u⟩
      have hrad : r = s := by
        apply Subtype.ext
        have hh := congrArg (fun z : SignedCollarRectangle => ((z.1 : SignedCollarRadius) : ℝ)) h
        dsimp [signedRectangleMap, signedLeft] at hh
        linarith
      have hang : t = u := congrArg Prod.snd h
      exact Or.inl (congrArg Sum.inl (Prod.ext hrad hang))
    · rcases p with ⟨r, t⟩
      rcases q with ⟨s, u⟩
      have hh := congrArg (fun z : SignedCollarRectangle => ((z.1 : SignedCollarRadius) : ℝ)) h
      dsimp [signedRectangleMap, signedLeft, signedRight] at hh
      have hr : (r : ℝ) = 1 := by
        have hrle := r.2.2
        have hsle := s.2.2
        linarith
      have hs : (s : ℝ) = 1 := by
        have hrle := r.2.2
        have hsle := s.2.2
        linarith
      have hrad : r = ⟨1, by norm_num⟩ := Subtype.ext hr
      have hsad : s = ⟨1, by norm_num⟩ := Subtype.ext hs
      have hang : t = u := congrArg Prod.snd h
      subst r
      subst s
      subst u
      exact Or.inr ⟨t, Or.inl ⟨rfl, rfl⟩⟩
    · rcases p with ⟨r, t⟩
      rcases q with ⟨s, u⟩
      have hh := congrArg (fun z : SignedCollarRectangle => ((z.1 : SignedCollarRadius) : ℝ)) h
      dsimp [signedRectangleMap, signedLeft, signedRight] at hh
      have hr : (r : ℝ) = 1 := by
        have hrle := r.2.2
        have hsle := s.2.2
        linarith
      have hs : (s : ℝ) = 1 := by
        have hrle := r.2.2
        have hsle := s.2.2
        linarith
      have hrad : r = ⟨1, by norm_num⟩ := Subtype.ext hr
      have hsad : s = ⟨1, by norm_num⟩ := Subtype.ext hs
      have hang : t = u := congrArg Prod.snd h
      subst r
      subst s
      subst u
      exact Or.inr ⟨t, Or.inr ⟨rfl, rfl⟩⟩
    · rcases p with ⟨r, t⟩
      rcases q with ⟨s, u⟩
      have hrad : r = s := by
        apply Subtype.ext
        have hh := congrArg (fun z : SignedCollarRectangle => ((z.1 : SignedCollarRadius) : ℝ)) h
        dsimp [signedRectangleMap, signedRight] at hh
        linarith
      have hang : t = u := congrArg Prod.snd h
      exact Or.inl (congrArg Sum.inr (Prod.ext hrad hang))
  · intro h
    rcases h with rfl | ⟨t, h | h⟩
    · rfl
    · rcases h with ⟨rfl, rfl⟩
      apply Prod.ext
      · apply Subtype.ext
        norm_num [signedRectangleMap, signedLeft, signedRight]
      · rfl
    · rcases h with ⟨rfl, rfl⟩
      apply Prod.ext
      · apply Subtype.ext
        norm_num [signedRectangleMap, signedLeft, signedRight]
      · rfl

private instance : CompactSpace PairedClosedCollars := by infer_instance

theorem signedRectangleMap_isStrictMap :
    Topology.IsStrictMap signedRectangleMap := by
  have hclosed : IsClosedMap signedRectangleMap := by
    intro s hs
    exact (hs.isCompact.image continuous_signedRectangleMap).isClosed
  exact hclosed.isStrictMap continuous_signedRectangleMap

noncomputable def pairedSeam_quotientRectangle (i : Side) :
    Quotient (pairedSeamSetoid i) ≃ₜ SignedCollarRectangle := by
  have hsetoid : Setoid.ker signedRectangleMap = pairedSeamSetoid i := by
    apply Setoid.ext
    intro a b
    exact (signedRectangleMap_kernel_iff a b).trans
      (pairedSeamSetoid_iff i a b).symm
  let e : Quotient (Setoid.ker signedRectangleMap) ≃ₜ
      Set.range signedRectangleMap :=
    Homeomorph.quotientKerEquivRange signedRectangleMap_isStrictMap
  let e' : Set.range signedRectangleMap ≃ₜ SignedCollarRectangle :=
    (Homeomorph.setCongr (Set.range_eq_univ.mpr signedRectangleMap_surjective)).trans
      (Homeomorph.Set.univ SignedCollarRectangle)
  rw [hsetoid] at e
  exact e.trans e'

/-- The actual paired-edge slab in the octagon quotient is a closed
rectangle with the seam in its interior. -/
noncomputable def pairedEdgeClosedSlabChart (i : Side) :
    SignedCollarRectangle ≃ₜ Set.range (pairedClosedCollarMap i) :=
  (pairedSeam_quotientRectangle i).symm.trans
    (pairedClosedCollar_quotientHomeomorph i)

private def nestedSubtypeHomeomorph {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hts : t ⊆ s) :
    {x : s // (x : X) ∈ t} ≃ₜ t where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, hts y.2⟩, y.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro y; cases y; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Once an ambient-open neighborhood lies in the explicit closed slab, the
closed-slab homeomorphism restricts to an ordinary open local chart. The one
geometric input is exactly `W ⊆ range (pairedClosedCollarMap i)`. -/
theorem pairedEdge_open_chart_of_open_in_closedSlab (i : Side)
    (W : Set Surface) (hWopen : IsOpen W)
    (hWsub : W ⊆ Set.range (pairedClosedCollarMap i)) :
    ∃ U : Set SignedCollarRectangle, IsOpen U ∧ Nonempty (U ≃ₜ W) := by
  let e := pairedEdgeClosedSlabChart i
  let U : Set SignedCollarRectangle :=
    e ⁻¹' ((Subtype.val : Set.range (pairedClosedCollarMap i) → Surface) ⁻¹' W)
  have hU : IsOpen U :=
    (hWopen.preimage continuous_subtype_val).preimage e.continuous
  let e₁ : U ≃ₜ
      {q : Set.range (pairedClosedCollarMap i) // (q : Surface) ∈ W} :=
    e.sets rfl
  let e₂ : {q : Set.range (pairedClosedCollarMap i) // (q : Surface) ∈ W} ≃ₜ W :=
    nestedSubtypeHomeomorph hWsub
  exact ⟨U, hU, ⟨e₁.trans e₂⟩⟩

end CurveComplex.Octagon
