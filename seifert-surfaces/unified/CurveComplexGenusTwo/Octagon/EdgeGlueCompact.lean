import CurveComplexGenusTwo.Octagon.OctagonChartGlueWave10

namespace CurveComplex.Octagon

/-! A compact two-sided collar around a paired edge.  Quotienting this
concrete collar by exactly the kernel of its map to the octagon surface yields
a space homeomorphic to its image in the actual surface. -/

abbrev ClosedCollarRadius := Set.Icc (3 / 4 : ℝ) 1
abbrev ClosedCollarAngle := Set.Icc (1 / 4 : ℝ) (3 / 4)
abbrev PairedClosedCollars :=
  Sum (ClosedCollarRadius × ClosedCollarAngle)
    (ClosedCollarRadius × ClosedCollarAngle)

private noncomputable def radiusToCollar (r : ClosedCollarRadius) : CollarRadius :=
  ⟨r.1, by
    constructor
    · have h := r.2.1
      linarith
    · exact r.2.2⟩

private noncomputable def angleToCollar (t : ClosedCollarAngle) : CollarAngle :=
  ⟨t.1, by
    constructor <;> have h₁ := t.2.1 <;> have h₂ := t.2.2 <;> linarith⟩

private noncomputable def reverseClosedAngle (t : ClosedCollarAngle) : CollarAngle :=
  ⟨1 - t.1, by
    constructor <;> have h₁ := t.2.1 <;> have h₂ := t.2.2 <;> linarith⟩

private theorem continuous_radiusToCollar : Continuous radiusToCollar := by
  exact Continuous.subtype_mk continuous_subtype_val _

private theorem continuous_angleToCollar : Continuous angleToCollar := by
  exact Continuous.subtype_mk continuous_subtype_val _

private theorem continuous_reverseClosedAngle : Continuous reverseClosedAngle := by
  exact Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _

noncomputable def pairedClosedCollarMap (i : Side) : PairedClosedCollars → Surface
  | Sum.inl p => mk (collarPoint i (radiusToCollar p.1) (angleToCollar p.2))
  | Sum.inr p => mk (collarPoint (pair i) (radiusToCollar p.1)
      (reverseClosedAngle p.2))

theorem continuous_pairedClosedCollarMap (i : Side) :
    Continuous (pairedClosedCollarMap i) := by
  apply continuous_sum_dom.mpr
  constructor
  · have hp : Continuous (fun p : ClosedCollarRadius × ClosedCollarAngle =>
        (radiusToCollar p.1, angleToCollar p.2)) :=
      (continuous_radiusToCollar.comp continuous_fst).prodMk
        (continuous_angleToCollar.comp continuous_snd)
    exact continuous_mk.comp ((collarPoint_continuous i).comp hp)
  · have hp : Continuous (fun p : ClosedCollarRadius × ClosedCollarAngle =>
        (radiusToCollar p.1, reverseClosedAngle p.2)) :=
      (continuous_radiusToCollar.comp continuous_fst).prodMk
        (continuous_reverseClosedAngle.comp continuous_snd)
    exact continuous_mk.comp ((collarPoint_continuous (pair i)).comp hp)

theorem pairedClosedCollar_seam (i : Side) (t : ClosedCollarAngle) :
    pairedClosedCollarMap i (Sum.inl (⟨1, by norm_num⟩, t)) =
      pairedClosedCollarMap i (Sum.inr (⟨1, by norm_num⟩, t)) := by
  change mk (collarPoint i (radiusToCollar ⟨1, by norm_num⟩)
      (angleToCollar t)) =
    mk (collarPoint (pair i) (radiusToCollar ⟨1, by norm_num⟩)
      (reverseClosedAngle t))
  rw [show radiusToCollar (⟨1, by norm_num⟩ : ClosedCollarRadius) =
    (⟨1, by norm_num⟩ : CollarRadius) by rfl]
  rw [collarPoint_boundary, collarPoint_boundary]
  have h : collarToInterval (reverseClosedAngle t) =
      unitInterval.symm (collarToInterval (angleToCollar t)) := by
    apply Subtype.ext
    rfl
  rw [h]
  exact side_pairing i _

private theorem angleToCollar_ne_zero (t : ClosedCollarAngle) :
    collarToInterval (angleToCollar t) ≠ 0 := by
  intro h
  have ht : (t : ℝ) = 0 := congrArg Subtype.val h
  have hlow := t.2.1
  linarith

private theorem angleToCollar_ne_one (t : ClosedCollarAngle) :
    collarToInterval (angleToCollar t) ≠ 1 := by
  intro h
  have ht : (t : ℝ) = 1 := congrArg Subtype.val h
  have hhigh := t.2.2
  linarith

private theorem side_pair_ne_side (i : Side) (t : ClosedCollarAngle)
    (u : unitInterval) :
    side (pair i) u ≠ side i (collarToInterval (angleToCollar t)) := by
  intro h
  rcases side_eq_same_or_endpoints (pair i) i u
      (collarToInterval (angleToCollar t)) h with hsame | hend
  · exact pair_fixed_point_free i hsame.1
  · rcases hend.2 with h | h
    · exact angleToCollar_ne_zero t h
    · exact angleToCollar_ne_one t h

theorem pairedClosedCollar_boundary_injective (i : Side)
    (t u : ClosedCollarAngle)
    (h : pairedClosedCollarMap i (Sum.inl (⟨1, by norm_num⟩, t)) =
      pairedClosedCollarMap i (Sum.inr (⟨1, by norm_num⟩, u))) :
    t = u := by
  change mk (collarPoint i (radiusToCollar ⟨1, by norm_num⟩)
      (angleToCollar t)) =
    mk (collarPoint (pair i) (radiusToCollar ⟨1, by norm_num⟩)
      (reverseClosedAngle u)) at h
  rw [show radiusToCollar (⟨1, by norm_num⟩ : ClosedCollarRadius) =
    (⟨1, by norm_num⟩ : CollarRadius) by rfl] at h
  rw [collarPoint_boundary, collarPoint_boundary] at h
  have hrev : collarToInterval (reverseClosedAngle u) =
      unitInterval.symm (collarToInterval (angleToCollar u)) := by
    apply Subtype.ext
    rfl
  rw [hrev] at h
  have hf := edge_interior_fiber_eq_pair i (collarToInterval (angleToCollar t))
    (angleToCollar_ne_zero t) (angleToCollar_ne_one t)
  have hmem : side (pair i)
      (unitInterval.symm (collarToInterval (angleToCollar u))) ∈
      mk ⁻¹' ({mk (side i (collarToInterval (angleToCollar t)))} : Set Surface) := h.symm
  rw [hf] at hmem
  rcases Set.mem_insert_iff.mp hmem with hbad | hgood
  · exact False.elim (side_pair_ne_side i t _ hbad)
  · have heq : unitInterval.symm (collarToInterval (angleToCollar u)) =
        unitInterval.symm (collarToInterval (angleToCollar t)) := by
      apply side_injective (pair i)
      simpa using hgood
    have htu : collarToInterval (angleToCollar u) =
        collarToInterval (angleToCollar t) := by
      have h := congrArg unitInterval.symm heq
      simpa using h
    apply Subtype.ext
    have hh := congrArg (fun z : unitInterval => (z : ℝ)) htu
    exact hh.symm

private theorem collarPoint_same_radius_side_eq (i j : Side)
    (r : CollarRadius) (t u : CollarAngle)
    (h : collarPoint i r t = collarPoint j r u) :
    side i (collarToInterval t) = side j (collarToInterval u) := by
  have hh := congrArg (fun z : Disk => (z : ℂ)) h
  change ((r : ℝ) : ℂ) *
      (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (t : ℝ)) / 8) : ℂ) =
    ((r : ℝ) : ℂ) *
      (Circle.exp (2 * Real.pi * ((j.val : ℝ) + (u : ℝ)) / 8) : ℂ) at hh
  have hr : ((r : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) r.2.1)
  have he := mul_left_cancel₀ hr hh
  apply Subtype.ext
  simpa [side, collarToInterval] using he

theorem pairedClosedCollar_cross_eq_iff (i : Side)
    (r s : ClosedCollarRadius) (t u : ClosedCollarAngle) :
    pairedClosedCollarMap i (Sum.inl (r, t)) =
        pairedClosedCollarMap i (Sum.inr (s, u)) ↔
      r = ⟨1, by norm_num⟩ ∧ s = ⟨1, by norm_num⟩ ∧ t = u := by
  constructor
  · intro h
    have hrel : Relation.r
        (collarPoint i (radiusToCollar r) (angleToCollar t))
        (collarPoint (pair i) (radiusToCollar s) (reverseClosedAngle u)) :=
      Quotient.exact h
    have hnorm := norm_eq_of_related hrel
    have hrs : r = s := by
      apply Subtype.ext
      simpa [collarPoint_norm, radiusToCollar] using hnorm
    subst s
    have hr1 : r = (⟨1, by norm_num⟩ : ClosedCollarRadius) := by
      by_contra hrne
      have hrlt : (r : ℝ) < 1 := lt_of_le_of_ne r.2.2 (by
        intro hval
        exact hrne (Subtype.ext hval))
      have hinner : collarPoint i (radiusToCollar r) (angleToCollar t) ∈
          diskInterior :=
        (collarPoint_interior_iff i (radiusToCollar r) (angleToCollar t)).2 hrlt
      have heq : collarPoint i (radiusToCollar r) (angleToCollar t) =
          collarPoint (pair i) (radiusToCollar r) (reverseClosedAngle u) :=
        mem_diskInterior_of_mk_eq_mk hinner h
      have hside := collarPoint_same_radius_side_eq i (pair i)
        (radiusToCollar r) (angleToCollar t) (reverseClosedAngle u) heq
      exact side_pair_ne_side i t _ hside.symm
    have hs1 : r = (⟨1, by norm_num⟩ : ClosedCollarRadius) := hr1
    have htu : t = u := by
      subst r
      exact pairedClosedCollar_boundary_injective i t u h
    exact ⟨hr1, hs1, htu⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact pairedClosedCollar_seam i t

private theorem same_side_closedCollar_injective (i : Side)
    (r s : ClosedCollarRadius) (t u : ClosedCollarAngle)
    (h : mk (collarPoint i (radiusToCollar r) (angleToCollar t)) =
      mk (collarPoint i (radiusToCollar s) (angleToCollar u))) :
    r = s ∧ t = u := by
  have hrel : Relation.r
      (collarPoint i (radiusToCollar r) (angleToCollar t))
      (collarPoint i (radiusToCollar s) (angleToCollar u)) :=
    Quotient.exact h
  have hnorm := norm_eq_of_related hrel
  have hrs : r = s := by
    apply Subtype.ext
    simpa [collarPoint_norm, radiusToCollar] using hnorm
  subst s
  have htu : t = u := by
    by_cases hr1 : r = (⟨1, by norm_num⟩ : ClosedCollarRadius)
    · subst r
      have hb : mk (side i (collarToInterval (angleToCollar t))) =
          mk (side i (collarToInterval (angleToCollar u))) := by
        simpa [collarPoint_boundary, radiusToCollar] using h
      have hf := edge_interior_fiber_eq_pair i
        (collarToInterval (angleToCollar t))
        (angleToCollar_ne_zero t) (angleToCollar_ne_one t)
      have hmem : side i (collarToInterval (angleToCollar u)) ∈
          mk ⁻¹' ({mk (side i (collarToInterval (angleToCollar t)))} : Set Surface) := hb.symm
      rw [hf] at hmem
      rcases Set.mem_insert_iff.mp hmem with hsame | hbad
      · have heq := side_injective i hsame
        apply Subtype.ext
        have hh := congrArg (fun z : unitInterval => (z : ℝ)) heq
        exact hh.symm
      · have heq : side i (collarToInterval (angleToCollar u)) =
            side (pair i)
              (unitInterval.symm (collarToInterval (angleToCollar t))) := by
          simpa using hbad
        exact False.elim (side_pair_ne_side i u _ heq.symm)
    · have hrlt : (r : ℝ) < 1 := lt_of_le_of_ne r.2.2 (by
        intro hval
        exact hr1 (Subtype.ext hval))
      have hinner : collarPoint i (radiusToCollar r) (angleToCollar t) ∈
          diskInterior :=
        (collarPoint_interior_iff i (radiusToCollar r) (angleToCollar t)).2 hrlt
      have heq : collarPoint i (radiusToCollar r) (angleToCollar t) =
          collarPoint i (radiusToCollar r) (angleToCollar u) :=
        mem_diskInterior_of_mk_eq_mk hinner h
      have hinj : (radiusToCollar r, angleToCollar t) =
          (radiusToCollar r, angleToCollar u) :=
        collarPoint_injective i heq
      have ht : angleToCollar t = angleToCollar u := congrArg Prod.snd hinj
      apply Subtype.ext
      have hh := congrArg (fun z : CollarAngle => (z : ℝ)) ht
      exact hh
  exact ⟨rfl, htu⟩

theorem pairedClosedCollar_left_injective (i : Side) :
    Function.Injective (fun p : ClosedCollarRadius × ClosedCollarAngle =>
      pairedClosedCollarMap i (Sum.inl p)) := by
  rintro ⟨r, t⟩ ⟨s, u⟩ h
  obtain ⟨hrs, htu⟩ := same_side_closedCollar_injective i r s t u h
  exact Prod.ext hrs htu

theorem pairedClosedCollar_right_injective (i : Side) :
    Function.Injective (fun p : ClosedCollarRadius × ClosedCollarAngle =>
      pairedClosedCollarMap i (Sum.inr p)) := by
  rintro ⟨r, t⟩ ⟨s, u⟩ h
  have hh := same_side_closedCollar_injective (pair i) r s
    (⟨1 - t.1, by constructor <;> have h₁ := t.2.1 <;> have h₂ := t.2.2 <;> linarith⟩ : ClosedCollarAngle)
    (⟨1 - u.1, by constructor <;> have h₁ := u.2.1 <;> have h₂ := u.2.2 <;> linarith⟩ : ClosedCollarAngle) h
  obtain ⟨hrs, htu⟩ := hh
  have htu' : t = u := by
    apply Subtype.ext
    have heq := congrArg (fun z : ClosedCollarAngle => (z : ℝ)) htu
    dsimp at heq
    linarith
  exact Prod.ext hrs htu'

/-- Literal two-rectangle seam relation: points are equal, or the two outer
boundary copies at the same angle parameter are identified. -/
def PairedSeam (a b : PairedClosedCollars) : Prop :=
  a = b ∨ ∃ t : ClosedCollarAngle,
    (a = Sum.inl (⟨1, by norm_num⟩, t) ∧
      b = Sum.inr (⟨1, by norm_num⟩, t)) ∨
    (a = Sum.inr (⟨1, by norm_num⟩, t) ∧
      b = Sum.inl (⟨1, by norm_num⟩, t))

theorem pairedClosedCollar_kernel_iff (i : Side) (a b : PairedClosedCollars) :
    pairedClosedCollarMap i a = pairedClosedCollarMap i b ↔ PairedSeam a b := by
  constructor
  · intro h
    rcases a with ⟨p⟩ | ⟨p⟩ <;> rcases b with ⟨q⟩ | ⟨q⟩
    · exact Or.inl (congrArg Sum.inl (pairedClosedCollar_left_injective i h))
    · rcases p with ⟨r, t⟩
      rcases q with ⟨s, u⟩
      obtain ⟨rfl, rfl, rfl⟩ := (pairedClosedCollar_cross_eq_iff i r s t u).mp h
      exact Or.inr ⟨t, Or.inl ⟨rfl, rfl⟩⟩
    · rcases p with ⟨r, t⟩
      rcases q with ⟨s, u⟩
      obtain ⟨rfl, rfl, rfl⟩ :=
        (pairedClosedCollar_cross_eq_iff i s r u t).mp h.symm
      exact Or.inr ⟨u, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inl (congrArg Sum.inr (pairedClosedCollar_right_injective i h))
  · intro h
    rcases h with rfl | ⟨t, h | h⟩
    · rfl
    · rcases h with ⟨rfl, rfl⟩
      exact pairedClosedCollar_seam i t
    · rcases h with ⟨rfl, rfl⟩
      exact (pairedClosedCollar_seam i t).symm

noncomputable def pairedSeamSetoid (i : Side) : Setoid PairedClosedCollars :=
  Setoid.ker (pairedClosedCollarMap i)

theorem pairedSeamSetoid_iff (i : Side) (a b : PairedClosedCollars) :
    (pairedSeamSetoid i).r a b ↔ PairedSeam a b :=
  pairedClosedCollar_kernel_iff i a b

private instance : CompactSpace ClosedCollarRadius :=
  by infer_instance

private instance : CompactSpace ClosedCollarAngle :=
  by infer_instance

private instance : T2Space Surface := quotient_t2

theorem pairedClosedCollar_isStrictMap (i : Side) :
    Topology.IsStrictMap (pairedClosedCollarMap i) := by
  have hclosed : IsClosedMap (pairedClosedCollarMap i) := by
    intro s hs
    exact (hs.isCompact.image (continuous_pairedClosedCollarMap i)).isClosed
  exact hclosed.isStrictMap (continuous_pairedClosedCollarMap i)

noncomputable def pairedClosedCollar_quotientHomeomorph (i : Side) :
    Quotient (pairedSeamSetoid i) ≃ₜ
      Set.range (pairedClosedCollarMap i) :=
  Homeomorph.quotientKerEquivRange (pairedClosedCollar_isStrictMap i)

end CurveComplex.Octagon
