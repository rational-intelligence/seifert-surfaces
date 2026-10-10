import CurveComplexGenusTwo.Octagon.EdgeGlueRectangle
import CurveComplexGenusTwo.Octagon.CollarCoordinatesWave10

namespace CurveComplex.Octagon

abbrev UniversalPairedCollars :=
  Sum (CollarRadius × CollarAngle) (CollarRadius × CollarAngle)

noncomputable def universalCollarMap (i : Side) : UniversalPairedCollars → Surface
  | Sum.inl p => mk (collarPoint i p.1 p.2)
  | Sum.inr p => mk (collarPoint (pair i) p.1 (collarReverseAngle p.2))

private theorem collarAngle_ne_zero (t : CollarAngle) :
    collarToInterval t ≠ 0 := by
  intro h
  have hh := congrArg (fun z : unitInterval => (z : ℝ)) h
  change (t : ℝ) = 0 at hh
  linarith [t.property.1]

private theorem collarAngle_ne_one (t : CollarAngle) :
    collarToInterval t ≠ 1 := by
  intro h
  have hh := congrArg (fun z : unitInterval => (z : ℝ)) h
  change (t : ℝ) = 1 at hh
  linarith [t.property.2]

private theorem collarPoint_same_radius_side_eq_general (i j : Side)
    (r : CollarRadius) (t u : CollarAngle)
    (h : collarPoint i r t = collarPoint j r u) :
    side i (collarToInterval t) = side j (collarToInterval u) := by
  have hh := congrArg (fun z : Disk => (z : ℂ)) h
  change ((r : ℝ) : ℂ) *
      (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (t : ℝ)) / 8) : ℂ) =
    ((r : ℝ) : ℂ) *
      (Circle.exp (2 * Real.pi * ((j.val : ℝ) + (u : ℝ)) / 8) : ℂ) at hh
  have hr : ((r : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) r.2.1)
  have he := mul_left_cancel₀ hr hh
  apply Subtype.ext
  simpa [side, collarToInterval] using he

private theorem side_pair_ne_side_general (i : Side) (t u : CollarAngle) :
    side (pair i) (collarToInterval u) ≠ side i (collarToInterval t) := by
  intro h
  rcases side_eq_same_or_endpoints (pair i) i _ _ h with hsame | hend
  · exact pair_fixed_point_free i hsame.1
  · rcases hend.2 with h | h
    · exact collarAngle_ne_zero t h
    · exact collarAngle_ne_one t h

private theorem universal_left_injective (i : Side) :
    Function.Injective (fun p : CollarRadius × CollarAngle =>
      universalCollarMap i (Sum.inl p)) := by
  rintro ⟨r, t⟩ ⟨s, u⟩ h
  have hrel : Relation.r (collarPoint i r t) (collarPoint i s u) :=
    Quotient.exact h
  have hrs : r = s := Subtype.ext (by
    simpa [collarPoint_norm] using norm_eq_of_related hrel)
  subst s
  by_cases hr1 : r = (⟨1, by norm_num⟩ : CollarRadius)
  · subst r
    have htu := collarPoint_boundary_quotient_unique i t u h
    exact Prod.ext rfl htu
  · have hrlt : (r : ℝ) < 1 := lt_of_le_of_ne r.2.2 (by
      intro hv
      exact hr1 (Subtype.ext hv))
    exact collarPoint_interior_quotient_unique i (r,t) (r,u) hrlt h

private theorem universal_right_injective (i : Side) :
    Function.Injective (fun p : CollarRadius × CollarAngle =>
      universalCollarMap i (Sum.inr p)) := by
  rintro ⟨r,t⟩ ⟨s,u⟩ h
  have hh : (r, collarReverseAngle t) =
      (s, collarReverseAngle u) :=
    universal_left_injective (pair i) (by
      simpa [universalCollarMap] using h)
  have ht : t = u := by
    apply Subtype.ext
    have heq := congrArg (fun z : CollarAngle => (z : ℝ))
      (congrArg Prod.snd hh)
    dsimp [collarReverseAngle] at heq
    linarith
  have hr : r = s := congrArg (fun p : CollarRadius × CollarAngle => p.1) hh
  exact Prod.ext hr ht

private theorem universal_cross_eq_iff (i : Side)
    (r s : CollarRadius) (t u : CollarAngle) :
    universalCollarMap i (Sum.inl (r,t)) =
        universalCollarMap i (Sum.inr (s,u)) ↔
      r = ⟨1, by norm_num⟩ ∧ s = ⟨1, by norm_num⟩ ∧ t = u := by
  constructor
  · intro h
    have hrel : Relation.r (collarPoint i r t)
        (collarPoint (pair i) s (collarReverseAngle u)) :=
      Quotient.exact h
    have hrs : r = s := Subtype.ext (by
      simpa [collarPoint_norm] using norm_eq_of_related hrel)
    subst s
    have hr1 : r = (⟨1, by norm_num⟩ : CollarRadius) := by
      by_contra hrne
      have hrlt : (r : ℝ) < 1 := lt_of_le_of_ne r.2.2 (by
        intro hv
        exact hrne (Subtype.ext hv))
      have hinner : collarPoint i r t ∈ diskInterior :=
        (collarPoint_interior_iff i r t).2 hrlt
      have heq : collarPoint i r t =
          collarPoint (pair i) r (collarReverseAngle u) :=
        mem_diskInterior_of_mk_eq_mk hinner h
      have hside := collarPoint_same_radius_side_eq_general i (pair i)
        r t (collarReverseAngle u) heq
      exact side_pair_ne_side_general i t (collarReverseAngle u) hside.symm
    subst r
    have htu : t = u := by
      have h' : mk (collarPoint i (⟨1, by norm_num⟩ : CollarRadius) t) =
          mk (collarPoint i (⟨1, by norm_num⟩ : CollarRadius) u) :=
        h.trans (pairedCollar_boundary_quotient i u).symm
      exact collarPoint_boundary_quotient_unique i t u h'
    exact ⟨rfl, rfl, htu⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact pairedCollar_boundary_quotient i t

def UniversalSeam (a b : UniversalPairedCollars) : Prop :=
  a = b ∨ ∃ t : CollarAngle,
    (a = Sum.inl (⟨1, by norm_num⟩, t) ∧
      b = Sum.inr (⟨1, by norm_num⟩, t)) ∨
    (a = Sum.inr (⟨1, by norm_num⟩, t) ∧
      b = Sum.inl (⟨1, by norm_num⟩, t))

theorem universalCollarMap_kernel_iff (i : Side)
    (a b : UniversalPairedCollars) :
    universalCollarMap i a = universalCollarMap i b ↔
      UniversalSeam a b := by
  constructor
  · intro h
    rcases a with ⟨p⟩ | ⟨p⟩ <;> rcases b with ⟨q⟩ | ⟨q⟩
    · exact Or.inl (congrArg Sum.inl (universal_left_injective i h))
    · rcases p with ⟨r,t⟩
      rcases q with ⟨s,u⟩
      obtain ⟨rfl,rfl,rfl⟩ := (universal_cross_eq_iff i r s t u).mp h
      exact Or.inr ⟨t, Or.inl ⟨rfl,rfl⟩⟩
    · rcases p with ⟨r,t⟩
      rcases q with ⟨s,u⟩
      obtain ⟨rfl,rfl,rfl⟩ := (universal_cross_eq_iff i s r u t).mp h.symm
      exact Or.inr ⟨u, Or.inr ⟨rfl,rfl⟩⟩
    · exact Or.inl (congrArg Sum.inr (universal_right_injective i h))
  · intro h
    rcases h with rfl | ⟨t, h | h⟩
    · rfl
    · rcases h with ⟨rfl,rfl⟩
      exact pairedCollar_boundary_quotient i t
    · rcases h with ⟨rfl,rfl⟩
      exact (pairedCollar_boundary_quotient i t).symm

end CurveComplex.Octagon
