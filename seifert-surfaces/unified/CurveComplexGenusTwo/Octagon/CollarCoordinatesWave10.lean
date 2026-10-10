import CurveComplexGenusTwo.Octagon.TopologyLocalChartWave10

namespace CurveComplex.Octagon

noncomputable def collarRotation (i : Side) : ℂ :=
  (Circle.exp (2 * Real.pi * (i.val : ℝ) / 8) : ℂ)

noncomputable def collarAngle (t : ℝ) : ℝ :=
  2 * Real.pi * t / 8

noncomputable def collarUnrotate (i : Side) (x : Disk) : ℂ :=
  (collarRotation i)⁻¹ * (x : ℂ)

private theorem polarSymm_eq (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = (r : ℂ) * (Circle.exp θ : ℂ) := by
  simp [Complex.polarCoord_symm_apply, Circle.coe_exp, Complex.exp_mul_I,
    Complex.ofReal_cos, Complex.ofReal_sin]

theorem collarPoint_unrotate_eq_polarSymm (i : Side) (r : CollarRadius)
    (t : CollarAngle) :
    collarUnrotate i (collarPoint i r t) =
      Complex.polarCoord.symm ((r : ℝ), collarAngle (t : ℝ)) := by
  have hc : collarRotation i ≠ 0 := by simp [collarRotation]
  have heq : (collarPoint i r t : ℂ) =
      collarRotation i *
        Complex.polarCoord.symm ((r : ℝ), collarAngle (t : ℝ)) := by
    rw [polarSymm_eq]
    change ((r : ℝ) : ℂ) *
      (Circle.exp (2 * Real.pi * ((i.val : ℝ) + (t : ℝ)) / 8) : ℂ) =
        (Circle.exp (2 * Real.pi * (i.val : ℝ) / 8) : ℂ) *
          (((r : ℝ) : ℂ) * (Circle.exp (collarAngle (t : ℝ)) : ℂ))
    have ha : 2 * Real.pi * ((i.val : ℝ) + (t : ℝ)) / 8 =
        2 * Real.pi * (i.val : ℝ) / 8 + collarAngle (t : ℝ) := by
      unfold collarAngle
      ring
    rw [ha, Circle.exp_add]
    simp only [Circle.coe_mul]
    ring
  unfold collarUnrotate
  rw [heq]
  simp [hc]

private theorem collarPolarTarget (r : CollarRadius) (t : CollarAngle) :
    ((r : ℝ), collarAngle (t : ℝ)) ∈ Complex.polarCoord.target := by
  rw [Complex.polarCoord_target]
  have ht0 : 0 < collarAngle (t : ℝ) := by
    unfold collarAngle
    nlinarith [mul_pos Real.pi_pos t.property.1]
  have ht1 : collarAngle (t : ℝ) < Real.pi := by
    unfold collarAngle
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr t.property.2), Real.pi_pos]
  exact ⟨by change 0 < (r : ℝ); linarith [r.property.1],
    by change -Real.pi < collarAngle (t : ℝ) ∧ collarAngle (t : ℝ) < Real.pi
       constructor <;> linarith [Real.pi_pos]⟩

theorem collarPoint_polar_recover (i : Side) (r : CollarRadius)
    (t : CollarAngle) :
    Complex.polarCoord (collarUnrotate i (collarPoint i r t)) =
      ((r : ℝ), collarAngle (t : ℝ)) := by
  rw [collarPoint_unrotate_eq_polarSymm]
  exact Complex.polarCoord.right_inv (collarPolarTarget r t)

theorem collarPoint_radius_recover (i : Side) (r : CollarRadius)
    (t : CollarAngle) :
    (Complex.polarCoord (collarUnrotate i (collarPoint i r t))).1 = (r : ℝ) :=
  congrArg Prod.fst (collarPoint_polar_recover i r t)

theorem collarPoint_angle_recover (i : Side) (r : CollarRadius)
    (t : CollarAngle) :
    (Complex.polarCoord (collarUnrotate i (collarPoint i r t))).2 =
      collarAngle (t : ℝ) :=
  congrArg Prod.snd (collarPoint_polar_recover i r t)

private theorem collarPoint_exists_param (i : Side) (x : openCollar i) :
    ∃ p : CollarRadius × CollarAngle, collarPoint i p.1 p.2 = (x : Disk) := by
  exact (Set.ext_iff.mp (openCollar_eq_collarPoint_range i) (x : Disk)).mp
    x.property

noncomputable def collarCoordinates (i : Side) (x : openCollar i) :
    CollarRadius × CollarAngle :=
  Classical.choose (collarPoint_exists_param i x)

theorem collarPoint_coordinates (i : Side) (x : openCollar i) :
    collarPoint i (collarCoordinates i x).1 (collarCoordinates i x).2 = (x : Disk) :=
  Classical.choose_spec (collarPoint_exists_param i x)

theorem collarCoordinates_point (i : Side) (p : CollarRadius × CollarAngle) :
    collarCoordinates i ⟨collarPoint i p.1 p.2,
      collarPoint_mem_openCollar i p.1 p.2⟩ = p := by
  apply collarPoint_injective i
  exact collarPoint_coordinates i ⟨collarPoint i p.1 p.2,
    collarPoint_mem_openCollar i p.1 p.2⟩

theorem collarCoordinates_polar_recover (i : Side) (x : openCollar i) :
    Complex.polarCoord (collarUnrotate i x) =
      (((collarCoordinates i x).1 : ℝ),
        collarAngle ((collarCoordinates i x).2 : ℝ)) := by
  simpa [collarPoint_coordinates i x] using
    (collarPoint_polar_recover i (collarCoordinates i x).1
      (collarCoordinates i x).2)

theorem collarUnrotate_mem_polar_source (i : Side) (x : openCollar i) :
    collarUnrotate i x ∈ Complex.polarCoord.source := by
  rw [← collarPoint_coordinates i x, collarPoint_unrotate_eq_polarSymm]
  exact Complex.polarCoord.map_target
    (collarPolarTarget (collarCoordinates i x).1 (collarCoordinates i x).2)

private theorem collarAngle_inverse (t : ℝ) :
    4 * collarAngle t / Real.pi = t := by
  unfold collarAngle
  field_simp [ne_of_gt Real.pi_pos]
  ring

theorem collarCoordinates_continuous (i : Side) :
    Continuous (collarCoordinates i) := by
  have hrotate : Continuous (fun x : openCollar i => collarUnrotate i x) := by
    unfold collarUnrotate
    fun_prop
  have hpolar : Continuous (fun x : openCollar i =>
      Complex.polarCoord (collarUnrotate i x)) := by
    exact Complex.polarCoord.continuousOn.comp_continuous hrotate
      (collarUnrotate_mem_polar_source i)
  have hr : Continuous (fun x : openCollar i =>
      ((collarCoordinates i x).1 : ℝ)) := by
    have heq : (fun x : openCollar i => ((collarCoordinates i x).1 : ℝ)) =
        (fun x : openCollar i =>
          (Complex.polarCoord (collarUnrotate i x)).1) := by
      funext x
      exact (congrArg Prod.fst (collarCoordinates_polar_recover i x)).symm
    rw [heq]
    exact continuous_fst.comp hpolar
  have ht : Continuous (fun x : openCollar i =>
      ((collarCoordinates i x).2 : ℝ)) := by
    have heq : (fun x : openCollar i => ((collarCoordinates i x).2 : ℝ)) =
        (fun x : openCollar i =>
          4 * (Complex.polarCoord (collarUnrotate i x)).2 / Real.pi) := by
      funext x
      have hθ := congrArg Prod.snd (collarCoordinates_polar_recover i x)
      dsimp at hθ
      calc
        ((collarCoordinates i x).2 : ℝ) =
            4 * collarAngle ((collarCoordinates i x).2 : ℝ) / Real.pi :=
          (collarAngle_inverse _).symm
        _ = 4 * (Complex.polarCoord (collarUnrotate i x)).2 / Real.pi := by
          rw [hθ]
    rw [heq]
    fun_prop
  have hr' : Continuous (fun x : openCollar i => (collarCoordinates i x).1) :=
    Continuous.subtype_mk hr (fun x => (collarCoordinates i x).1.property)
  have ht' : Continuous (fun x : openCollar i => (collarCoordinates i x).2) :=
    Continuous.subtype_mk ht (fun x => (collarCoordinates i x).2.property)
  exact hr'.prodMk ht'

noncomputable def collarPointHomeomorph (i : Side) :
    CollarRadius × CollarAngle ≃ₜ openCollar i where
  toFun p := ⟨collarPoint i p.1 p.2,
    collarPoint_mem_openCollar i p.1 p.2⟩
  invFun := collarCoordinates i
  left_inv := collarCoordinates_point i
  right_inv x := Subtype.ext (collarPoint_coordinates i x)
  continuous_toFun :=
    Continuous.subtype_mk (collarPoint_continuous i)
      (fun p => collarPoint_mem_openCollar i p.1 p.2)
  continuous_invFun := collarCoordinates_continuous i

noncomputable def collarReverseAngle (t : CollarAngle) : CollarAngle :=
  ⟨1 - (t : ℝ), by
    constructor <;> linarith [t.property.1, t.property.2]⟩

theorem collarReverseAngle_toInterval (t : CollarAngle) :
    collarToInterval (collarReverseAngle t) =
      unitInterval.symm (collarToInterval t) := by
  apply Subtype.ext
  rfl

theorem pairedCollar_boundary_quotient (i : Side) (t : CollarAngle) :
    mk (collarPoint i ⟨1, by norm_num⟩ t) =
      mk (collarPoint (pair i) ⟨1, by norm_num⟩
        (collarReverseAngle t)) := by
  rw [collarPoint_boundary, collarPoint_boundary,
    collarReverseAngle_toInterval]
  exact side_pairing i (collarToInterval t)

theorem collarPoint_interior_quotient_unique (i : Side)
    (p q : CollarRadius × CollarAngle) (hp : (p.1 : ℝ) < 1)
    (h : mk (collarPoint i p.1 p.2) = mk (collarPoint i q.1 q.2)) :
    p = q := by
  have hinner : collarPoint i p.1 p.2 ∈ diskInterior :=
    (collarPoint_interior_iff i p.1 p.2).2 hp
  have heq : collarPoint i p.1 p.2 = collarPoint i q.1 q.2 :=
    mem_diskInterior_of_mk_eq_mk hinner h
  exact collarPoint_injective i heq

private theorem collarToInterval_ne_zero' (t : CollarAngle) :
    collarToInterval t ≠ 0 := by
  intro h
  have ht := congrArg (fun x : unitInterval => (x : ℝ)) h
  change (t : ℝ) = 0 at ht
  exact (ne_of_gt t.property.1) ht

private theorem collarToInterval_ne_one' (t : CollarAngle) :
    collarToInterval t ≠ 1 := by
  intro h
  have ht := congrArg (fun x : unitInterval => (x : ℝ)) h
  change (t : ℝ) = 1 at ht
  exact (ne_of_lt t.property.2) ht

theorem collarPoint_boundary_quotient_unique (i : Side)
    (t u : CollarAngle)
    (h : mk (collarPoint i ⟨1, by norm_num⟩ t) =
      mk (collarPoint i ⟨1, by norm_num⟩ u)) : t = u := by
  have hside : mk (side i (collarToInterval t)) =
      mk (side i (collarToInterval u)) := by
    simpa [collarPoint_boundary] using h
  have hf := edge_interior_fiber_eq_pair i (collarToInterval t)
    (collarToInterval_ne_zero' t) (collarToInterval_ne_one' t)
  have hmem : side i (collarToInterval u) ∈
      mk ⁻¹' ({mk (side i (collarToInterval t))} : Set Surface) := hside.symm
  rw [hf] at hmem
  rcases Set.mem_insert_iff.mp hmem with hsame | hpair
  · have htu := side_injective i hsame
    exact Subtype.ext (congrArg (fun z : unitInterval => (z : ℝ)) htu).symm
  · have heq : side i (collarToInterval u) =
        side (pair i) (unitInterval.symm (collarToInterval t)) := by
      simpa using hpair
    rcases side_eq_same_or_endpoints i (pair i) _ _ heq with hbad | hend
    · exact False.elim (pair_fixed_point_free i hbad.1.symm)
    · rcases hend.1 with h0 | h1
      · exact False.elim (collarToInterval_ne_zero' u h0)
      · exact False.elim (collarToInterval_ne_one' u h1)

end CurveComplex.Octagon
