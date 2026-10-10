import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSupportedFamilyTransport

open Set Topology Schoenflies CurveComplex
open scoped NNReal

/-- An actual small periodic displacement field constructs its ambient isotopy.
The inverse/homeomorphism is supplied by the quantitative global inverse theorem. -/
theorem actual_small_periodic_displacement_isotopy
    (f : Plane→Plane) (d : ℝ≥0) (hd : (d : ℝ)<1) (hf : LipschitzWith d f)
    (T : ℝ)
    (hp : ∀ (i : ℤ×ℤ) z,
      f (z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=f z) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t z, H.map (t,z)=z+(t:ℝ) • f z) ∧
      (∀ t (i : ℤ×ℤ) z,
        H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t z, f z=0 → H.map (t,z)=z) := by
  let F : Interval×Plane→Plane := fun q => q.2+(q.1:ℝ) • f q.2
  have hF : Continuous F := continuous_snd.add
    ((continuous_subtype_val.comp continuous_fst).smul (hf.continuous.comp continuous_snd))
  let H : AmbientIsotopy Plane := {
    map := ⟨F,hF⟩
    homeomorphism_at := by
      intro t
      have happ : ApproximatesLinearOn (fun x => F (t,x))
          (ContinuousLinearEquiv.refl ℝ Plane : Plane→L[ℝ] Plane) univ d := by
        intro x _ y _
        have he : F (t,x)-F (t,y)-(x-y)=(t:ℝ) • (f x-f y) := by dsimp [F]; module
        change ‖F (t,x)-F (t,y)-(x-y)‖≤_
        rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg t.property.1]
        calc (t:ℝ)*‖f x-f y‖≤1*‖f x-f y‖ := mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
          _≤d*‖x-y‖ := by simpa [dist_eq_norm] using hf.dist_le_mul x y
      let e := happ.toHomeomorph (fun x => F (t,x)) (Or.inr (by simpa using hd))
      exact ⟨e,fun _ => rfl⟩
    at_zero := by intro z; simp [F] }
  refine ⟨H,fun _ _ => rfl,?_,?_⟩
  · intro t i z
    change z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)+(t:ℝ) • f (z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
      z+(t:ℝ) • f z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
    rw [hp]
    abel
  · intro t z hz
    change z+(t:ℝ) • f z=z
    simp [hz]

#print axioms actual_small_periodic_displacement_isotopy
