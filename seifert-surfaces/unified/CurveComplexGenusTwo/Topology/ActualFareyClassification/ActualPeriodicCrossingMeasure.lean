import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualGridOrbitInteraction

open Set Schoenflies

/-- The full-grid crossing count uses the same quotient measure for every
actual fundamental interval. No finite-count independence certificate is input. -/
theorem actual_periodic_grid_crossing_count_independent_of_origin
    (F : ℝ→Plane) (T c a b : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), F (x+(k:ℝ)*T)=F x+Plane.mk ((k:ℝ)*T) 0) :
    {t : Ico a (a+T) | ∃ i : ℤ, F t.val 0=c+(i:ℝ)*T}.ncard =
      {t : Ico b (b+T) | ∃ i : ℤ, F t.val 0=c+(i:ℝ)*T}.ncard := by
  let e : Ico a (a+T) ≃ Ico b (b+T) :=
    (QuotientAddGroup.equivIcoMod hT a).symm.trans (QuotientAddGroup.equivIcoMod hT b)
  have he (t : Ico a (a+T)) : (e t).val=toIcoMod hT b t.val := rfl
  have hgrid (x : ℝ) :
      (∃ i : ℤ, F (toIcoMod hT b x) 0=c+(i:ℝ)*T) ↔
        ∃ i : ℤ, F x 0=c+(i:ℝ)*T := by
    let k := toIcoDiv hT b x
    have hx : x=toIcoMod hT b x+(k:ℝ)*T := by
      have hh := toIcoMod_add_toIcoDiv_mul hT b x
      exact hh.symm
    have hFx : F x=F (toIcoMod hT b x)+Plane.mk ((k:ℝ)*T) 0 := by
      calc F x=F (toIcoMod hT b x+(k:ℝ)*T) := congrArg F hx
        _=F (toIcoMod hT b x)+Plane.mk ((k:ℝ)*T) 0 := hp k _
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨i+k,?_⟩
      rw [hFx]
      change F (toIcoMod hT b x) 0+(k:ℝ)*T=c+((i+k:ℤ):ℝ)*T
      push_cast
      linarith
    · rintro ⟨i,hi⟩
      refine ⟨i-k,?_⟩
      rw [hFx] at hi
      change F (toIcoMod hT b x) 0+(k:ℝ)*T=c+(i:ℝ)*T at hi
      push_cast
      linarith
  have hImage : e '' {t : Ico a (a+T) | ∃ i : ℤ, F t.val 0=c+(i:ℝ)*T}=
      {t : Ico b (b+T) | ∃ i : ℤ, F t.val 0=c+(i:ℝ)*T} := by
    ext t
    constructor
    · rintro ⟨u,hu,rfl⟩
      change ∃ i : ℤ, F (e u).val 0=c+(i:ℝ)*T
      rw [he]
      exact (hgrid u.val).mpr hu
    · intro ht
      refine ⟨e.symm t,?_,e.apply_symm_apply _⟩
      apply (hgrid (e.symm t).val).mp
      rw [←he,e.apply_symm_apply]
      exact ht
  rw [←hImage,ncard_image_of_injective _ e.injective]

#print axioms actual_periodic_grid_crossing_count_independent_of_origin
