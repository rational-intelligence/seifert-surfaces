import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSurvivingEventLocality

open Set Topology Schoenflies CurveComplex

theorem actual_supported_full_grid_erase_has_exact_single_fiber_erase
    (G : C(ℝ,Plane)) (T a b c r s : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (phi : Plane ≃ₜ Plane)
    (hcontact : (phi '' Plane.closedSquare 0 1)∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=G '' Icc a b)
    (hold : (G '' Icc a b)∩{z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}={G r,G s})
    (H : AmbientIsotopy Plane)
    (hfix : ∀ t z, z∉⋃ i : ℤ×ℤ,
      (fun w : Plane => w+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (phi '' Plane.openSquare 0 1) →
      H.map (t,z)=z)
    (herase : {t : ℝ | ∃ i : ℤ, H.finalMap (G t) 0=c+(i:ℝ)*T}=
      {t : ℝ | ∃ i : ℤ, G t 0=c+(i:ℝ)*T}\G ⁻¹'
        (⋃ i : ℤ×ℤ, ({G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
          G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)))
 :
    {t : ℝ | H.finalMap (G t) 0=c}=
      {t : ℝ | G t 0=c}\G ⁻¹'
        (⋃ i : ℤ×ℤ, ({G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
          G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)) := by
  have hFixed (x : ℝ) (hx : ∃ i : ℤ, H.finalMap (G x) 0=c+(i:ℝ)*T) : H.finalMap (G x)=G x := by
    have hSource : x∈{t : ℝ | ∃ i : ℤ, G t 0=c+(i:ℝ)*T}\G ⁻¹'
        (⋃ i : ℤ×ℤ, ({G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
          G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)) := herase ▸ hx
    have hGL : G x∈⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)) := by
      refine mem_iUnion.mpr ⟨0,x,?_⟩
      ext k; fin_cases k <;> simp [Plane.mk]
    obtain ⟨N,_,hxN,hNfix⟩ := normalized_actual_surviving_crossing_has_fixed_open_neighborhood
      G T a b c r s hT hp phi hcontact hold H hfix (G x) hGL hSource.1 hSource.2
    exact hNfix ⟨1,by norm_num⟩ (G x) hxN
  ext x
  constructor
  · intro hx
    have hxGrid : ∃ i : ℤ, H.finalMap (G x) 0=c+(i:ℝ)*T := ⟨0,by simpa using hx⟩
    have hxOld : x∈{t : ℝ | ∃ i : ℤ, G t 0=c+(i:ℝ)*T}\G ⁻¹'
        (⋃ i : ℤ×ℤ, ({G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
          G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)) := herase ▸ hxGrid
    refine ⟨?_,hxOld.2⟩
    change G x 0=c
    change H.finalMap (G x) 0=c at hx
    rwa [hFixed x hxGrid] at hx
  · rintro ⟨hx,hxOrbit⟩
    have hxGrid : ∃ i : ℤ, H.finalMap (G x) 0=c+(i:ℝ)*T := by
      change x∈{t : ℝ | ∃ i : ℤ, H.finalMap (G t) 0=c+(i:ℝ)*T}
      rw [herase]
      exact ⟨⟨0,by simpa using hx⟩,hxOrbit⟩
    change H.finalMap (G x) 0=c
    rw [hFixed x hxGrid]
    exact hx

#print axioms actual_supported_full_grid_erase_has_exact_single_fiber_erase
