import CurveComplexGenusTwo.Topology.ActualFareyClassification.PeriodicEventErasePort

open Set Schoenflies CurveComplex

/-- Exact deletion of the FULL lattice orbit gives strict reduction of a
finite representative crossing set. No two-parameter deletion is substituted
for that orbit, and no strict cardinal inequality is an input. -/
theorem finite_crossing_count_strict_after_full_lattice_orbit_erase
    {α : Type*} (γ γ' : α → Plane) (L : Set Plane) (T : ℝ) (x y : Plane)
    (hfinite : {s | γ s∈L}.Finite)
    (herase : {s | γ' s∈L} = {s | γ s∈L} \ γ ⁻¹'
      (⋃ i : ℤ × ℤ, ({x+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
        y+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)))
    (s : α) (hs : γ s∈L)
    (hsOrbit : γ s∈⋃ i : ℤ × ℤ,
      ({x+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
        y+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)) :
    {s | γ' s∈L}.Finite ∧ {s | γ' s∈L}.ncard < {s | γ s∈L}.ncard := by
  rw [herase]
  refine ⟨hfinite.subset sdiff_subset, ncard_lt_ncard ?_ hfinite⟩
  apply ssubset_iff_subset_ne.mpr
  refine ⟨sdiff_subset,?_⟩
  intro he
  have hs' : s∈{s | γ s∈L} \ γ ⁻¹'
      (⋃ i : ℤ × ℤ, ({x+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
        y+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)) := by
    rw [he]
    exact hs
  exact hs'.2 hsOrbit

/-- Since the full orbit includes its untranslated corner, a selected actual
crossing suffices as the witness for strict quotient-count reduction. -/
theorem finite_crossing_count_strict_when_selected_corner_erased
    {α : Type*} (γ γ' : α → Plane) (L : Set Plane) (T : ℝ) (x y : Plane)
    (hfinite : {s | γ s∈L}.Finite)
    (herase : {s | γ' s∈L} = {s | γ s∈L} \ γ ⁻¹'
      (⋃ i : ℤ × ℤ, ({x+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
        y+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)))
    (s : α) (hs : γ s=x) (hxL : x∈L) :
    {s | γ' s∈L}.Finite ∧ {s | γ' s∈L}.ncard < {s | γ s∈L}.ncard := by
  apply finite_crossing_count_strict_after_full_lattice_orbit_erase γ γ' L T x y
    hfinite herase s (hs ▸ hxL)
  rw [hs]
  apply mem_iUnion.mpr
  refine ⟨(0,0),Or.inl ?_⟩
  ext i
  fin_cases i <;> simp [Plane.mk]

#print axioms finite_crossing_count_strict_after_full_lattice_orbit_erase
#print axioms finite_crossing_count_strict_when_selected_corner_erased

/-- Supported geometric move receipts produce the exact full-orbit erasure
and strict finite representative-count reduction; neither conclusion is assumed. -/
theorem finite_quotient_crossing_count_after_actual_supported_periodic_move
    {α : Type*} (γ : α → Plane)
    (T : ℝ) (hT : 0 < T) (φ : Plane ≃ₜ Plane)
    (P : AmbientIsotopy Plane) (A B L : Set Plane) (x y : Plane)
    (hlocal : Set.range γ ∩
      (⋃ i : ℤ × ℤ, (fun z : Plane =>
        z + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) ''
          (φ '' Plane.openSquare 0 1)) ⊆
      ⋃ i : ℤ × ℤ, (fun z : Plane =>
        z + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) '' A)
    (hmove : ∀ i : ℤ × ℤ,
      P.finalMap '' ((fun z : Plane =>
        z + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) '' A) =
        (fun z : Plane =>
          z + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) '' B)
    (hfix : ∀ t z, z ∉
      (⋃ i : ℤ × ℤ, (fun w : Plane =>
        w + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) ''
          (φ '' Plane.openSquare 0 1)) → P.map (t, z) = z)
    (havoid : Disjoint
      (⋃ i : ℤ × ℤ, (fun z : Plane =>
        z + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) '' B) L)
    (hold :
      (⋃ i : ℤ × ℤ, (fun z : Plane =>
        z + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) '' A) ∩ L =
      ⋃ i : ℤ × ℤ, ({x + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T),
        y + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)} : Set Plane))
    (hcrossingsSupported :
      (⋃ i : ℤ × ℤ, ({x + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T),
        y + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)} : Set Plane)) ⊆
      ⋃ i : ℤ × ℤ, (fun z : Plane =>
        z + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) ''
          (φ '' Plane.openSquare 0 1))
    (hfinite : {s | γ s ∈ L}.Finite)
    (s : α) (hs : γ s=x) (hxL : x∈L) :
    {s | P.finalMap (γ s) ∈ L}.Finite ∧
      {s | P.finalMap (γ s) ∈ L}.ncard < {s | γ s ∈ L}.ncard ∧
    {s | P.finalMap (γ s) ∈ L} =
      {s | γ s ∈ L} \ γ ⁻¹'
        (⋃ i : ℤ × ℤ, ({x + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T),
          y + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)} : Set Plane)) := by
  have herase := crossing_parameters_of_periodic_supported_crosscut_replacement γ T hT φ P A B L x y
    hlocal hmove hfix havoid hold hcrossingsSupported
  have hcount := finite_crossing_count_strict_when_selected_corner_erased γ
    (fun u => P.finalMap (γ u)) L T x y hfinite herase s hs hxL
  exact ⟨hcount.1,hcount.2,herase⟩

#print axioms finite_quotient_crossing_count_after_actual_supported_periodic_move
