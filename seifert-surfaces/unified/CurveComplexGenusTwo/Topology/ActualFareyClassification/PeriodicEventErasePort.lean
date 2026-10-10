import CurveComplexGenusTwo.Topology.TorusStrip.PeriodicChartCrosscutIsotopy

open Set Schoenflies CurveComplex

/-- An actual supported periodic crosscut move removes the preimages of every
lattice translate of its two old crossings. No global event-update equality is
assumed, and parameters may describe an entire lift rather than a quotient. -/
theorem crossing_parameters_of_periodic_supported_crosscut_replacement
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
          (φ '' Plane.openSquare 0 1)) :
    {s | P.finalMap (γ s) ∈ L} =
      {s | γ s ∈ L} \ γ ⁻¹'
        (⋃ i : ℤ × ℤ, ({x + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T),
          y + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)} : Set Plane)) := by
  let S : Set Plane := ⋃ i : ℤ × ℤ, (fun z : Plane =>
    z + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) ''
      (φ '' Plane.openSquare 0 1)
  let AA : Set Plane := ⋃ i : ℤ × ℤ, (fun z : Plane =>
    z + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) '' A
  let BB : Set Plane := ⋃ i : ℤ × ℤ, (fun z : Plane =>
    z + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)) '' B
  let O : Set Plane := ⋃ i : ℤ × ℤ,
    ({x + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T),
      y + Plane.mk ((i.1 : ℝ) * T) ((i.2 : ℝ) * T)} : Set Plane)
  have hinside (s : α) (hs : γ s ∈ S) : P.finalMap (γ s) ∉ L := by
    have ha : γ s ∈ AA := hlocal ⟨⟨s, rfl⟩, hs⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp ha
    have hb : P.finalMap (γ s) ∈ BB := by
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [← hmove i]
      exact mem_image_of_mem _ hi
    exact fun hl => Set.disjoint_left.mp havoid hb hl
  have houtside (s : α) (hs : γ s ∉ S) : P.finalMap (γ s) = γ s :=
    hfix ⟨1, by norm_num⟩ (γ s) hs
  change {s | P.finalMap (γ s) ∈ L} = {s | γ s ∈ L} \ γ ⁻¹' O
  ext s
  constructor
  · intro hs
    change P.finalMap (γ s) ∈ L at hs
    have hn : γ s ∉ S := fun hi => hinside s hi hs
    refine ⟨?_, ?_⟩
    · change γ s ∈ L
      rw [houtside s hn] at hs
      exact hs
    · exact fun ho => hn (hcrossingsSupported ho)
  · rintro ⟨hl, ho⟩
    have hn : γ s ∉ S := by
      intro hi
      apply ho
      change γ s ∈ O
      have he : AA ∩ L = O := hold
      rw [← he]
      exact ⟨hlocal ⟨⟨s, rfl⟩, hi⟩, hl⟩
    change P.finalMap (γ s) ∈ L
    rw [houtside s hn]
    exact hl

#print axioms crossing_parameters_of_periodic_supported_crosscut_replacement
