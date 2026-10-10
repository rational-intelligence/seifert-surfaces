import Schoenflies.JordanClosed

namespace CurveComplex

open Set Topology

/-- A Jordan curve carried by the closed bounded side of another has its own
bounded region in that side. Adapted from the corresponding monotonicity proof
in the ClassificationOfSurfaces JordanRegions port (Apache-2.0). -/
theorem jordan_inside_mono_of_boundary_subset_closed_inside
    {C K : Set Schoenflies.Plane}
    (hC : Schoenflies.IsSeparating C) (hK : Schoenflies.IsSeparating K)
    (hboundary : K ⊆ Schoenflies.inside C ∪ C) :
    Schoenflies.inside K ⊆ Schoenflies.inside C := by
  have houtsideCarrier : Disjoint (Schoenflies.outside C) K := by
    rw [Set.disjoint_left]
    intro x hxOutside hxK
    rcases hboundary hxK with hxInside | hxCarrier
    · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
        hxInside hxOutside
    · exact Schoenflies.outside_subset_compl hxOutside hxCarrier
  have houtsideRegions : Schoenflies.outside C ⊆
      Schoenflies.inside K ∪ Schoenflies.outside K := by
    rw [Schoenflies.inside_union_outside]
    intro x hxOutside hxCarrier
    exact Set.disjoint_left.mp houtsideCarrier hxOutside hxCarrier
  have houtsideSubset : Schoenflies.outside C ⊆ Schoenflies.outside K := by
    rcases hC.isConnected_outside.isPreconnected.subset_or_subset
        hK.isOpen_inside hK.isOpen_outside Schoenflies.disjoint_inside_outside
        houtsideRegions with hInside | hOutside
    · exact False.elim
        (hC.not_isBounded_outside (hK.isBounded_inside.subset hInside))
    · exact hOutside
  intro x hxKInside
  have hxNotCarrier : x ∉ C := by
    intro hxCarrier
    have hxClosure : x ∈ closure (Schoenflies.outside C) := by
      apply frontier_subset_closure
      rw [hC.frontier_outside]
      exact hxCarrier
    have hxInterClosure : x ∈ closure (Schoenflies.inside K ∩ Schoenflies.outside C) :=
      hK.isOpen_inside.inter_closure ⟨hxKInside, hxClosure⟩
    obtain ⟨y, hyKInside, hyCOutside⟩ :=
      Set.Nonempty.of_closure ⟨x, hxInterClosure⟩
    exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
      hyKInside (houtsideSubset hyCOutside)
  rcases (show x ∈ Schoenflies.inside C ∪ Schoenflies.outside C by
      rw [Schoenflies.inside_union_outside]; exact hxNotCarrier) with hxInside | hxOutside
  · exact hxInside
  · exact False.elim <| Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
      hxKInside (houtsideSubset hxOutside)

/-- A disjoint Jordan boundary lies wholly on one side of a separating Jordan
curve. -/
theorem jordan_boundary_subset_inside_or_outside
    {C K : Set Schoenflies.Plane}
    (hC : Schoenflies.IsSeparating C) (hK : Schoenflies.IsSeparating K)
    (hdisj : Disjoint C K) :
    K ⊆ Schoenflies.inside C ∨ K ⊆ Schoenflies.outside C := by
  obtain ⟨W, V, hpair, hsub⟩ := hC.exists_isRegionPair_subset
    hK.isJordanCurve.isConnected.isPreconnected hK.isJordanCurve.nonempty hdisj.symm
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hsub
  · exact Or.inr hsub

/-- If two disjoint Jordan boundaries lie on one another's unbounded sides,
their closed bounded regions are disjoint. -/
theorem jordan_closed_insides_disjoint_of_mutual_outside
    {C K : Set Schoenflies.Plane}
    (hC : Schoenflies.IsSeparating C) (hK : Schoenflies.IsSeparating K)
    (hCK : C ⊆ Schoenflies.outside K)
    (hKC : K ⊆ Schoenflies.outside C) :
    Disjoint (Schoenflies.inside C ∪ C) (Schoenflies.inside K ∪ K) := by
  have hinsideCcompK : Schoenflies.inside C ⊆ Kᶜ := by
    intro x hx hKx
    exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
      hx (hKC hKx)
  have hcover : Schoenflies.inside C ⊆
      Schoenflies.inside K ∪ Schoenflies.outside K := by
    rw [Schoenflies.inside_union_outside]
    exact hinsideCcompK
  have hinsideCoutsideK : Schoenflies.inside C ⊆ Schoenflies.outside K := by
    rcases hC.isConnected_inside.isPreconnected.subset_or_subset
        hK.isOpen_inside hK.isOpen_outside Schoenflies.disjoint_inside_outside
        hcover with hinside | houtside
    · obtain ⟨x, hxC⟩ := hC.isJordanCurve.nonempty
      have hxClosure : x ∈ closure (Schoenflies.inside C) := by
        apply frontier_subset_closure
        rw [hC.frontier_inside]
        exact hxC
      have hxClosureK : x ∈ closure (Schoenflies.inside K) :=
        closure_mono hinside hxClosure
      have hxInter : x ∈ closure
          (Schoenflies.outside K ∩ Schoenflies.inside K) :=
        hK.isOpen_outside.inter_closure ⟨hCK hxC, hxClosureK⟩
      obtain ⟨y, hyOutside, hyInside⟩ :=
        Set.Nonempty.of_closure ⟨x, hxInter⟩
      exact False.elim
        (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hyInside hyOutside)
    · exact houtside
  apply Set.disjoint_left.mpr
  intro x hxC hxK
  rcases hxC with hxC | hxC <;> rcases hxK with hxK | hxK
  · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
      hxK (hinsideCoutsideK hxC)
  · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
      hxC (hKC hxK)
  · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
      hxK (hCK hxC)
  · exact Schoenflies.outside_subset_compl (hCK hxC) hxK

/-- Two disjoint separating Jordan curves have disjoint or nested closed
bounded regions. This is the precise planar alternative needed by the deck
translate argument. -/
theorem jordan_closed_insides_disjoint_or_nested
    {C K : Set Schoenflies.Plane}
    (hC : Schoenflies.IsSeparating C) (hK : Schoenflies.IsSeparating K)
    (hdisj : Disjoint C K) :
    Disjoint (Schoenflies.inside C ∪ C) (Schoenflies.inside K ∪ K) ∨
    Schoenflies.inside C ∪ C ⊆ Schoenflies.inside K ∪ K ∨
    Schoenflies.inside K ∪ K ⊆ Schoenflies.inside C ∪ C := by
  rcases jordan_boundary_subset_inside_or_outside hC hK hdisj with hKinside | hKoutside
  · right
    right
    have hmono := jordan_inside_mono_of_boundary_subset_closed_inside
      hC hK (fun x hx => Or.inl (hKinside hx))
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (hmono hx)
    · exact Or.inl (hKinside hx)
  · rcases jordan_boundary_subset_inside_or_outside hK hC hdisj.symm with
      hCinside | hCoutside
    · right
      left
      have hmono := jordan_inside_mono_of_boundary_subset_closed_inside
        hK hC (fun x hx => Or.inl (hCinside hx))
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl (hmono hx)
      · exact Or.inl (hCinside hx)
    · left
      exact jordan_closed_insides_disjoint_of_mutual_outside hC hK hCoutside hKoutside

/-- The disjoint-or-nested alternative stated directly for Jordan curves;
the imported Jordan curve theorem supplies separation. -/
theorem jordan_curve_closed_regions_disjoint_or_nested
    {C K : Set Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C) (hK : Schoenflies.IsJordanCurve K)
    (hdisj : Disjoint C K) :
    Disjoint (Schoenflies.inside C ∪ C) (Schoenflies.inside K ∪ K) ∨
    Schoenflies.inside C ∪ C ⊆ Schoenflies.inside K ∪ K ∨
    Schoenflies.inside K ∪ K ⊆ Schoenflies.inside C ∪ C :=
  jordan_closed_insides_disjoint_or_nested
    (Schoenflies.jordan_curve_theorem hC)
    (Schoenflies.jordan_curve_theorem hK) hdisj

/-- Jordan curves are preserved by ambient homeomorphisms of the plane. -/
theorem jordan_curve_homeomorph_image
    {C : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C)
    (t : Schoenflies.Plane ≃ₜ Schoenflies.Plane) :
    Schoenflies.IsJordanCurve (t '' C) := by
  obtain ⟨r, hr, hrange⟩ := hC
  refine ⟨fun s => t (r s), ?_, ?_⟩
  · refine ⟨t.continuous.comp_continuousOn hr.continuousOn, ?_, ?_⟩
    · exact congrArg t hr.closes
    · intro x hx y hy hxy
      exact hr.injOn hx hy (t.injective hxy)
  · change (t ∘ r) '' unitInterval = t '' C
    rw [Set.image_comp, hrange]

/-- Plane homeomorphisms preserve bounded sets, by compactness of closures in
the proper Euclidean plane. -/
theorem bounded_homeomorph_image
    (t : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {s : Set Schoenflies.Plane} (hs : Bornology.IsBounded s) :
    Bornology.IsBounded (t '' s) := by
  exact ((hs.isCompact_closure.image t.continuous).isBounded).subset
    (Set.image_mono subset_closure)

/-- The bounded complementary region is invariant under ambient
homeomorphisms of the plane. -/
theorem jordan_inside_homeomorph_image
    (t : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    (C : Set Schoenflies.Plane) :
    t '' Schoenflies.inside C = Schoenflies.inside (t '' C) := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    have hxC : x ∉ C := hx.1
    have hmem : t x ∉ t '' C := by
      intro ht
      obtain ⟨y, hy, hxy⟩ := ht
      exact hxC (t.injective hxy ▸ hy)
    refine ⟨hmem, ?_⟩
    have hcomp := t.image_connectedComponentIn (s := Cᶜ) hxC
    rw [t.image_compl] at hcomp
    rw [← hcomp]
    exact bounded_homeomorph_image t hx.2
  · intro z hz
    have hz' : t.symm z ∈ Schoenflies.inside C := by
      have hzC : t.symm z ∉ C := by
        intro hCz
        exact hz.1 ⟨t.symm z, hCz, t.apply_symm_apply z⟩
      refine ⟨hzC, ?_⟩
      have hcomp := t.symm.image_connectedComponentIn
        (s := (t '' C)ᶜ) hz.1
      have him : t.symm '' (t '' C) = C := by
        ext x
        simp
      rw [t.symm.image_compl, him] at hcomp
      rw [← hcomp]
      exact bounded_homeomorph_image t.symm hz.2
    exact ⟨t.symm z, hz', t.apply_symm_apply z⟩

/-- The exact planar Jordan alternative for a translated embedded disc, once
both disc carriers have been identified with their bounded Jordan regions. -/
theorem planar_disc_translate_disjoint_or_nested
    (d : C(Metric.closedBall (0 : Schoenflies.Plane) 1, Schoenflies.Plane))
    (C : Set Schoenflies.Plane)
    (hC : Schoenflies.IsJordanCurve C)
    (hregion : Set.range d = Schoenflies.inside C ∪ C)
    (t : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    (hboundaryDisjoint : Disjoint C (t '' C)) :
    Disjoint (Set.range d) (t '' Set.range d) ∨
    Set.range d ⊆ t '' Set.range d ∨
    t '' Set.range d ⊆ Set.range d := by
  have hregionT : t '' Set.range d =
      Schoenflies.inside (t '' C) ∪ (t '' C) := by
    rw [hregion, Set.image_union, jordan_inside_homeomorph_image]
  simpa only [← hregion, ← hregionT] using
    jordan_curve_closed_regions_disjoint_or_nested
      hC (jordan_curve_homeomorph_image hC t) hboundaryDisjoint

end CurveComplex
