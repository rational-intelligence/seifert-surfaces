import CurveComplexGenusTwo.Topology.ActualFareyClassification.PeriodicSpatialMinimum
import CurveComplexGenusTwo.Topology.TorusStrip.NormalizedDeckFamily
import CurveComplexGenusTwo.Topology.TorusStrip.NestedBands
import Schoenflies.JordanClosed
import Mathlib
open Set Schoenflies Bornology Topology

/-- A bounded nonempty planar set cannot be contained in a nontrivial
vertical translate of itself. -/
theorem bounded_ne_subset_vertical_translate (S : Set Plane) (hS : IsBounded S)
    (hne : S.Nonempty) (a : ℝ) (ha : a ≠ 0) :
    ¬ S ⊆ (Homeomorph.addRight (Plane.mk 0 a)) '' S := by
  intro hsub
  let e : Plane ≃ₜ Plane := Homeomorph.addRight (Plane.mk 0 a)
  have hcl : closure S ⊆ e '' closure S := by
    rw [e.image_closure]
    exact closure_mono hsub
  have hc := hS.isCompact_closure
  have hn : (closure S).Nonempty := hne.mono subset_closure
  rcases lt_or_gt_of_ne ha with ha | ha
  · obtain ⟨x,hx,hmax⟩ := hc.exists_isMaxOn hn (EuclideanSpace.proj 1).continuous.continuousOn
    obtain ⟨y,hy,he⟩ := hcl hx
    have hxy : y 1 ≤ x 1 := hmax hy
    have he0 := congrArg (fun z : Plane => z 1) he
    change y 1+a=x 1 at he0
    linarith
  · obtain ⟨x,hx,hmin⟩ := hc.exists_isMinOn hn (EuclideanSpace.proj 1).continuous.continuousOn
    obtain ⟨y,hy,he⟩ := hcl hx
    have hxy : x 1 ≤ y 1 := hmin hy
    have he0 := congrArg (fun z : Plane => z 1) he
    change y 1+a=x 1 at he0
    linarith

/-- Boundary avoidance suffices even when adjacent Jordan boundaries share
an edge: overlap forces nesting of the bounded open regions, which a
nontrivial translation cannot do. -/
theorem vertical_row_disjoint_of_boundary_avoidance (C : Set Plane) (hC : IsJordanCurve C)
    (T : ℝ) (hT : 0 < T)
    (havoid : ∀ n : ℤ, Disjoint (inside C)
      ((Homeomorph.addRight (Plane.mk 0 ((n:ℝ)*T))) '' C)) :
    Pairwise (fun i j : ℤ => Disjoint
      (inside ((fun z : Plane => z+Plane.mk 0 ((i:ℝ)*T)) '' C))
      (inside ((fun z : Plane => z+Plane.mk 0 ((j:ℝ)*T)) '' C))) := by
  let X : ℤ → Plane ≃ₜ Plane := fun n => Homeomorph.addRight (Plane.mk 0 ((n:ℝ)*T))
  have hsep := jordan_curve_theorem hC
  have base (n : ℤ) (hn : n ≠ 0) : Disjoint (inside C) (inside (X n '' C)) := by
    have hCn : IsJordanCurve (X n '' C) := by
      obtain ⟨g,hg,hgC⟩ := hC
      refine ⟨(X n) ∘ g, ⟨(X n).continuous.comp_continuousOn hg.continuousOn, ?_, ?_⟩, ?_⟩
      · simp only [Function.comp_apply,hg.closes]
      · exact (X n).injective.injOn.comp hg.injOn (mapsTo_univ _ _)
      · rw [image_comp,hgC]
    have hsepn := jordan_curve_theorem hCn
    have hcover : inside C ⊆ inside (X n '' C) ∪ outside (X n '' C) := by
      rw [inside_union_outside]
      exact fun z hz h => disjoint_left.mp (havoid n) hz h
    rcases hsep.isConnected_inside.isPreconnected.subset_or_subset
        hsepn.isOpen_inside hsepn.isOpen_outside disjoint_inside_outside hcover with h | h
    · rw [← (plane_homeomorph_inside_transport (X n) C).1] at h
      exact False.elim (bounded_ne_subset_vertical_translate (inside C)
        hsep.isBounded_inside hsep.isConnected_inside.nonempty ((n:ℝ)*T)
        (mul_ne_zero (by exact_mod_cast hn) hT.ne') h)
    · exact disjoint_left.mpr (fun z hz hz' => disjoint_left.mp disjoint_inside_outside hz' (h hz))
  have comp (i j : ℤ) (S : Set Plane) : X (i+j) '' S = X i '' (X j '' S) := by
    rw [← image_comp]
    congr 1
    funext z
    ext k
    fin_cases k
    · simp [X,Plane.mk]
    · simp [X,Plane.mk,Int.cast_add]
      ring
  intro i j hij
  change Disjoint (inside (X i '' C)) (inside (X j '' C))
  rw [← (plane_homeomorph_inside_transport (X i) C).1,
    ← (plane_homeomorph_inside_transport (X j) C).1]
  have hj : j=i+(j-i) := by omega
  rw [hj,comp]
  have hb := base (j-i) (by omega)
  rw [← (plane_homeomorph_inside_transport (X (j-i)) C).1] at hb
  exact (disjoint_image_iff (X i).injective).mpr hb

#print axioms bounded_ne_subset_vertical_translate
#print axioms vertical_row_disjoint_of_boundary_avoidance


/-- Empty interior against the full line family implies avoidance of every
vertical translate of the entire bigon boundary, including its fiber side. -/
theorem fiber_bigon_vertical_boundary_avoidance
    (G : C(ℝ,Plane)) (T c r s : ℝ)
    (hr : G r 0=c) (hs : G s 0=c)
    (hno : ∀ t ∈ Ioo r s, G t 0≠c)
    (hC : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (hempty : Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
      (⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T)))) :
    ∀ j : ℤ, Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
      ((Homeomorph.addRight (Plane.mk 0 ((j:ℝ)*T))) ''
        ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) := by
  intro j
  apply disjoint_left.mpr
  rintro z hz ⟨w,hw,rfl⟩
  rcases hw with hw | hw
  · obtain ⟨t,ht,rfl⟩ := hw
    exact disjoint_left.mp hempty hz (mem_iUnion.mpr ⟨j,t,rfl⟩)
  · have hwc : w 0=c := by
      rw [segment_eq_image_lineMap] at hw
      obtain ⟨v,hv,rfl⟩ := hw
      simp only [AffineMap.lineMap_apply]
      change v*(G s 0-G r 0)+G r 0=c
      rw [hr,hs]
      ring
    have hh := fiber_free_interval_bigon_inside_avoids_fiber G c r s hr hs hno hC _ hz
    apply hh
    simpa [Homeomorph.addRight,Plane.mk] using hwc

/-- The selected periodic-line-empty disk has disjoint vertical translates.
No boundary-avoidance or disk-separation receipt is assumed. -/
theorem actual_vertical_family_select_separated_bigon
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hcount : 1 < {t : ℝ | G t 0=c}.ncard)
    (hpair : Pairwise (fun i j : ℤ => Disjoint
      (range (fun t => G t+Plane.mk 0 ((i:ℝ)*T)))
      (range (fun t => G t+Plane.mk 0 ((j:ℝ)*T)))))
    (hlf : LocallyFinite (fun j : ℤ => range (fun t => G t+Plane.mk 0 ((j:ℝ)*T)))) :
    ∃ r s : ℝ, r<s ∧ G r 0=c ∧ G s 0=c ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      (∀ t ∈ Ioo r s, G t 0≠c) ∧
      Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
        (⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))) ∧
      Pairwise (fun i j : ℤ => Disjoint
        (inside ((fun z : Plane => z+Plane.mk 0 ((i:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
        (inside ((fun z : Plane => z+Plane.mk 0 ((j:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) := by
  obtain ⟨r,s,hrs,hr,hs,hC,hno,he⟩ :=
    actual_vertical_family_select_interior_empty_bigon G hG T c hfinite hcount hpair hlf
  exact ⟨r,s,hrs,hr,hs,hC,hno,he,
    vertical_row_disjoint_of_boundary_avoidance _ hC T hT
      (fiber_bigon_vertical_boundary_avoidance G T c r s hr hs hno hC he)⟩

#print axioms fiber_bigon_vertical_boundary_avoidance
#print axioms actual_vertical_family_select_separated_bigon

/-- Normalized actual source data supplies the whole deck-family geometry;
only actual finite fiber intersections are input, with no empty disk receipt. -/
theorem normalized_actual_line_select_periodically_empty_bigon
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ),
      G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hcount : 1 < {t : ℝ | G t 0=c}.ncard) :
    ∃ r s : ℝ, r<s ∧ G r 0=c ∧ G s 0=c ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      (∀ t ∈ Ioo r s, G t 0≠c) ∧
      Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
        (⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))) ∧
      Pairwise (fun i j : ℤ => Disjoint
        (inside ((fun z : Plane => z+Plane.mk 0 ((i:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
        (inside ((fun z : Plane => z+Plane.mk 0 ((j:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) := by
  obtain ⟨hclosed,hpair,hlf⟩ := normalized_line_deck_family G hG T hT hp hc
  exact actual_vertical_family_select_separated_bigon G hG T c hT hfinite hcount hpair hlf

#print axioms normalized_actual_line_select_periodically_empty_bigon
