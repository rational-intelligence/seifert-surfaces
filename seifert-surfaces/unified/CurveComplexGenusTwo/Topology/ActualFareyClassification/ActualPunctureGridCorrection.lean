import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualPointOffGridRelativeFamily
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualEquivariantSourcePreservation
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFamilySupportOrbit

open Set Topology Schoenflies CurveComplex

theorem actual_puncture_free_source_outside_row_family
    (G : ℝ→Plane) (T : ℝ) (p : Plane)
    (hGM : Disjoint (range G) (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)})) :
    p∉⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)) := by
  intro hp
  obtain ⟨j,x,hx⟩ := mem_iUnion.mp hp
  change G x+Plane.mk 0 ((j:ℝ)*T)=p at hx
  have hOrbit : G x∈⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} := by
    refine mem_iUnion.mpr ⟨(0,-j),?_⟩
    change G x=p+Plane.mk (((0:ℤ):ℝ)*T) (((-j:ℤ):ℝ)*T)
    have hh : Plane.mk (((0:ℤ):ℝ)*T) (((-j:ℤ):ℝ)*T)=-Plane.mk 0 ((j:ℝ)*T) := by
      ext n; fin_cases n <;> simp [Plane.mk]
    rw [hh,←hx]
    abel
  exact disjoint_left.mp hGM (mem_range_self _) hOrbit

/-- Actual normalized source data builds the point correction after ANY actual
equivariant move. It leaves the moved source pointwise unchanged and makes the
moved puncture avoid the reference grid; no separation or correction certificate
is a premise. -/
theorem actual_equivariant_move_has_puncture_grid_correction
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (i j : ℤ), G x=G y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0)
    (p : Plane)
    (hGM : Disjoint (range G) (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)}))
    (H : AmbientIsotopy Plane)
    (heq : ∀ t (i : ℤ×ℤ) z,
      H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) :
    ∃ K : AmbientIsotopy Plane,
      (∀ t (i : ℤ×ℤ) z,
        K.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          K.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ x, K.finalMap (G x)=H.finalMap (G x)) ∧
      (∀ i : ℤ, K.finalMap p 0≠c+(i:ℝ)*T) := by
  obtain ⟨G',hEq,hG',hp',hc'⟩ := actual_equivariant_isotopy_preserves_normalized_source G hG T hp hc H heq
  let L := ⋃ j : ℤ, range (fun x : ℝ => G' x+Plane.mk 0 ((j:ℝ)*T))
  obtain ⟨hClosed,_,hlf⟩ := normalized_line_deck_family G' hG' T hT hp' hc'
  have hL : IsClosed L := hlf.isClosed_iUnion hClosed
  have hInv : ∀ (i : ℤ×ℤ) z,
      z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)∈L ↔ z∈L := by
    intro i z
    exact (normalized_actual_row_family_lattice_invariant G' T hp' i z).symm
  have hImage : H.finalMap '' (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=L := by
    rw [actual_equivariant_final_map_row_family_image G H T heq]
    simp only [L,hEq]
  obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hInj : Function.Injective H.finalMap := by
    intro x y hxy
    apply e.injective
    simpa only [he,AmbientIsotopy.finalMap] using hxy
  have hOutside : H.finalMap p∉L := by
    rw [←hImage]
    rintro ⟨z,hz,he⟩
    have hzp := hInj he
    exact actual_puncture_free_source_outside_row_family G T p hGM (hzp ▸ hz)
  obtain ⟨J,hJeq,hJfix,hJgrid⟩ := actual_outside_point_can_avoid_grid_fixing_family L hL T c hT hInv
    (H.finalMap p) hOutside
  let K := H.compose J
  refine ⟨K,?_,?_,hJgrid⟩
  · intro t i z
    change J.map (t,H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)))=
      J.map (t,H.map (t,z))+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
    rw [heq,hJeq]
  · intro x
    change J.finalMap (H.finalMap (G x))=H.finalMap (G x)
    apply hJfix ⟨1,by norm_num⟩
    have hx : G' x∈L := by
      refine mem_iUnion.mpr ⟨0,x,?_⟩
      ext n; fin_cases n <;> simp [Plane.mk]
    rwa [hEq] at hx

#print axioms actual_puncture_free_source_outside_row_family
#print axioms actual_equivariant_move_has_puncture_grid_correction
