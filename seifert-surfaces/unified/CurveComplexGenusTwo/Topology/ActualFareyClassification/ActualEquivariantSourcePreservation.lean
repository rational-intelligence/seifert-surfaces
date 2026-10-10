import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSupportedFamilyTransport

open Set Topology Schoenflies CurveComplex

theorem actual_equivariant_isotopy_preserves_normalized_source
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T : ℝ)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (i j : ℤ), G x=G y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0)
    (H : AmbientIsotopy Plane)
    (heq : ∀ t (i : ℤ×ℤ) z,
      H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) :
    ∃ G' : C(ℝ,Plane), (∀ x, G' x=H.finalMap (G x)) ∧ IsClosedEmbedding G' ∧
      (∀ (k : ℤ) (x : ℝ), G' (x+(k:ℝ)*T)=G' x+Plane.mk ((k:ℝ)*T) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ), G' x=G' y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0) := by
  obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have heFinal : ∀ z, e z=H.finalMap z := he
  let G' : C(ℝ,Plane) := ⟨fun x => e (G x),e.continuous.comp G.continuous⟩
  have hG' : IsClosedEmbedding G' := e.isClosedEmbedding.comp hG
  have hFinalEq (i : ℤ×ℤ) (z : Plane) :
      e (z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=e z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T) := by
    simpa only [he] using heq ⟨1,by norm_num⟩ i z
  refine ⟨G',fun x => heFinal _,hG',?_,?_⟩
  · intro k x
    change e (G (x+(k:ℝ)*T))=e (G x)+Plane.mk ((k:ℝ)*T) 0
    rw [hp]
    simpa only [Int.cast_zero,zero_mul] using hFinalEq (k,0) (G x)
  · intro x y i j hxy
    apply hc x y i j
    apply e.injective
    change e (G x)=e (G y)+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) at hxy
    exact hxy.trans (hFinalEq (i,j) (G y)).symm

#print axioms actual_equivariant_isotopy_preserves_normalized_source
