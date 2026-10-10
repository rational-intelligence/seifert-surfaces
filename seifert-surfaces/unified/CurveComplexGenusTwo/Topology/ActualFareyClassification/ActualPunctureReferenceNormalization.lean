import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualPunctureGridCorrection
import CurveComplexGenusTwo.Topology.ActualFareyClassification.OnePunctureNormalization

open Set Topology Schoenflies CurveComplex

/-- The concrete puncture correction followed by actual pinning fixes the
puncture orbit and makes the EXPLICIT translated reference puncture-free. -/
theorem actual_move_has_puncture_free_translated_reference
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (i j : ℤ), G x=G y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0)
    (p : Plane)
    (hGM : Disjoint (range G) (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)}))
    (H : AmbientIsotopy Plane)
    (heq : ∀ t (i : ℤ×ℤ) z,
      H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) :
    ∃ K P : AmbientIsotopy Plane,
      (∀ x, K.finalMap (G x)=H.finalMap (G x)) ∧
      (∀ t (i : ℤ×ℤ), P.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ) z,
        P.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          P.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ x, P.finalMap (G x)=H.finalMap (G x)-K.finalMap p+p) ∧
      (∀ i : ℤ, p 0+(i:ℝ)*T≠c-K.finalMap p 0+p 0) ∧
      Disjoint (P.finalMap '' range G)
        (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)}) := by
  obtain ⟨K,hKeq,hKG,hKgrid⟩ := actual_equivariant_move_has_puncture_grid_correction G hG T c hT hp hc p hGM H heq
  obtain ⟨P,hP,hPeq,hPfix,_⟩ := equivariant_ambient_isotopy_pin_one_puncture K T p hKeq
  have hFinal (z : Plane) : P.finalMap z=K.finalMap z-K.finalMap p+p := hP ⟨1,by norm_num⟩ z
  refine ⟨K,P,hKG,hPfix,hPeq,?_,?_,?_⟩
  · intro x
    rw [hFinal,hKG]
  · intro i hi
    apply hKgrid (-i)
    push_cast
    linarith
  · apply disjoint_left.mpr
    rintro z ⟨w,hw,he⟩ hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    have hi' : z=p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T) := hi
    have hPmark : P.finalMap (p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T) := hPfix ⟨1,by norm_num⟩ i
    obtain ⟨e,heHomeo⟩ := P.homeomorphism_at ⟨1,by norm_num⟩
    have hInj : Function.Injective P.finalMap := by
      intro x y hxy
      apply e.injective
      simpa only [heHomeo,AmbientIsotopy.finalMap] using hxy
    have hwmark : w=p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T) :=
      hInj (he.trans (hi'.trans hPmark.symm))
    exact disjoint_left.mp hGM hw (mem_iUnion.mpr ⟨i,hwmark⟩)

#print axioms actual_move_has_puncture_free_translated_reference
