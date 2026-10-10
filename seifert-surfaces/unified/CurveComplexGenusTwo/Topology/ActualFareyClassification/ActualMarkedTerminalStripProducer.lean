import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTerminalStripArc
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedReferenceClass

open Set Topology Schoenflies CurveComplex

/-- From the original normalized actual finite transverse source, construct
marked finite descent, its actual terminal fundamental strip, and a puncture-
relative isotopy relating the EXPLICIT final reference class to the old one. -/
theorem normalized_actual_source_has_marked_terminal_strip_and_relative_reference
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (htrans : ∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) → q 0=c+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 0=c+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
    (p : Plane) (hpgrid : ∀ i : ℤ, p 0+(i:ℝ)*T≠c)
    (hGM : Disjoint (range G)
      (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)})) :
    ∃ P Q : AmbientIsotopy Plane, ∃ Gf : C(ℝ,Plane), ∃ cf r : ℝ,
      (∀ x, Gf x=P.finalMap (G x)) ∧
      (∀ t (i : ℤ×ℤ), P.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ) z, P.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        P.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ), Q.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ) z, Q.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        Q.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      Q.finalMap '' {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}=
        {z : Plane | ∃ i : ℤ, z 0=cf+(i:ℝ)*T} ∧
      IsClosedEmbedding Gf ∧
      (∀ (k : ℤ) (x : ℝ), Gf (x+(k:ℝ)*T)=Gf x+Plane.mk ((k:ℝ)*T) 0) ∧
      (∀ (x y : ℝ) (i j : ℤ), Gf x=Gf y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0) ∧
      (∀ i : ℤ, p 0+(i:ℝ)*T≠cf) ∧
      Disjoint (range Gf) (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)}) ∧
      {t : ℝ | Gf t 0=cf}={r} ∧
      {t : ℝ | ∃ i : ℤ, Gf t 0=cf+(i:ℝ)*T}=range (fun i : ℤ => r+(i:ℝ)*T) ∧
      Gf r 0=cf ∧ Gf (r+T)=Gf r+Plane.mk T 0 ∧
      (∀ t∈Ioo r (r+T), cf<Gf t 0 ∧ Gf t 0<cf+T) ∧
      (∀ t∈Ioo (0:ℝ) 1, AffineMap.lineMap (Gf r) (Gf r+Plane.mk 0 T) t∉
        (⋃ j : ℤ, range (fun x : ℝ => Gf x+Plane.mk 0 ((j:ℝ)*T)))) ∧
      (∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => Gf x+Plane.mk 0 ((j:ℝ)*T))) → q 0=cf+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 0=cf+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => Gf x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
 := by
  obtain ⟨P,Gf,cf,hGfEq,hPfix,hPeq,hGf,hpf,hcf,hReference,hGMf,hFinite,hCount,_,hTrans⟩ :=
    normalized_actual_transverse_has_puncture_relative_finite_descent G hG T c hT hp hc hfinite htrans p hpgrid hGM
  obtain ⟨r,hFiber,hGrid⟩ := actual_terminal_source_has_one_crossing_and_exact_grid_parameters Gf T cf hT hpf hFinite hCount
  obtain ⟨hr,hEnd,hStrip⟩ := actual_single_fiber_source_has_strict_fundamental_strip_arc Gf T cf r hT hpf hFiber
  have hConnector := actual_single_fiber_source_has_actual_vertical_adjacent_connector Gf T cf r hT hFiber
  obtain ⟨Q,hQfix,hQeq,hQgrid⟩ := actual_puncture_free_vertical_reference_grids_are_relative_isotopic T c cf p hT hpgrid hReference
  exact ⟨P,Q,Gf,cf,r,hGfEq,hPfix,hPeq,hQfix,hQeq,hQgrid,hGf,hpf,hcf,hReference,hGMf,
    hFiber,hGrid,hr,hEnd,hStrip,hConnector,hTrans⟩

#print axioms normalized_actual_source_has_marked_terminal_strip_and_relative_reference
