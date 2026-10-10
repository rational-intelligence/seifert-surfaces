import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCrossingChartRestriction
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSupportedFamilyTransport

open Set Topology Schoenflies CurveComplex

/-- The actual exact erase and supported source geometry renew the entire
simultaneous-axis transversality structure by restricting old charts to the
constructed fixed neighborhoods. -/
theorem actual_supported_erase_renews_whole_family_transversality
    (G : C(ℝ,Plane)) (T a b c r s : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (phi : Plane ≃ₜ Plane)
    (hcontact : (phi '' Plane.closedSquare 0 1)∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=G '' Icc a b)
    (hold : (G '' Icc a b)∩{z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}={G r,G s})
    (H : AmbientIsotopy Plane)
    (heq : ∀ t (i : ℤ×ℤ) z,
      H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))
    (hfix : ∀ t z, z∉⋃ i : ℤ×ℤ,
      (fun w : Plane => w+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (phi '' Plane.openSquare 0 1) →
      H.map (t,z)=z)
    (herase : {t : ℝ | ∃ i : ℤ, H.finalMap (G t) 0=c+(i:ℝ)*T}=
      {t : ℝ | ∃ i : ℤ, G t 0=c+(i:ℝ)*T}\G ⁻¹'
        (⋃ i : ℤ×ℤ, ({G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
          G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)))
    (htrans : ∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) → q 0=c+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 0=c+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
     : ∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => H.finalMap (G x)+Plane.mk 0 ((j:ℝ)*T))) → q 0=c+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 0=c+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => H.finalMap (G x)+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)) := by
  intro q i hq hi
  obtain ⟨j,x,hx⟩ := mem_iUnion.mp hq
  change H.finalMap (G x)+Plane.mk 0 ((j:ℝ)*T)=q at hx
  have hFinalGrid : ∃ i : ℤ, H.finalMap (G x) 0=c+(i:ℝ)*T := by
    refine ⟨i,?_⟩
    rw [←hx] at hi
    simpa [Plane.mk] using hi
  have hSource : x∈{t : ℝ | ∃ i : ℤ, G t 0=c+(i:ℝ)*T}\G ⁻¹'
      (⋃ i : ℤ×ℤ, ({G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
        G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)) := herase ▸ hFinalGrid
  have hGL : G x∈⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)) := by
    refine mem_iUnion.mpr ⟨0,x,?_⟩
    ext k; fin_cases k <;> simp [Plane.mk]
  obtain ⟨N,hN,hxN,hNfix⟩ := normalized_actual_surviving_crossing_has_fixed_open_neighborhood
    G T a b c r s hT hp phi hcontact hold H hfix (G x) hGL hSource.1 hSource.2
  have hFinalx : H.finalMap (G x)=G x := hNfix ⟨1,by norm_num⟩ (G x) hxN
  have hqOld : G x+Plane.mk 0 ((j:ℝ)*T)=q := by rwa [hFinalx] at hx
  let d := Plane.mk 0 ((j:ℝ)*T)
  let F := Homeomorph.addRight d
  let M := F '' N
  have hM : IsOpen M := F.isOpenMap _ hN
  have hqM : q∈M := ⟨G x,hxN,hqOld⟩
  have hMfix : ∀ t z, z∈M → H.map (t,z)=z := by
    intro t z hz
    obtain ⟨w,hw,rfl⟩ := hz
    change H.map (t,w+d)=w+d
    have hh := heq t (0,j) w
    simpa only [Int.cast_zero,zero_mul,hNfix t w hw] using hh
  have hqOriginal : q∈⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)) :=
    mem_iUnion.mpr ⟨j,x,hqOld⟩
  obtain ⟨U,V,hqU,h,hU,hV,hq0,haxis⟩ := htrans q i hqOriginal hi
  obtain ⟨W,hW,e,heChart⟩ := actual_crossing_chart_restrict_to_open U V hU hV h M hM
  refine ⟨U∩M,W,⟨hqU,hqM⟩,e,hU.inter hM,hW,?_,?_⟩
  · exact (heChart q ⟨hqU,hqM⟩).trans hq0
  · intro z hz
    rw [heChart z hz]
    obtain ⟨hfirst,hsecond⟩ := haxis z hz.1
    refine ⟨hfirst,?_⟩
    rw [actual_fixed_neighborhood_row_family_membership G H T heq M hMfix z hz.2]
    exact hsecond

#print axioms actual_supported_erase_renews_whole_family_transversality
