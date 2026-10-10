import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTransverseEndpointSelection

open Set Topology Schoenflies

/-- Actual transversality at the two old corners chooses enlarged SOURCE
endpoints on the far side of the supporting fiber. No endpoint choice or
shortness certificate for the enlarged interval is supplied. -/
theorem normalized_one_sided_bigon_has_actual_far_side_endpoints
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s c : ℝ) (hT : 0<T)
    (hrs : r<s) (hshort : s-r<T)
    (hp : ∀ (k : ℤ) (u : ℝ), G (u+(k:ℝ)*T)=G u+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hr : G r 0=c) (hs : G s 0=c)
    (hside : (∀ t∈Icc r s, G t 0 ≤ c) ∨ (∀ t∈Icc r s, c ≤ G t 0))
    (htrans : ∀ t, G t 0=c →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (htU : G t∈U) (h : U ≃ₜ V),
      IsOpen U ∧ IsOpen V ∧ ((h ⟨G t,htU⟩ : V) : ℝ×ℝ)=(0,0) ∧
      (∀ z (hz : z∈U),
        (z 0=c ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
        (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
          ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
    (N M : Set Plane) (hN : IsOpen N) (hM : IsOpen M)
    (hrN : G r∈N) (hsM : G s∈M) :
    ∃ a b : ℝ, a<r ∧ s<b ∧ b-a<T ∧ G a∈N ∧ G b∈M ∧
      (((∀ t∈Icc r s, G t 0 ≤ c) ∧ c<G a 0 ∧ c<G b 0) ∨
       ((∀ t∈Icc r s, c ≤ G t 0) ∧ G a 0<c ∧ G b 0<c)) := by
  let d := min ((s-r)/2) ((T-(s-r))/4)
  have hd : 0<d := by dsimp [d]; positivity
  have hdsr : d<s-r := by
    have hh := min_le_left ((s-r)/2) ((T-(s-r))/4)
    dsimp [d]; linarith
  have hdT : d ≤ (T-(s-r))/4 := min_le_right _ _
  obtain ⟨U,V,hrU,h,hU,hV,hr0,haxr⟩ := htrans r hr
  obtain ⟨Ur,Vr,hsU,j,hUr,hVr,hs0,haxs⟩ := htrans s hs
  have hpr := normalized_transverse_family_has_both_sides_near_parameter
    G hG T r c d hT hd hp hc hr U V hrU h hU hV hr0 haxr N hN hrN
  have hps := normalized_transverse_family_has_both_sides_near_parameter
    G hG T s c d hT hd hp hc hs Ur Vr hsU j hUr hVr hs0 haxs M hM hsM
  rcases hside with hleft|hright
  · obtain ⟨a,ha,haN,hac⟩ := hpr.2
    obtain ⟨b,hb,hbM,hbc⟩ := hps.2
    have har : a<r := by
      by_contra hh
      have haI : a∈Icc r s := ⟨le_of_not_gt hh,by linarith [ha.2]⟩
      exact not_lt_of_ge (hleft a haI) hac
    have hsb : s<b := by
      by_contra hh
      have hbI : b∈Icc r s := ⟨by linarith [hb.1],le_of_not_gt hh⟩
      exact not_lt_of_ge (hleft b hbI) hbc
    refine ⟨a,b,har,hsb,?_,haN,hbM,Or.inl ⟨hleft,hac,hbc⟩⟩
    linarith [ha.1,hb.2]
  · obtain ⟨a,ha,haN,hac⟩ := hpr.1
    obtain ⟨b,hb,hbM,hbc⟩ := hps.1
    have har : a<r := by
      by_contra hh
      have haI : a∈Icc r s := ⟨le_of_not_gt hh,by linarith [ha.2]⟩
      exact not_lt_of_ge (hright a haI) hac
    have hsb : s<b := by
      by_contra hh
      have hbI : b∈Icc r s := ⟨by linarith [hb.1],le_of_not_gt hh⟩
      exact not_lt_of_ge (hright b hbI) hbc
    refine ⟨a,b,har,hsb,?_,haN,hbM,Or.inr ⟨hright,hac,hbc⟩⟩
    linarith [ha.1,hb.2]

#print axioms normalized_one_sided_bigon_has_actual_far_side_endpoints
