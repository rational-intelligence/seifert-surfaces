import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCoherentEventFamilyChart
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSameChartTarget
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFamilySupportOrbit
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualGridOrbitInteraction
import CurveComplexGenusTwo.Topology.ActualFareyClassification.FiniteQuotientOrbitErase
import CurveComplexGenusTwo.Topology.TorusStrip.PeriodicChartCrosscutIsotopy

open Set Topology Schoenflies CurveComplex

theorem normalized_actual_transverse_has_genuine_periodic_event_erase
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hcount : 1<{t : ℝ | G t 0=c}.ncard)
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
    ∃ r s : ℝ, r<s ∧
    ∃ H : AmbientIsotopy Plane,
      (∀ t (i : ℤ×ℤ) z, H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      {t : ℝ | ∃ i : ℤ, H.finalMap (G t) 0=c+(i:ℝ)*T}=
        {t : ℝ | ∃ i : ℤ, G t 0=c+(i:ℝ)*T}\G ⁻¹'
          (⋃ i : ℤ×ℤ, ({G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
            G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)) ∧
      {t : Ico r (r+T) | ∃ i : ℤ, H.finalMap (G t.val) 0=c+(i:ℝ)*T}.Finite ∧
      {t : Ico r (r+T) | ∃ i : ℤ, H.finalMap (G t.val) 0=c+(i:ℝ)*T}.ncard <
        {t : Ico r (r+T) | ∃ i : ℤ, G t.val 0=c+(i:ℝ)*T}.ncard := by
  obtain ⟨k,r,s,a,b,hrs,har,hsb,hba,hr,hs,_,_,hcontact,hside,hold,phi,hfamily,hAi,haModel,hbModel,hFi,hdeck⟩ :=
    normalized_actual_transverse_has_coherent_event_family_chart G hG T c hT hp hc hfinite hcount htrans
  have hGL : range G⊆⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)) := by
    rintro z ⟨t,rfl⟩
    refine mem_iUnion.mpr ⟨0,t,?_⟩
    ext i; fin_cases i <;> simp [Plane.mk]
  have htx := fun t ht => htrans (G t) k (hGL (mem_range_self _)) ht
  have hpgridK : ∀ i : ℤ, p 0+(i:ℝ)*T≠c+(k:ℝ)*T := by
    intro i hi
    apply hpgrid (i-k)
    push_cast
    linarith
  have holdK : (G '' Icc a b)∩{z : Plane | ∃ i : ℤ, z 0=(c+(k:ℝ)*T)+(i:ℝ)*T}={G r,G s} := by
    convert hold using 2
    ext z
    constructor
    · rintro ⟨i,hi⟩; refine ⟨k+i,?_⟩; push_cast; linarith
    · rintro ⟨i,hi⟩; refine ⟨i-k,?_⟩; push_cast; linarith
  obtain ⟨B,hB,hBi,hBG,hBM⟩ := actual_two_event_chart_has_grid_free_target G hG T (c+(k:ℝ)*T)
    r s a b hT hrs har hsb hba hp hc hr hs hcontact hside htx holdK phi hAi hFi p hpgridK hGM
  have hBGOriginal : ∀ z∈B, ∀ i : ℤ, z 0≠c+(i:ℝ)*T := by
    intro z hz i hi
    apply hBG z hz (i-k)
    push_cast
    linarith
  have hab : a<b := har.trans (hrs.trans hsb)
  have hA := continuous_injective_interval_isArcBetween G hG.injective hab
  obtain ⟨H,hHeq,hHmove,hHfix⟩ := periodic_chart_crosscut_isotopy T hT phi hdeck
    (G '' Icc a b) B (G a) (G b) hA hB haModel hbModel hAi hBi
  obtain ⟨_,hlocal⟩ := normalized_actual_family_disk_full_lattice_contact G T a b hp phi hfamily
  have havoid := plane_actual_grid_free_full_lattice_orbit T c B hBGOriginal
  have holdOrbit := plane_actual_grid_contacts_full_lattice_orbit T c (G '' Icc a b) {G r,G s} hold
  have htwoImage (i : ℤ×ℤ) :
      (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' ({G r,G s} : Set Plane)=
      {G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} := by simp
  simp_rw [htwoImage] at holdOrbit
  have hcorners : ({G r,G s} : Set Plane)⊆phi '' Plane.openSquare 0 1 := by
    intro z hz
    rcases hz with hz|hz
    · subst z
      apply hAi
      refine ⟨⟨r,⟨har.le,hrs.le.trans hsb.le⟩,rfl⟩,?_⟩
      intro hh
      rcases hh with hh|hh
      · have h := hG.injective hh; linarith
      · have h := hG.injective (show G r=G b from hh); linarith
    · have hz' : z=G s := hz
      subst z
      apply hAi
      refine ⟨⟨s,⟨har.le.trans hrs.le,hsb.le⟩,rfl⟩,?_⟩
      intro hh
      rcases hh with hh|hh
      · have h := hG.injective hh; linarith
      · have h := hG.injective (show G s=G b from hh); linarith
  have hsupported : (⋃ i : ℤ×ℤ, ({G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
      G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane))⊆
      ⋃ i : ℤ×ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (phi '' Plane.openSquare 0 1) := by
    apply iUnion_mono
    intro i
    rw [←htwoImage]
    exact image_mono hcorners
  have herase := crossing_parameters_of_periodic_supported_crosscut_replacement G T hT phi H
    (G '' Icc a b) B {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T} (G r) (G s)
    hlocal hHmove hHfix havoid holdOrbit hsupported
  let gamma : Ico r (r+T)→Plane := fun t => G t.val
  have hγlocal : range gamma∩(⋃ i : ℤ×ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
      (phi '' Plane.openSquare 0 1))⊆⋃ i : ℤ×ℤ,
      (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (G '' Icc a b) := by
    rintro z ⟨⟨t,rfl⟩,hz⟩
    exact hlocal ⟨mem_range_self _,hz⟩
  have hfin := normalized_line_full_grid_contacts_finite_in_compact G T c hT hp hfinite
    (G '' Icc r (r+T)) (isCompact_Icc.image G.continuous)
  have hγinj : Function.Injective gamma := fun x y he => Subtype.ext (hG.injective he)
  have hγfinite : {t | ∃ i : ℤ, gamma t 0=c+(i:ℝ)*T}.Finite := by
    apply (hfin.preimage hγinj.injOn).subset
    intro t ht
    refine ⟨⟨hGL (mem_range_self _),ht⟩,t.val,⟨t.property.1,t.property.2.le⟩,rfl⟩
  let tr : Ico r (r+T) := ⟨r,⟨le_rfl,by linarith⟩⟩
  obtain ⟨hnew,hdecrease,_⟩ := finite_quotient_crossing_count_after_actual_supported_periodic_move gamma T hT phi H
    (G '' Icc a b) B {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T} (G r) (G s)
    hγlocal hHmove hHfix havoid holdOrbit hsupported hγfinite tr rfl ⟨k,hr⟩
  exact ⟨r,s,hrs,H,hHeq,herase,hnew,hdecrease⟩

#print axioms normalized_actual_transverse_has_genuine_periodic_event_erase
