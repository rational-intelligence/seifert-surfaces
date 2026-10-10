import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFarSideEndpoints
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualAcrossFiberTarget

open Set Topology Schoenflies Metric

/-- A clean actual straight side has a convex operation neighborhood avoiding
all puncture lifts, derived from actual compact separation, not supplied. -/
theorem clean_fiber_has_convex_mark_free_neighborhood
    (G : C(ℝ,Plane)) (_hG : IsClosedEmbedding G) (T r s c : ℝ) (hT : 0<T)
    (hr : G r 0=c) (hs : G s 0=c)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hcontact : segment ℝ (G r) (G s) ∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))={G r,G s})
    (p : Plane) (hpgrid : ∀ i : ℤ, p 0+(i:ℝ)*T≠c)
    (W : Set Plane) (hW : IsOpen W) (hFW : segment ℝ (G r) (G s)⊆W) :
    ∃ N V : Set Plane, IsOpen N ∧ Convex ℝ N ∧
      segment ℝ (G r) (G s)⊆N ∧ N⊆W ∧ N⊆V ∧ IsCompact V ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint V
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' V)) ∧
      (∀ z∈N, c-T<z 0 ∧ z 0<c+T) ∧
      Disjoint N (⋃ i : ℤ×ℤ, ({p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)) := by
  let F := segment ℝ (G r) (G s)
  let M := ⋃ i : ℤ×ℤ, ({p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)
  have hF : IsCompact F := isCompact_segment _ _
  have hcoord (z : Plane) (hz : z∈F) : z 0=c := by
    change z∈segment ℝ (G r) (G s) at hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨u,hu,rfl⟩ := hz
    simp only [AffineMap.lineMap_apply]
    change u*(G s 0-G r 0)+G r 0=c
    rw [hr,hs]
    ring
  have hheight := clean_fiber_side_has_short_height G T r s c hT hr hs hc hcontact
  have hcoords (z : Plane) (hz : z 0=c) : z=Plane.mk c (z 1) := by
    ext i
    fin_cases i <;> simp [hz]
  have hbox (z : Plane) (hz : z∈F) : c ≤ z 0 ∧ z 0 ≤ c+0 ∧
      min (G r 1) (G s 1) ≤ z 1 ∧ z 1 ≤ min (G r 1) (G s 1)+|G s 1-G r 1| := by
    have hz0 := hcoord z hz
    refine ⟨hz0.ge,by rw [hz0]; simp,?_,?_⟩
    change z∈segment ℝ (G r) (G s) at hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨u,hu,rfl⟩ := hz
    simp only [AffineMap.lineMap_apply]
    change min (G r 1) (G s 1) ≤ u*(G s 1-G r 1)+G r 1
    rcases le_total (G r 1) (G s 1) with hle|hle
    · rw [min_eq_left hle]; nlinarith [hu.1,hu.2]
    · rw [min_eq_right hle]; nlinarith [hu.1,hu.2]
    change z∈segment ℝ (G r) (G s) at hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨u,hu,rfl⟩ := hz
    simp only [AffineMap.lineMap_apply]
    change u*(G s 1-G r 1)+G r 1 ≤ min (G r 1) (G s 1)+|G s 1-G r 1|
    rcases le_total (G r 1) (G s 1) with hle|hle
    · rw [min_eq_left hle,abs_of_nonneg (sub_nonneg.mpr hle)]; nlinarith [hu.1,hu.2]
    · rw [min_eq_right hle,abs_of_nonpos (sub_nonpos.mpr hle)]; nlinarith [hu.1,hu.2]
  have hdeck := plane_narrow_box_lattice_disjoint F T c (min (G r 1) (G s 1)) 0
    |G s 1-G r 1| hT hT hheight hbox
  have hM : IsClosed M := by
    have hlf := CurveComplex.ActualFareyClassification.compact_lattice_translates_locally_finite {p} (isCompact_singleton) T hT
    have hh := hlf.isClosed_iUnion (fun i => (isCompact_singleton.image (Homeomorph.addRight _).continuous).isClosed)
    simpa only [image_singleton] using hh
  have hFM : Disjoint F M := by
    apply disjoint_left.mpr
    intro z hz hzM
    obtain ⟨i,hi⟩ := mem_iUnion.mp hzM
    have he : z=p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T) := mem_singleton_iff.mp hi
    have h0 := congrArg (fun w : Plane => w 0) he
    change z 0=p 0+(i.1:ℝ)*T at h0
    exact hpgrid i.1 (h0.symm.trans (hcoord z hz))
  obtain ⟨U,V,hU,hFU,hUV,hV,hVM,hVD⟩ := compact_deck_free_marked_uniform_support F M hF hM hFM T hT hdeck
  obtain ⟨ρ,hρ,hρU⟩ := hF.exists_cthickening_subset_open (hU.inter hW) (fun z hz => ⟨hFU hz,hFW hz⟩)
  let S : Set Plane := (EuclideanSpace.proj 0) ⁻¹' Ioo (c-T) (c+T)
  let N := thickening ρ F ∩ S
  have hS : IsOpen S := isOpen_Ioo.preimage (EuclideanSpace.proj 0).continuous
  have hNc : Convex ℝ N :=
    ((convex_segment (G r) (G s)).thickening ρ).inter
      ((convex_Ioo (c-T) (c+T)).is_linear_preimage (EuclideanSpace.proj 0).isLinear)
  have hFN : F⊆N := by
    intro z hz
    refine ⟨self_subset_thickening hρ F hz,?_⟩
    change c-T<z 0 ∧ z 0<c+T
    rw [hcoord z hz]
    constructor <;> linarith
  have hNU : N⊆U := fun z hz => (hρU ((thickening_subset_cthickening ρ F) hz.1)).1
  have hNV : N⊆V := hNU.trans (subset_closure.trans hUV)
  refine ⟨N,V,isOpen_thickening.inter hS,hNc,hFN,?_,hNV,hV,hVD,?_,hVM.mono_left hNV⟩
  · exact fun z hz => (hρU ((thickening_subset_cthickening ρ F) hz.1)).2
  · exact fun z hz => hz.2

#print axioms clean_fiber_has_convex_mark_free_neighborhood

/-- The full target has the ACTUAL enlarged original endpoints. Convexity
joins the source-selected far-side endpoints without any connector premise. -/
theorem clean_transverse_bigon_has_actual_full_marked_far_side_target
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s c : ℝ) (hT : 0<T)
    (hrs : r<s) (hshort : s-r<T)
    (hp : ∀ (k : ℤ) (u : ℝ), G (u+(k:ℝ)*T)=G u+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hr : G r 0=c) (hs : G s 0=c)
    (hcontact : segment ℝ (G r) (G s) ∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))={G r,G s})
    (hside : (∀ t∈Icc r s, G t 0 ≤ c) ∨ (∀ t∈Icc r s, c ≤ G t 0))
    (htrans : ∀ t, G t 0=c →
      ∃ (U : Set Plane) (W : Set (ℝ×ℝ)) (htU : G t∈U) (h : U ≃ₜ W),
      IsOpen U ∧ IsOpen W ∧ ((h ⟨G t,htU⟩ : W) : ℝ×ℝ)=(0,0) ∧
      (∀ z (hz : z∈U),
        (z 0=c ↔ ((h ⟨z,hz⟩ : W) : ℝ×ℝ).1=0) ∧
        (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
          ((h ⟨z,hz⟩ : W) : ℝ×ℝ).2=0)))
    (p : Plane) (hpgrid : ∀ i : ℤ, p 0+(i:ℝ)*T≠c)
    (W : Set Plane) (hW : IsOpen W) (hFW : segment ℝ (G r) (G s)⊆W) :
    ∃ a b : ℝ, a<r ∧ s<b ∧ b-a<T ∧
      IsArcBetween (segment ℝ (G a) (G b)) (G a) (G b) ∧
      segment ℝ (G a) (G b)⊆W ∧
      Disjoint (G '' Icc r s) (segment ℝ (G a) (G b)) ∧
      (∀ z∈segment ℝ (G a) (G b), ∀ i : ℤ, z 0≠c+(i:ℝ)*T) ∧
      Disjoint (segment ℝ (G a) (G b))
        (⋃ i : ℤ×ℤ, ({p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)) ∧
      ∃ V : Set Plane, IsCompact V ∧ segment ℝ (G a) (G b)⊆V ∧
        (∀ i : ℤ×ℤ, i≠0 → Disjoint V
          ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' V)) := by
  obtain ⟨N,V,hN,hconv,hFN,hNW,hNV,hV,hVD,hcoord,hNM⟩ :=
    clean_fiber_has_convex_mark_free_neighborhood G hG T r s c hT hr hs hc hcontact p hpgrid W hW hFW
  obtain ⟨a,b,har,hsb,hba,haN,hbN,hfar⟩ :=
    normalized_one_sided_bigon_has_actual_far_side_endpoints G hG T r s c hT hrs hshort
      hp hc hr hs hside htrans N N hN hN
      (hFN (left_mem_segment ℝ _ _)) (hFN (right_mem_segment ℝ _ _))
  have hBN : segment ℝ (G a) (G b)⊆N := hconv.segment_subset haN hbN
  have hne : G a≠G b := by
    intro hh
    have hab := hG.injective hh
    linarith
  have hsign : (∀ z∈segment ℝ (G a) (G b), c<z 0) ∨
      (∀ z∈segment ℝ (G a) (G b), z 0<c) := by
    rcases hfar with ⟨_,ha,hb⟩|⟨_,ha,hb⟩
    · left
      exact ((convex_Ioi c).is_linear_preimage (EuclideanSpace.proj 0).isLinear).segment_subset ha hb
    · right
      exact ((convex_Iio c).is_linear_preimage (EuclideanSpace.proj 0).isLinear).segment_subset ha hb
  have hcoreB : Disjoint (G '' Icc r s) (segment ℝ (G a) (G b)) := by
    apply disjoint_left.mpr
    rintro z ⟨t,ht,rfl⟩ hzB
    rcases hfar with ⟨hleft,ha,hb⟩|⟨hright,ha,hb⟩
    · have hzside := ((convex_Ioi c).is_linear_preimage (EuclideanSpace.proj 0).isLinear).segment_subset ha hb hzB
      exact not_lt_of_ge (hleft t ht) hzside
    · have hzside := ((convex_Iio c).is_linear_preimage (EuclideanSpace.proj 0).isLinear).segment_subset ha hb hzB
      exact not_lt_of_ge (hright t ht) hzside
  refine ⟨a,b,har,hsb,hba,isArcBetween_segment hne,hBN.trans hNW,hcoreB,?_,hNM.mono_left hBN,V,hV,
    hBN.trans hNV,hVD⟩
  intro z hz i he
  obtain ⟨hlo,hhi⟩ := hcoord z (hBN hz)
  have hi : i ≤ -1 ∨ i=0 ∨ 1 ≤ i := by omega
  rcases hi with hi|(hi|hi)
  · have hi' : (i:ℝ) ≤ -1 := by exact_mod_cast hi
    rw [he] at hlo
    nlinarith
  · subst i
    simp only [Int.cast_zero,zero_mul,add_zero] at he
    rcases hsign with hsign|hsign
    · exact (ne_of_gt (hsign z hz)) he
    · exact (ne_of_lt (hsign z hz)) he
  · have hi' : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
    rw [he] at hhi
    nlinarith

#print axioms clean_transverse_bigon_has_actual_full_marked_far_side_target
