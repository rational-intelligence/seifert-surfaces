import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFullFarSideTarget
import CurveComplexGenusTwo.Topology.TopologicalArcJoin

open Set Topology Schoenflies CurveComplex

/-- The actual marked target and both source connectors are constructed inside
one prescribed operation chart. Loop erasure retains support and grid avoidance. -/
theorem actual_two_event_chart_has_grid_free_target
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c r s a b : ℝ) (hT : 0<T)
    (hrs : r<s) (har : a<r) (hsb : s<b) (hshort : b-a<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (i j : ℤ), G x=G y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0)
    (hr : G r 0=c) (hs : G s 0=c)
    (hcontact : segment ℝ (G r) (G s)∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))={G r,G s})
    (hside : (∀ t∈Icc r s, G t 0 ≤ c) ∨ (∀ t∈Icc r s, c ≤ G t 0))
    (htrans : ∀ t, G t 0=c →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (htU : G t∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨G t,htU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 0=c ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
    (hold : (G '' Icc a b)∩{z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}={G r,G s})
    (phi : Plane ≃ₜ Plane)
    (hAi : (G '' Icc a b)\{G a,G b}⊆phi '' Plane.openSquare 0 1)
    (hFi : segment ℝ (G r) (G s)⊆phi '' Plane.openSquare 0 1)
    (p : Plane) (hpgrid : ∀ i : ℤ, p 0+(i:ℝ)*T≠c)
    (hGM : Disjoint (range G)
      (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)})) :
    ∃ B : Set Plane, IsArcBetween B (G a) (G b) ∧
      B\{G a,G b}⊆phi '' Plane.openSquare 0 1 ∧
      (∀ z∈B, ∀ i : ℤ, z 0≠c+(i:ℝ)*T) ∧
      Disjoint B (⋃ i : ℤ×ℤ, {p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)}) := by
  let W := (phi '' Plane.openSquare 0 1)∩(G '' (Ioo a b)ᶜ)ᶜ
  have hW : IsOpen W := (phi.isOpenMap _ (Plane.isOpen_openSquare 0 1)).inter
    (hG.isClosedMap _ isOpen_Ioo.isClosed_compl).isOpen_compl
  have hGL : range G⊆⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)) := by
    rintro z ⟨t,rfl⟩
    refine mem_iUnion.mpr ⟨0,t,?_⟩
    ext i; fin_cases i <;> simp [Plane.mk]
  have hFW : segment ℝ (G r) (G s)⊆W := by
    intro z hz
    refine ⟨hFi hz,?_⟩
    rintro ⟨t,ht,he⟩
    have hh : z∈({G r,G s} : Set Plane) := hcontact ▸ ⟨hz,hGL ⟨t,he⟩⟩
    rcases hh with hh|hh
    · have htr := hG.injective (he.trans hh)
      subst t; exact ht ⟨har,lt_trans hrs hsb⟩
    · have hts := hG.injective (he.trans (show z=G s from hh))
      subst t; exact ht ⟨lt_trans har hrs,hsb⟩
  have hcoreShort : s-r<T := by linarith
  obtain ⟨u,v,hur,hsv,_,hMid,hMidW,_,hMidGrid,hMidM,_⟩ :=
    clean_transverse_bigon_has_actual_full_marked_far_side_target G hG T r s c hT hrs hcoreShort hp hc
      hr hs hcontact hside htrans p hpgrid W hW hFW
  have hu : u∈Ioo a b := by
    by_contra hn
    exact (hMidW (left_mem_segment ℝ _ _)).2 ⟨u,hn,rfl⟩
  have hv : v∈Ioo a b := by
    by_contra hn
    exact (hMidW (right_mem_segment ℝ _ _)).2 ⟨v,hn,rfl⟩
  have hLeft := continuous_injective_interval_isArcBetween G hG.injective hu.1
  have hRight := continuous_injective_interval_isArcBetween G hG.injective hv.2
  have hav : G a≠G v := fun hh => (ne_of_lt hv.1) (hG.injective hh)
  obtain ⟨C,hCsub,hC⟩ := exists_arc_in_union_of_arcs hLeft hMid hav
  have hab : G a≠G b := fun hh => (ne_of_lt (lt_trans har (lt_trans hrs hsb))) (hG.injective hh)
  obtain ⟨B,hBsub,hB⟩ := exists_arc_in_union_of_arcs hC hRight hab
  have hBwhole : B⊆(G '' Icc a u∪segment ℝ (G u) (G v))∪G '' Icc v b :=
    hBsub.trans (union_subset_union hCsub subset_rfl)
  have hConnect (l d : ℝ) (hld : Icc l d⊆Icc a b)
      (hgap : ∀ t∈Icc l d, t≠r ∧ t≠s) :
      ∀ z∈G '' Icc l d, ∀ i : ℤ, z 0≠c+(i:ℝ)*T := by
    rintro z ⟨t,ht,rfl⟩ i he
    have hh : G t∈({G r,G s} : Set Plane) := hold ▸ ⟨⟨t,hld ht,rfl⟩,i,he⟩
    rcases hh with hh|hh
    · exact (hgap t ht).1 (hG.injective hh)
    · exact (hgap t ht).2 (hG.injective (show G t=G s from hh))
  have hLGrid := hConnect a u (Icc_subset_Icc le_rfl hu.2.le) (by
    intro t ht; constructor <;> intro he <;> subst t <;> linarith [ht.2])
  have hRGrid := hConnect v b (Icc_subset_Icc hv.1.le le_rfl) (by
    intro t ht; constructor <;> intro he <;> subst t <;> linarith [ht.1])
  refine ⟨B,hB,?_,?_,?_⟩
  · rintro z ⟨hz,hne⟩
    rcases hBwhole hz with (hz|hz)|hz
    · exact hAi ⟨image_mono (Icc_subset_Icc le_rfl hu.2.le) hz,hne⟩
    · exact (hMidW hz).1
    · exact hAi ⟨image_mono (Icc_subset_Icc hv.1.le le_rfl) hz,hne⟩
  · intro z hz i
    rcases hBwhole hz with (hz|hz)|hz
    · exact hLGrid z hz i
    · exact hMidGrid z hz i
    · exact hRGrid z hz i
  · apply disjoint_left.mpr
    intro z hz hzM
    rcases hBwhole hz with (hz|hz)|hz
    · exact disjoint_left.mp hGM (image_subset_range G _ hz) hzM
    · exact disjoint_left.mp hMidM hz hzM
    · exact disjoint_left.mp hGM (image_subset_range G _ hz) hzM

#print axioms actual_two_event_chart_has_grid_free_target
