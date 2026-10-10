import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualClosedBigonProducer

open Set Topology Schoenflies Metric

/-- A compact clean actual fiber side has concrete parallel target arcs on
BOTH sides of the supporting fiber, avoiding all grid fibers and all lifts of
one puncture. The puncture is only assumed to avoid the reference grid itself;
no target-arc or support separation certificate is supplied. -/
theorem clean_actual_fiber_has_marked_parallel_target_arcs
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s c : ℝ) (hT : 0<T)
    (hrs : r<s) (hr : G r 0=c) (hs : G s 0=c)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hcontact : segment ℝ (G r) (G s) ∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))={G r,G s})
    (p : Plane) (hpgrid : ∀ i : ℤ, p 0+(i:ℝ)*T≠c) :
    ∃ e : ℝ, 0<e ∧ e<T ∧
      ∃ V : Set Plane, IsCompact V ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint V
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' V)) ∧
      ∀ σ : ℝ, σ=-1 ∨ σ=1 →
        let B := (fun z : Plane => z+Plane.mk (σ*e) 0) '' segment ℝ (G r) (G s)
        IsArcBetween B (G r+Plane.mk (σ*e) 0) (G s+Plane.mk (σ*e) 0) ∧ B⊆V ∧
        (∀ z∈B, z 0=c+σ*e) ∧
        (∀ z∈B, ∀ i : ℤ, z 0≠c+(i:ℝ)*T) ∧
        Disjoint B (⋃ i : ℤ×ℤ, ({p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)) := by
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
  obtain ⟨ρ,hρ,hρU⟩ := hF.exists_cthickening_subset_open hU hFU
  have hncont : Continuous (fun e : ℝ => ‖Plane.mk e 0‖) := by
    apply Continuous.norm
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  have hz0 : Plane.mk (0:ℝ) 0=0 := by ext i; fin_cases i <;> rfl
  have hopen : IsOpen {e : ℝ | ‖Plane.mk e 0‖<ρ} := isOpen_Iio.preimage hncont
  have hzero : (0:ℝ)∈{e : ℝ | ‖Plane.mk e 0‖<ρ} := by simp only [mem_ofPred_eq,hz0,norm_zero]; exact hρ
  obtain ⟨η,hη,hηN⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let e := min η T/2
  have he : 0<e := half_pos (lt_min hη hT)
  have heη : e<η := by dsimp [e]; linarith [min_le_left η T]
  have heT : e<T := by dsimp [e]; linarith [min_le_right η T]
  have hnorm : ‖Plane.mk e 0‖<ρ := by
    apply hηN
    rw [mem_ball,Real.dist_eq,sub_zero,abs_of_pos he]
    exact heη
  have hnormNeg : ‖Plane.mk (-e) 0‖<ρ := by
    have hh : Plane.mk (-e) 0= -Plane.mk e 0 := by ext i; fin_cases i <;> simp [Plane.mk]
    rw [hh,norm_neg]
    exact hnorm
  refine ⟨e,he,heT,V,hV,hVD,?_⟩
  intro σ hσ
  dsimp only
  let d := Plane.mk (σ*e) 0
  have hd : ‖d‖<ρ := by
    rcases hσ with rfl|rfl
    · simpa only [d,neg_one_mul] using hnormNeg
    · simpa only [d,one_mul] using hnorm
  have hBV : (fun z : Plane => z+d) '' F⊆V := by
    rintro z ⟨w,hw,rfl⟩
    apply hUV
    apply subset_closure
    apply hρU
    apply thickening_subset_cthickening
    apply mem_thickening_iff.mpr
    refine ⟨w,hw,?_⟩
    change dist (w+d) w<ρ
    rw [dist_eq_norm,add_sub_cancel_left]
    exact hd
  have hne : G r≠G s := fun hh => (ne_of_lt hrs) (hG.injective hh)
  have harc := (isArcBetween_segment hne).image_of_injOn (subset_univ _)
    (Homeomorph.addRight d).continuous.continuousOn (Homeomorph.addRight d).injective.injOn
  refine ⟨harc,hBV,?_,?_,hVM.mono_left hBV⟩
  · rintro z ⟨w,hw,rfl⟩
    change w 0+σ*e=c+σ*e
    rw [hcoord w hw]
  · rintro z ⟨w,hw,rfl⟩ i hh
    change w 0+σ*e=c+(i:ℝ)*T at hh
    rw [hcoord w hw] at hh
    have hi : i ≤ 0 ∨ 1 ≤ i := by omega
    rcases hσ with hσ|hσ <;> rw [hσ] at hh
    · rcases hi with hi|hi
      · have hi' : (i:ℝ) ≤ 0 := by exact_mod_cast hi
        by_cases hi0 : i=0
        · rw [hi0] at hh
          simp only [Int.cast_zero,zero_mul,neg_one_mul] at hh
          linarith
        · have hi' : (i:ℝ) ≤ -1 := by exact_mod_cast (show i ≤ -1 by omega)
          nlinarith
      · have hi' : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
        nlinarith
    · rcases hi with hi|hi
      · have hi' : (i:ℝ) ≤ 0 := by exact_mod_cast hi
        nlinarith
      · have hi' : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
        nlinarith

#print axioms clean_actual_fiber_has_marked_parallel_target_arcs
