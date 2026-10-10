import CurveComplexGenusTwo.Topology.TorusStrip.NormalizedDeckFamily
import Mathlib

open Set Topology Schoenflies Metric Bornology
open scoped Topology

theorem CurveComplex.ActualFareyClassification.compact_lattice_translates_locally_finite (K : Set Plane) (hK : IsCompact K) (T : ℝ) (hT : 0 < T) :
    LocallyFinite (fun n : ℤ × ℤ => (fun z : Plane => z+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)) '' K) := by
  have lattice (K : Set (ℝ × ℝ)) (hK : IsCompact K) (T : ℝ) (hT : 0 < T) :
    LocallyFinite (fun i : ℤ × ℤ =>
      (fun z : ℝ × ℝ => z + ((i.1 : ℝ) * T, (i.2 : ℝ) * T)) '' K) := by
  
    obtain ⟨M₀, hM₀⟩ := (hK.image (continuous_abs.comp continuous_fst)).bddAbove
    obtain ⟨M₁, hM₁⟩ := (hK.image (continuous_abs.comp continuous_snd)).bddAbove
    let M : ℝ := max (max M₀ M₁) 0
    have hb₀ (z : ℝ × ℝ) (hz : z ∈ K) : |z.1| ≤ M :=
      (hM₀ ⟨z, hz, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hb₁ (z : ℝ × ℝ) (hz : z ∈ K) : |z.2| ≤ M :=
      (hM₁ ⟨z, hz, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
    intro x
    let U : Set (ℝ × ℝ) :=
      (Prod.fst ⁻¹' Ioo (x.1 - 1) (x.1 + 1)) ∩
      (Prod.snd ⁻¹' Ioo (x.2 - 1) (x.2 + 1))
    have hU : U ∈ 𝓝 x := by
      apply ((isOpen_Ioo.preimage continuous_fst).inter
        (isOpen_Ioo.preimage continuous_snd)).mem_nhds
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    obtain ⟨N, hN⟩ := exists_nat_gt ((max |x.1| |x.2| + M + 1) / T)
    have hNT := (div_lt_iff₀ hT).mp hN
    refine ⟨U, hU, (Set.finite_Icc (-(N : ℤ), -(N : ℤ)) ((N : ℤ), (N : ℤ))).subset ?_⟩
    intro i hi
    obtain ⟨w, ⟨z, hz, rfl⟩, hw⟩ := hi
    have hz₀ := abs_le.mp (hb₀ z hz)
    have hz₁ := abs_le.mp (hb₁ z hz)
    have hw₀ : x.1 - 1 < z.1 + (i.1 : ℝ) * T ∧
        z.1 + (i.1 : ℝ) * T < x.1 + 1 := hw.1
    have hw₁ : x.2 - 1 < z.2 + (i.2 : ℝ) * T ∧
        z.2 + (i.2 : ℝ) * T < x.2 + 1 := hw.2
    have hi₀lo : -(N : ℝ) < (i.1 : ℝ) := by
      nlinarith [neg_abs_le x.1, le_max_left |x.1| |x.2|]
    have hi₀hi : (i.1 : ℝ) < (N : ℝ) := by
      nlinarith [le_abs_self x.1, le_max_left |x.1| |x.2|]
    have hi₁lo : -(N : ℝ) < (i.2 : ℝ) := by
      nlinarith [neg_abs_le x.2, le_max_right |x.1| |x.2|]
    have hi₁hi : (i.2 : ℝ) < (N : ℝ) := by
      nlinarith [le_abs_self x.2, le_max_right |x.1| |x.2|]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact_mod_cast hi₀lo.le
    · exact_mod_cast hi₁lo.le
    · exact_mod_cast hi₀hi.le
    · exact_mod_cast hi₁hi.le
  let e : Plane ≃ₜ (ℝ × ℝ) := {
    toFun := fun z => (z 0,z 1)
    invFun := fun z => Plane.mk z.1 z.2
    left_inv := by intro z; ext i; fin_cases i <;> simp
    right_inv := by intro z; cases z; simp
    continuous_toFun := by fun_prop
    continuous_invFun := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop }
  have hf := lattice (e '' K) (hK.image e.continuous) T hT
  have hfp := hf.preimage_continuous e.continuous
  apply hfp.subset
  intro n
  rintro z ⟨w,hw,rfl⟩
  refine ⟨e w,mem_image_of_mem e hw,?_⟩
  simp [e,Plane.mk]

/-- A compact deck-free actual set has an enlarged compact deck-free support
avoiding any closed forbidden set it already avoids. The uniform radius is
constructed from the closed locally finite union of nonzero translates. -/
theorem compact_deck_free_marked_uniform_support
    (K M : Set Plane) (hK : IsCompact K) (hM : IsClosed M)
    (hKM : Disjoint K M) (T : ℝ) (hT : 0<T)
    (hdeck : ∀ i : ℤ × ℤ, i≠0 → Disjoint K
      ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' K)) :
    ∃ U V : Set Plane, IsOpen U ∧ K⊆U ∧ closure U⊆V ∧ IsCompact V ∧
      Disjoint V M ∧
      ∀ i : ℤ × ℤ, i≠0 → Disjoint V
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' V) := by
  let tau := fun i : ℤ × ℤ => fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
  let Q := ⋃ i : {i : ℤ × ℤ // i≠0}, tau i.val '' K
  have hlf := CurveComplex.ActualFareyClassification.compact_lattice_translates_locally_finite K hK T hT
  have hQ : IsClosed Q :=
    (hlf.comp_injective Subtype.val_injective).isClosed_iUnion
      (fun i => (hK.image (Homeomorph.addRight _).continuous).isClosed)
  have hKavoid : K⊆(Q∪M)ᶜ := by
    intro z hz hh
    rcases hh with hh | hh
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hh
      exact disjoint_left.mp (hdeck i.val i.property) hz hi
    · exact disjoint_left.mp hKM hz hh
  obtain ⟨rho,hrho,hsub⟩ := hK.exists_cthickening_subset_open
    (hQ.union hM).isOpen_compl hKavoid
  let e := rho/5
  have he : 0<e := by dsimp [e]; positivity
  let U := thickening e K
  let V := cthickening e K
  have hVM : Disjoint V M := by
    apply disjoint_left.mpr
    intro z hz hzM
    exact hsub ((cthickening_mono (show e≤rho by dsimp [e]; linarith) K) hz) (Or.inr hzM)
  refine ⟨U,V,isOpen_thickening,self_subset_thickening he K,
    closure_thickening_subset_cthickening e K,hK.cthickening,hVM,?_⟩
  intro i hi
  apply disjoint_left.mpr
  rintro z hz ⟨v,hv,hvz⟩
  obtain ⟨p,hp,hzp⟩ := mem_thickening_iff.mp
    ((cthickening_subset_thickening' (show 0<2*e by positivity) (by linarith) K) hz)
  obtain ⟨q,hq,hvq⟩ := mem_thickening_iff.mp
    ((cthickening_subset_thickening' (show 0<2*e by positivity) (by linarith) K) hv)
  let d := Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
  have hzq : dist z (q+d)<2*e := by
    change v+d=z at hvz
    rw [← hvz,dist_add_right]
    exact hvq
  have hqp : dist (q+d) p<rho := by
    have hh := dist_triangle (q+d) z p
    rw [dist_comm (q+d) z] at hh
    dsimp [e] at *
    linarith
  have hthick : q+d∈cthickening rho K :=
    thickening_subset_cthickening rho K (mem_thickening_iff.mpr ⟨p,hp,hqp⟩)
  apply hsub hthick
  left
  exact mem_iUnion.mpr ⟨⟨i,hi⟩,q,hq,rfl⟩

/-- Compact deck-freeness of a short normalized actual lifted arc is derived
from the period and collision identities, without a separation certificate. -/
theorem normalized_plane_short_arc_deck_free
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s : ℝ) (hT : 0<T)
    (hshort : s-r<T)
    (hp : ∀ (k : ℤ) (t : ℝ), G (t+(k:ℝ)*T)=G t+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ),
      G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0) :
    ∀ i : ℤ × ℤ, i≠0 → Disjoint (G '' Icc r s)
      ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (G '' Icc r s)) := by
  intro i hi
  apply disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨_,⟨y,hy,rfl⟩,he⟩
  have hb := hc x y i.1 i.2 he.symm
  have hxy : x=y+(i.1:ℝ)*T := by
    apply hG.injective
    rw [hp]
    simpa only [hb,Int.cast_zero,zero_mul] using he.symm
  have ha : i.1≠0 := by
    intro hh
    exact hi (Prod.ext hh hb)
  have habs : (1:ℝ)≤|(i.1:ℝ)| := by exact_mod_cast Int.one_le_abs ha
  have hlt : |(i.1:ℝ)*T|<T := by
    rw [abs_lt]
    constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
  rw [abs_mul,abs_of_pos hT] at hlt
  nlinarith [mul_le_mul_of_nonneg_right habs hT.le]

/-- Actual normalized short-arc source data produces a compact enlarged
support, uniformly deck-free and mark-free. Neither property is assumed of
a preselected operation disk. -/
theorem normalized_short_arc_has_marked_uniform_support
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s : ℝ) (hT : 0<T)
    (hshort : s-r<T)
    (hp : ∀ (k : ℤ) (t : ℝ), G (t+(k:ℝ)*T)=G t+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ),
      G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (M : Set Plane) (hM : IsClosed M) (hGM : Disjoint (range G) M) :
    ∃ U V : Set Plane, IsOpen U ∧ G '' Icc r s⊆U ∧ closure U⊆V ∧ IsCompact V ∧
      Disjoint V M ∧
      ∀ i : ℤ × ℤ, i≠0 → Disjoint V
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' V) := by
  exact compact_deck_free_marked_uniform_support _ M (isCompact_Icc.image G.continuous) hM
    (hGM.mono_left (image_subset_range G _)) T hT
    (normalized_plane_short_arc_deck_free G hG T r s hT hshort hp hc)

#print axioms CurveComplex.ActualFareyClassification.compact_lattice_translates_locally_finite
#print axioms compact_deck_free_marked_uniform_support
#print axioms normalized_plane_short_arc_deck_free
#print axioms normalized_short_arc_has_marked_uniform_support
