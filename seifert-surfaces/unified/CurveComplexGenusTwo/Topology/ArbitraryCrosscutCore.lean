/-
The proof of `crosscut_at_most_two_of_collars` adapts the unused-polygonality
argument from Schoenflies/CrosscutAtMostTwo.lean.
Copyright (c) 2026 Álvaro Begué. Released under Apache 2.0.
-/
import Schoenflies.CrosscutAtMostTwo

open Metric Set unitInterval

namespace Schoenflies

/- The polygonality argument of `crosscut_at_most_two` is unused.  This version
   records the exact generality of its connectedness argument. -/
theorem crosscut_at_most_two_of_collars {D P : Set Plane} {a b : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (hcollars : HasArcCollars D P) :
    ∃ zL ∈ D \ P, ∃ zR ∈ D \ P, ∀ x ∈ D \ P,
      x ∈ connectedComponentIn (D \ P) zL ∨ x ∈ connectedComponentIn (D \ P) zR := by
  have hPclosed : IsClosed P := hP.isArc.isClosed
  obtain ⟨f, hc, hi, himg, h0, h1⟩ := hP
  have hDPeq : D ∩ P = f '' Ioo 0 1 := by
    have hdiff : P \ {a, b} = f '' Ioo 0 1 := by
      rw [← himg, ← h0, ← h1, ← openArc_eq_diff hi]
      rfl
    rw [← hdiff]
    ext y
    simp only [mem_inter_iff, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun ⟨hyD, hyP⟩ => ⟨hyP, ?_⟩, fun ⟨hyP, hy⟩ => ⟨hPD ⟨hyP, by simpa using hy⟩, hyP⟩⟩
    rintro (rfl | rfl)
    exacts [ha hyD, hb hyD]
  have hsubarc : ∀ s t : ℝ, 0 < s → s < t → t < 1 → Nonempty (ArcCollar D P (f '' Icc s t)) := by
    intro s t hs hst ht
    have hsubI : Icc s t ⊆ I := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hsubIoo : Icc s t ⊆ Ioo 0 1 := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hsI : s ∈ Icc s t := left_mem_Icc.2 hst.le
    have htI : t ∈ Icc s t := right_mem_Icc.2 hst.le
    refine hcollars _ (by rw [hDPeq]; exact image_mono hsubIoo)
      (isCompact_image_of_subset_I hc hsubI isClosed_Icc)
      (isPreconnected_Icc.image f (hc.mono hsubI))
      ⟨f s, mem_image_of_mem f hsI, f t, mem_image_of_mem f htI, fun h => ?_⟩
    exact absurd (hi (hsubI hsI) (hsubI htI) h) (ne_of_lt hst)
  obtain ⟨C₀⟩ := hsubarc (1 / 4) (3 / 4) (by norm_num) (by norm_num) (by norm_num)
  have hz₀ : f (1 / 2) ∈ f '' Icc (1 / 4 : ℝ) (3 / 4) :=
    mem_image_of_mem f ⟨by norm_num, by norm_num⟩
  refine ⟨C₀.ptL, C₀.ptL_mem_diff, C₀.ptR, C₀.ptR_mem_diff, fun x hx => ?_⟩
  refine covered_by_two_of_local hDopen hDconn hPclosed C₀.ptL_mem_diff (fun w hw => ?_) hx
  rw [hDPeq] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  obtain ⟨C⟩ := hsubarc (min u (1 / 4)) (max u (3 / 4))
    (lt_min hu.1 (by norm_num)) (by have := min_le_right u (1 / 4 : ℝ)
                                    have := le_max_right u (3 / 4 : ℝ)
                                    linarith)
    (max_lt hu.2 (by norm_num))
  refine ⟨C.nbhd, C.isOpen_nbhd,
    C.subset_nbhd (mem_image_of_mem f ⟨min_le_left _ _, le_max_left _ _⟩), C.nbhd_subset, ?_⟩
  exact C₀.nbhd_diff_subset_components C hz₀
    (mem_image_of_mem f ⟨le_trans (min_le_right _ _) (by norm_num),
      le_trans (by norm_num) (le_max_right _ _)⟩)

theorem crosscut_components_exhaust_of_collars {D P : Set Plane} {a b v₁ v₂ : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (hcollars : HasArcCollars D P)
    (h₁ : v₁ ∈ D \ P) (h₂ : v₂ ∈ D \ P)
    (hne : connectedComponentIn (D \ P) v₁ ≠ connectedComponentIn (D \ P) v₂) :
    ∀ x ∈ D \ P, x ∈ connectedComponentIn (D \ P) v₁ ∨ x ∈ connectedComponentIn (D \ P) v₂ := by
  obtain ⟨zL, -, zR, -, hcov⟩ :=
    crosscut_at_most_two_of_collars hDopen hDconn hP ha hb hPD hcollars
  exact covered_by_two_components_of_ne hcov h₁ h₂ hne

/-- A collar can be transported by an ambient homeomorphism, including its
connected tracks and their common limiting arc. -/
noncomputable def ArcCollar.image {D P K : Set Plane} (C : ArcCollar D P K)
    (F : Plane ≃ₜ Plane) : ArcCollar (F '' D) (F '' P) (F '' K) where
  nbhd := F '' C.nbhd
  left := F '' C.left
  right := F '' C.right
  isOpen_nbhd := F.isOpenMap _ C.isOpen_nbhd
  subset_nbhd := image_mono C.subset_nbhd
  nbhd_subset := image_mono C.nbhd_subset
  nbhd_diff := by
    calc
      F '' C.nbhd \ F '' P = F '' (C.nbhd \ P) :=
        (image_sdiff F.injective C.nbhd P).symm
      _ = F '' (C.left ∪ C.right) := by rw [C.nbhd_diff]
      _ = F '' C.left ∪ F '' C.right := image_union ..
  isConnected_left := C.isConnected_left.image F F.continuous.continuousOn
  isConnected_right := C.isConnected_right.image F F.continuous.continuousOn
  subset_closure_left := by
    rw [← F.image_closure]
    exact image_mono C.subset_closure_left
  subset_closure_right := by
    rw [← F.image_closure]
    exact image_mono C.subset_closure_right

/-- Ambient homeomorphisms preserve the complete collar property. -/
theorem HasArcCollars.image {D P : Set Plane} (h : HasArcCollars D P)
    (F : Plane ≃ₜ Plane) : HasArcCollars (F '' D) (F '' P) := by
  intro K hK hKcompact hKconn hKnon
  let K₀ : Set Plane := F.symm '' K
  have hK₀ : K₀ ⊆ D ∩ P := by
    intro x hx
    obtain ⟨y, hyK, rfl⟩ := hx
    obtain ⟨hyD, hyP⟩ := hK hyK
    constructor
    · rcases hyD with ⟨z, hz, hzy⟩
      have : F.symm y = z := by rw [← hzy]; simp
      exact this ▸ hz
    · rcases hyP with ⟨z, hz, hzy⟩
      have : F.symm y = z := by rw [← hzy]; simp
      exact this ▸ hz
  obtain ⟨C⟩ := h K₀ hK₀ (hKcompact.image F.symm.continuous)
    (hKconn.image F.symm F.symm.continuous.continuousOn) (hKnon.image F.symm.injective)
  have himage : F '' K₀ = K := by
    ext x
    simp [K₀]
  rw [← himage]
  exact ⟨C.image F⟩

/-- Any embedded arc that admits an ambient straightening has collars, whether
or not its given embedding is polygonal. -/
theorem hasArcCollars_of_ambient_straightening {D P : Set Plane} {a b : Plane}
    (hDopen : IsOpen D) (hab : a ≠ b)
    (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a, b} ⊆ D)
    (F : Plane ≃ₜ Plane) (hstraight : F '' P = segment ℝ (F a) (F b)) :
    HasArcCollars D P := by
  have hDopen' : IsOpen (F '' D) := F.isOpenMap D hDopen
  have ha' : F a ∉ F '' D := by
    rintro ⟨x, hx, hxa⟩
    exact ha ((F.injective hxa) ▸ hx)
  have hb' : F b ∉ F '' D := by
    rintro ⟨x, hx, hxb⟩
    exact hb ((F.injective hxb) ▸ hx)
  have hPD' : segment ℝ (F a) (F b) \ {F a, F b} ⊆ F '' D := by
    have hpair : F '' ({a, b} : Set Plane) = {F a, F b} := by simp
    rw [← hstraight, ← hpair, ← image_sdiff F.injective P {a, b}]
    exact image_mono hPD
  have hseg : HasArcCollars (F '' D) (F '' P) := by
    rw [hstraight]
    exact hasArcCollars_segment (F.injective.ne hab) hDopen' ha' hb' hPD'
  have hback := hseg.image F.symm
  have hDback : F.symm '' (F '' D) = D := by
    ext x
    simp
  have hPback : F.symm '' (F '' P) = P := by
    ext x
    simp
  rwa [hDback, hPback] at hback

theorem crosscut_components_exhaust_of_ambient_straightening
    {D P : Set Plane} {a b v₁ v₂ : Plane}
    (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hP : IsArcBetween P a b) (ha : a ∉ D) (hb : b ∉ D)
    (hPD : P \ {a, b} ⊆ D)
    (F : Plane ≃ₜ Plane) (hstraight : F '' P = segment ℝ (F a) (F b))
    (h₁ : v₁ ∈ D \ P) (h₂ : v₂ ∈ D \ P)
    (hne : connectedComponentIn (D \ P) v₁ ≠ connectedComponentIn (D \ P) v₂) :
    ∀ x ∈ D \ P, x ∈ connectedComponentIn (D \ P) v₁ ∨
      x ∈ connectedComponentIn (D \ P) v₂ := by
  have hab : a ≠ b := by
    obtain ⟨f, _, hi, _, h0, h1⟩ := hP
    intro heq
    have h01 : (0 : ℝ) = 1 := hi zero_mem_I one_mem_I (by rw [h0, h1, heq])
    norm_num at h01
  exact crosscut_components_exhaust_of_collars hDopen hDconn hP ha hb hPD
    (hasArcCollars_of_ambient_straightening hDopen hab ha hb hPD F hstraight)
    h₁ h₂ hne

end Schoenflies

#print axioms Schoenflies.crosscut_at_most_two_of_collars
#print axioms Schoenflies.crosscut_components_exhaust_of_collars
#print axioms Schoenflies.HasArcCollars.image
#print axioms Schoenflies.hasArcCollars_of_ambient_straightening
#print axioms Schoenflies.crosscut_components_exhaust_of_ambient_straightening
