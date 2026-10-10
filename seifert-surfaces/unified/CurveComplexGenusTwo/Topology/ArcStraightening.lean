/-
Relative Jordan-Schoenflies and model-curve APIs are imported from the
Apache-2.0 Schoenflies dependency (Copyright (c) 2026 Álvaro Begué).
-/
import Schoenflies.JordanSchoenflies
import Schoenflies.ModelCurve
import Schoenflies.PolyArcRealize
import CurveComplexGenusTwo.Topology.GluedArcBoundary
import CurveComplexGenusTwo.Topology.ArbitraryCrosscutCore

open Set

namespace Schoenflies

/-- A simple crosscut that completes to a Jordan curve can be sent by an
ambient homeomorphism to a polygonal half of the model square. The boundary
map is glued from separate endpoint-matched homeomorphisms on the two arcs. -/
theorem exists_ambient_straightening_of_jordan_arc_split
    {A P : Set Plane} {a b : Plane}
    (hA : IsArcBetween A a b) (hP : IsArcBetween P a b)
    (hmeet : A ∩ P = {a, b})
    (hJ : IsJordanCurve (A ∪ P)) :
    ∃ F : Plane ≃ₜ Plane, F '' P = sideBottom ∪ sideRight ∧
      F a = cornerNE ∧ F b = cornerSW := by
  let B : Set Plane := sideTop ∪ sideLeft
  let Q : Set Plane := sideBottom ∪ sideRight
  have hB : IsArcBetween B cornerNE cornerSW := by
    simpa [B] using isArcBetween_upperSides
  have hQ : IsArcBetween Q cornerNE cornerSW := by
    simpa [Q] using isArcBetween_lowerSides.reverse
  have hmeetTarget : B ∩ Q = {cornerNE, cornerSW} := by
    apply Subset.antisymm
    · intro z hz
      have hmem : z ∈ sideTop ∪ sideLeft ∧ z ∈ sideBottom ∪ sideRight := by
        simpa [B, Q] using hz
      rcases upperSides_meet_lowerSides z hmem.1 hmem.2 with rfl | rfl
      · simp
      · simp
    · intro z hz
      have hz' : z = cornerNE ∨ z = cornerSW := by simpa using hz
      rcases hz' with rfl | rfl
      · exact ⟨hB.left_mem, hQ.left_mem⟩
      · exact ⟨hB.right_mem, hQ.right_mem⟩
  obtain ⟨e, hArcImage, hleft, hright⟩ :=
    exists_homeomorph_union_arcs_preserving_second hA hP hB hQ hmeet hmeetTarget
  have hModel : B ∪ Q = modelCurve := by
    dsimp [B, Q]
    exact modelCurve_eq_sides.symm
  let eModel : ↥(A ∪ P) ≃ₜ ↥modelCurve := e.trans (Homeomorph.setCongr hModel)
  obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hJ isJordanCurve_modelCurve eModel
  have hImage : F '' P = Q := by
    ext y
    constructor
    · rintro ⟨x, hxP, rfl⟩
      have hxJ : x ∈ A ∪ P := Or.inr hxP
      have hxArc : (e ⟨x, hxJ⟩ : Plane) ∈ Q := by
        have hmem : (e ⟨x, hxJ⟩ : ↥(B ∪ Q)) ∈ e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P} :=
          ⟨⟨x, hxJ⟩, hxP, rfl⟩
        have hval : (e ⟨x, hxJ⟩ : Plane) ∈ Subtype.val ''
            (e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P}) := Set.mem_image_of_mem _ hmem
        rw [hArcImage] at hval
        exact hval
      have hfx : F x = (eModel ⟨x, hxJ⟩ : Plane) := hF ⟨x, hxJ⟩
      have hEmodel : (eModel ⟨x, hxJ⟩ : Plane) = (e ⟨x, hxJ⟩ : Plane) := by rfl
      rw [hfx, hEmodel]
      simpa [Q] using hxArc
    · intro hy
      have hyQ : y ∈ Q := by simpa [Q] using hy
      have hyImage : y ∈ Subtype.val ''
          (e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P}) := by rw [hArcImage]; exact hyQ
      obtain ⟨z, hzImage, hzy⟩ := hyImage
      obtain ⟨x, hxP, hzx⟩ := hzImage
      have hxJ : (x : Plane) ∈ A ∪ P := x.property
      refine ⟨(x : Plane), hxP, ?_⟩
      have hFz : F (x : Plane) = (eModel ⟨(x : Plane), hxJ⟩ : Plane) :=
        hF ⟨(x : Plane), hxJ⟩
      have hEmodel : (eModel ⟨(x : Plane), hxJ⟩ : Plane) =
          (e ⟨(x : Plane), hxJ⟩ : Plane) := rfl
      have hzx' : (e ⟨(x : Plane), hxJ⟩ : Plane) = (z : Plane) :=
        congrArg Subtype.val hzx
      calc
        F (x : Plane) = (eModel ⟨(x : Plane), hxJ⟩ : Plane) := hFz
        _ = (e ⟨(x : Plane), hxJ⟩ : Plane) := hEmodel
        _ = (z : Plane) := hzx'
        _ = y := hzy
  have hFa : F a = cornerNE := by
    let x : ↥(A ∪ P) := ⟨a, Or.inl hA.left_mem⟩
    have hxF : F (x : Plane) = (eModel x : Plane) := hF x
    have hxE : (eModel x : Plane) = (e x : Plane) := rfl
    have hxe : (e x : Plane) = cornerNE := by
      have h := congrArg Subtype.val hleft
      exact h
    calc
      F a = F (x : Plane) := rfl
      _ = (eModel x : Plane) := hxF
      _ = (e x : Plane) := hxE
      _ = cornerNE := hxe
  have hFb : F b = cornerSW := by
    let x : ↥(A ∪ P) := ⟨b, Or.inl hA.right_mem⟩
    have hxF : F (x : Plane) = (eModel x : Plane) := hF x
    have hxE : (eModel x : Plane) = (e x : Plane) := rfl
    have hxe : (e x : Plane) = cornerSW := by
      have h := congrArg Subtype.val hright
      exact h
    calc
      F b = F (x : Plane) := rfl
      _ = (eModel x : Plane) := hxF
      _ = (e x : Plane) := hxE
      _ = cornerSW := hxe
  exact ⟨F, hImage, hFa, hFb⟩

/-- An arbitrary arc in a Jordan split inherits the two-sided collars of the
polygonal model arc under the relative Schoenflies homeomorphism. -/
theorem hasArcCollars_of_jordan_arc_split
    {D A P : Set Plane} {a b : Plane}
    (hDopen : IsOpen D)
    (hA : IsArcBetween A a b) (hP : IsArcBetween P a b)
    (hmeet : A ∩ P = {a, b})
    (hJ : IsJordanCurve (A ∪ P))
    (ha : a ∉ D) (hb : b ∉ D)
    (hPD : P \ {a, b} ⊆ D) :
    HasArcCollars D P := by
  obtain ⟨F, hF, hFa, hFb⟩ :=
    exists_ambient_straightening_of_jordan_arc_split hA hP hmeet hJ
  have hDopen' : IsOpen (F '' D) := F.isOpenMap D hDopen
  have ha' : cornerNE ∉ F '' D := by
    rw [← hFa]
    intro h
    obtain ⟨x, hxD, hx⟩ := h
    exact ha ((F.injective hx) ▸ hxD)
  have hb' : cornerSW ∉ F '' D := by
    rw [← hFb]
    intro h
    obtain ⟨x, hxD, hx⟩ := h
    exact hb ((F.injective hx) ▸ hxD)
  have hpair : F '' ({a, b} : Set Plane) = {cornerNE, cornerSW} := by
    simp [hFa, hFb]
  have hQPD : (sideBottom ∪ sideRight) \ {cornerNE, cornerSW} ⊆ F '' D := by
    rw [← hF, ← hpair, ← image_sdiff F.injective P ({a, b} : Set Plane)]
    exact image_mono hPD
  have hQarc : IsArcBetween (sideBottom ∪ sideRight) cornerNE cornerSW := by
    simpa using isArcBetween_lowerSides.reverse
  have hQpoly : IsPolygonal (sideBottom ∪ sideRight) := by
    apply IsPolygonal.union (isPolygonal_segment cornerSW cornerSE)
      (isPolygonal_segment cornerSE cornerNE)
    exact ⟨cornerSE, isArcBetween_sideBottom.right_mem,
      isArcBetween_sideRight.left_mem⟩
  have hseg : HasArcCollars (F '' D) (F '' P) := by
    rw [hF]
    exact hasArcCollars_of_isPolygonal hDopen' ha' hb' hQPD hQarc hQpoly
  have hback := hseg.image F.symm
  have hDback : F.symm '' (F '' D) = D := by
    ext x
    simp
  have hPback : F.symm '' (F '' P) = P := by
    ext x
    simp
  rwa [hDback, hPback] at hback

/-- A simple, possibly nonpolygonal crosscut of a Jordan domain has two-sided
collars: the boundary arc closes it to the Jordan split above. -/
theorem hasArcCollars_of_jordan_crosscut
    {C A P : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C)
    (hA : IsArcBetween A a b) (hAC : A ⊆ C)
    (hP : IsArcBetween P a b)
    (ha : a ∈ C) (hb : b ∈ C)
    (hPC : P ∩ C = {a, b})
    (hPD : P \ {a, b} ⊆ inside C) :
    HasArcCollars (inside C) P := by
  have hmeet : A ∩ P = {a, b} := by
    apply Subset.antisymm
    · intro z hz
      have hzPC : z ∈ P ∩ C := ⟨hz.2, hAC hz.1⟩
      rw [hPC] at hzPC
      exact hzPC
    · intro z hz
      rcases (by simpa using hz : z = a ∨ z = b) with rfl | rfl
      · exact ⟨hA.left_mem, hP.left_mem⟩
      · exact ⟨hA.right_mem, hP.right_mem⟩
  have hJ : IsJordanCurve (A ∪ P) :=
    isJordanCurve_union hA hP (fun z hzA hzP => by
      have hz : z ∈ ({a, b} : Set Plane) := hmeet ▸ ⟨hzA, hzP⟩
      simpa using hz)
  exact hasArcCollars_of_jordan_arc_split (isOpen_inside hC.isClosed) hA hP hmeet hJ
    (fun hz => inside_subset_compl hz ha) (fun hz => inside_subset_compl hz hb) hPD

/-- Source-level collar producer for a simple crosscut, deriving its exact
intersection with the Jordan boundary from endpoint and interior conditions. -/
theorem hasArcCollars_of_jordan_crosscut_of_endpoints
    {C A P : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C)
    (hA : IsArcBetween A a b) (hAC : A ⊆ C)
    (hP : IsArcBetween P a b)
    (ha : a ∈ C) (hb : b ∈ C)
    (hPD : P \ {a, b} ⊆ inside C) :
    HasArcCollars (inside C) P := by
  have hPC : P ∩ C = {a, b} := by
    apply Set.Subset.antisymm
    · intro z hz
      by_contra hzpair
      exact inside_subset_compl (hPD ⟨hz.1, hzpair⟩) hz.2
    · intro z hz
      rcases (by simpa using hz : z = a ∨ z = b) with rfl | rfl
      · exact ⟨hP.left_mem, ha⟩
      · exact ⟨hP.right_mem, hb⟩
  exact hasArcCollars_of_jordan_crosscut hC hA hAC hP ha hb hPC hPD

theorem crosscut_components_exhaust_of_jordan_crosscut
    {C A P : Set Plane} {a b v₁ v₂ : Plane}
    (hC : IsJordanCurve C)
    (hA : IsArcBetween A a b) (hAC : A ⊆ C)
    (hP : IsArcBetween P a b)
    (ha : a ∈ C) (hb : b ∈ C)
    (hPC : P ∩ C = {a, b})
    (hPD : P \ {a, b} ⊆ inside C)
    (h₁ : v₁ ∈ inside C \ P) (h₂ : v₂ ∈ inside C \ P)
    (hne : connectedComponentIn (inside C \ P) v₁ ≠
      connectedComponentIn (inside C \ P) v₂) :
    ∀ x ∈ inside C \ P, x ∈ connectedComponentIn (inside C \ P) v₁ ∨
      x ∈ connectedComponentIn (inside C \ P) v₂ := by
  have hsep : IsSeparating C := jordan_curve_theorem hC
  exact crosscut_components_exhaust_of_collars hsep.isOpen_inside
    hsep.isConnected_inside.isPreconnected hP
    (fun hz => inside_subset_compl hz ha) (fun hz => inside_subset_compl hz hb)
    hPD (hasArcCollars_of_jordan_crosscut hC hA hAC hP ha hb hPC hPD)
    h₁ h₂ hne

/-- Exact two-component classification for an arbitrary Jordan-domain
crosscut once two distinct complementary components are supplied. -/
theorem exact_two_components_of_jordan_crosscut
    {C A P : Set Plane} {a b v₁ v₂ : Plane}
    (hC : IsJordanCurve C)
    (hA : IsArcBetween A a b) (hAC : A ⊆ C)
    (hP : IsArcBetween P a b)
    (ha : a ∈ C) (hb : b ∈ C)
    (hPC : P ∩ C = {a, b})
    (hPD : P \ {a, b} ⊆ inside C)
    (h₁ : v₁ ∈ inside C \ P) (h₂ : v₂ ∈ inside C \ P)
    (hne : connectedComponentIn (inside C \ P) v₁ ≠
      connectedComponentIn (inside C \ P) v₂) :
    inside C \ P = connectedComponentIn (inside C \ P) v₁ ∪
      connectedComponentIn (inside C \ P) v₂ ∧
      Disjoint (connectedComponentIn (inside C \ P) v₁)
        (connectedComponentIn (inside C \ P) v₂) := by
  have hex := crosscut_components_exhaust_of_jordan_crosscut hC hA hAC hP ha hb
    hPC hPD h₁ h₂ hne
  constructor
  · apply Subset.antisymm
    · intro x hx
      exact hex x hx
    · intro x hx
      rcases hx with hx | hx
      · exact connectedComponentIn_subset _ _ hx
      · exact connectedComponentIn_subset _ _ hx
  · rw [Set.disjoint_left]
    intro x hx₁ hx₂
    apply hne
    exact (connectedComponentIn_eq hx₁).trans (connectedComponentIn_eq hx₂).symm

/-- The exterior of the original curve remains exterior to either Jordan
curve formed with a boundary subarc. -/
theorem outside_subset_outside_jordan_crosscut
    {C A P : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C) (hA : A ⊆ C)
    (hP : IsArcBetween P a b)
    (ha : a ∈ C) (hb : b ∈ C)
    (hPD : P \ {a, b} ⊆ inside C) :
    outside C ⊆ outside (A ∪ P) := by
  have hsep : IsSeparating C := jordan_curve_theorem hC
  have hPout : Disjoint P (outside C) := by
    rw [Set.disjoint_left]
    intro z hzP hzO
    by_cases hz : z ∈ ({a, b} : Set Plane)
    · rcases (by simpa using hz : z = a ∨ z = b) with rfl | rfl
      · exact hzO.1 ha
      · exact hzO.1 hb
    · exact Set.disjoint_left.1 disjoint_inside_outside (hPD ⟨hzP, hz⟩) hzO
  have hsub : outside C ⊆ (A ∪ P)ᶜ := by
    intro z hz hzAP
    rcases hzAP with hzA | hzP
    · exact hz.1 (hA hzA)
    · exact Set.disjoint_left.1 hPout hzP hz
  intro z hz
  refine ⟨hsub hz, fun hbdd => hsep.not_isBounded_outside (hbdd.subset ?_)⟩
  exact hsep.isConnected_outside.isPreconnected.subset_connectedComponentIn hz hsub

/-- The named bounded side is a component of the domain cut by an arbitrary
simple arc. Polygonality is nowhere used in this component recognition. -/
theorem jordan_crosscut_side_isComponent
    {C A P : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C)
    (hA : IsArcBetween A a b) (hAC : A ⊆ C)
    (hP : IsArcBetween P a b)
    (ha : a ∈ C) (hb : b ∈ C)
    (hPC : P ∩ C = {a, b})
    (hPD : P \ {a, b} ⊆ inside C) :
    ∀ z ∈ inside (A ∪ P),
      connectedComponentIn (inside C \ P) z = inside (A ∪ P) := by
  have hJ : IsJordanCurve (A ∪ P) := by
    apply isJordanCurve_union hA hP
    intro z hzA hzP
    have hz : z ∈ ({a, b} : Set Plane) := hPC ▸ ⟨hzP, hAC hzA⟩
    simpa using hz
  have hsep : IsSeparating C := jordan_curve_theorem hC
  have hJsep : IsSeparating (A ∪ P) := jordan_curve_theorem hJ
  refine cell_isComponent hsep hJsep
    (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)
    (outside_subset_outside_jordan_crosscut hC hAC hP ha hb hPD)
    subset_union_right (Set.union_subset (hAC.trans Set.subset_union_left)
      Set.subset_union_right)

/-- The closure of the named side meets the old boundary in precisely the
boundary arc used to close the crosscut. -/
theorem jordan_crosscut_closure_side_inter
    {C A P : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C)
    (hA : IsArcBetween A a b) (hAC : A ⊆ C)
    (hP : IsArcBetween P a b)
    (ha : a ∈ C) (hb : b ∈ C)
    (hPC : P ∩ C = {a, b})
    (hPD : P \ {a, b} ⊆ inside C) :
    closure (inside (A ∪ P)) ∩ C = A := by
  have hJ : IsJordanCurve (A ∪ P) := by
    apply isJordanCurve_union hA hP
    intro z hzA hzP
    have hz : z ∈ ({a, b} : Set Plane) := hPC ▸ ⟨hzP, hAC hzA⟩
    simpa using hz
  have hsep : IsSeparating C := jordan_curve_theorem hC
  have hJsep : IsSeparating (A ∪ P) := jordan_curve_theorem hJ
  rw [closure_cell_inter_curve hsep hJsep (IsRegionOf.outside C)
    (Or.inr ⟨rfl, rfl⟩)
    (outside_subset_outside_jordan_crosscut hC hAC hP ha hb hPD)]
  ext z
  constructor
  · rintro ⟨hzA | hzP, hzC⟩
    · exact hzA
    · have hzPair : z ∈ ({a, b} : Set Plane) := hPC ▸ ⟨hzP, hzC⟩
      rcases (by simpa using hzPair : z = a ∨ z = b) with rfl | rfl
      · exact hA.left_mem
      · exact hA.right_mem
  · intro hzA
    exact ⟨Or.inl hzA, hAC hzA⟩

/-- The full Jordan-domain crosscut classification for a simple arc, with no
polygonality requirement. The two boundary arcs name and distinguish the two
components of the cut domain. -/
theorem general_crosscut_arbitrary
    {C P A₁ A₂ : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P a b)
    (hcut : IsCutPair C a b A₁ A₂)
    (hPC : P ∩ C = {a, b})
    (hPD : P \ {a, b} ⊆ inside C) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      (∀ z ∈ inside (A₁ ∪ P),
        connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P),
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ inside C \ P,
        connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧
      closure (inside (A₂ ∪ P)) ∩ C = A₂ := by
  have ha : a ∈ C := hcut.fst_subset hcut.fst.left_mem
  have hb : b ∈ C := hcut.fst_subset hcut.fst.right_mem
  have hJ (A : Set Plane) (hA : IsArcBetween A a b) (hAC : A ⊆ C) :
      IsJordanCurve (A ∪ P) := by
    apply isJordanCurve_union hA hP
    intro z hzA hzP
    have hz : z ∈ ({a, b} : Set Plane) := hPC ▸ ⟨hzP, hAC hzA⟩
    simpa using hz
  have h₁non : (inside (A₁ ∪ P)).Nonempty :=
    (jordan_curve_theorem (hJ A₁ hcut.fst hcut.fst_subset)).isConnected_inside.nonempty
  have h₂non : (inside (A₂ ∪ P)).Nonempty :=
    (jordan_curve_theorem (hJ A₂ hcut.snd hcut.snd_subset)).isConnected_inside.nonempty
  have h₁comp := jordan_crosscut_side_isComponent hC hcut.fst hcut.fst_subset
    hP ha hb hPC hPD
  have h₂comp := jordan_crosscut_side_isComponent hC hcut.snd hcut.snd_subset
    hP ha hb hPC hPD
  have h₁label := jordan_crosscut_closure_side_inter hC hcut.fst hcut.fst_subset
    hP ha hb hPC hPD
  have h₂label := jordan_crosscut_closure_side_inter hC hcut.snd hcut.snd_subset
    hP ha hb hPC hPD
  have hsideNe : inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) := by
    intro heq
    have h₁label' := h₁label
    rw [heq] at h₁label'
    exact hcut.ne (h₁label'.symm.trans h₂label)
  have hdisj : Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) := by
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    exact hsideNe ((h₁comp z hz₁).symm.trans (h₂comp z hz₂))
  obtain ⟨v₁, hv₁side⟩ := h₁non
  obtain ⟨v₂, hv₂side⟩ := h₂non
  have hv₁ : v₁ ∈ inside C \ P := by
    have heq := h₁comp v₁ hv₁side
    have hmem : v₁ ∈ connectedComponentIn (inside C \ P) v₁ := heq ▸ hv₁side
    exact connectedComponentIn_subset _ _ hmem
  have hv₂ : v₂ ∈ inside C \ P := by
    have heq := h₂comp v₂ hv₂side
    have hmem : v₂ ∈ connectedComponentIn (inside C \ P) v₂ := heq ▸ hv₂side
    exact connectedComponentIn_subset _ _ hmem
  have hne : connectedComponentIn (inside C \ P) v₁ ≠
      connectedComponentIn (inside C \ P) v₂ := by
    rw [h₁comp v₁ hv₁side, h₂comp v₂ hv₂side]
    exact hsideNe
  have hex := crosscut_components_exhaust_of_jordan_crosscut hC hcut.fst
    hcut.fst_subset hP ha hb hPC hPD hv₁ hv₂ hne
  have hcomp : ∀ z ∈ inside C \ P,
      connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
      connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P) := by
    intro z hz
    rcases hex z hz with hz₁ | hz₂
    · rw [h₁comp v₁ hv₁side] at hz₁
      exact Or.inl (h₁comp z hz₁)
    · rw [h₂comp v₂ hv₂side] at hz₂
      exact Or.inr (h₂comp z hz₂)
  have hcover : inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases hex z hz with hz₁ | hz₂
      · exact Or.inl ((h₁comp v₁ hv₁side) ▸ hz₁)
      · exact Or.inr ((h₂comp v₂ hv₂side) ▸ hz₂)
    · intro z hz
      rcases hz with hz₁ | hz₂
      · have hmem : z ∈ connectedComponentIn (inside C \ P) z :=
          (h₁comp z hz₁) ▸ hz₁
        exact connectedComponentIn_subset _ _ hmem
      · have hmem : z ∈ connectedComponentIn (inside C \ P) z :=
          (h₂comp z hz₂) ▸ hz₂
        exact connectedComponentIn_subset _ _ hmem
  exact ⟨hcover, hdisj, ⟨v₁, hv₁side⟩, ⟨v₂, hv₂side⟩, hsideNe, h₁comp, h₂comp,
    hcomp, h₁label, h₂label⟩

/-- The source crosscut hypotheses imply the exact endpoint intersection with
the boundary, so the arbitrary-arc classification needs no extra incidence
assumption. -/
theorem general_crosscut_arbitrary_of_endpoints
    {C P A₁ A₂ : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P a b)
    (hcut : IsCutPair C a b A₁ A₂)
    (hPD : P \ {a, b} ⊆ inside C) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      (∀ z ∈ inside (A₁ ∪ P),
        connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P),
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ inside C \ P,
        connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧
      closure (inside (A₂ ∪ P)) ∩ C = A₂ := by
  have ha : a ∈ C := hcut.fst_subset hcut.fst.left_mem
  have hb : b ∈ C := hcut.fst_subset hcut.fst.right_mem
  have hPC : P ∩ C = {a, b} := by
    apply Set.Subset.antisymm
    · intro z hz
      by_contra hzpair
      exact inside_subset_compl (hPD ⟨hz.1, hzpair⟩) hz.2
    · intro z hz
      rcases (by simpa using hz : z = a ∨ z = b) with rfl | rfl
      · exact ⟨hP.left_mem, ha⟩
      · exact ⟨hP.right_mem, hb⟩
  exact general_crosscut_arbitrary hC hP hcut hPC hPD

/-- The exterior remains a component after inserting an arbitrary crosscut. -/
theorem jordan_crosscut_outside_isComponent_compl
    {C P : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P a b)
    (ha : a ∈ C) (hb : b ∈ C)
    (hPD : P \ {a, b} ⊆ inside C) :
    ∀ z ∈ outside C, connectedComponentIn (C ∪ P)ᶜ z = outside C := by
  have hsep : IsSeparating C := jordan_curve_theorem hC
  have hPout : Disjoint P (outside C) := by
    rw [Set.disjoint_left]
    intro z hzP hzO
    by_cases hz : z ∈ ({a, b} : Set Plane)
    · rcases (by simpa using hz : z = a ∨ z = b) with rfl | rfl
      · exact hzO.1 ha
      · exact hzO.1 hb
    · exact Set.disjoint_left.1 disjoint_inside_outside (hPD ⟨hzP, hz⟩) hzO
  have hsub : outside C ⊆ (C ∪ P)ᶜ := by
    intro z hz hzCP
    rcases hzCP with hzC | hzP
    · exact hz.1 hzC
    · exact Set.disjoint_left.1 hPout hzP hz
  intro z hz
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint hsep.isOpen_outside
    hsep.isConnected_outside.isPreconnected hsub ?_ hz
  rw [hsep.frontier_outside]
  exact eq_empty_iff_forall_notMem.2 fun w hw => hw.2 (Or.inl hw.1)

/-- Either bounded side is also a component of the full complement. -/
theorem jordan_crosscut_side_isComponent_compl
    {C A P : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C)
    (hA : IsArcBetween A a b) (hAC : A ⊆ C)
    (hP : IsArcBetween P a b)
    (ha : a ∈ C) (hb : b ∈ C)
    (hPC : P ∩ C = {a, b})
    (hPD : P \ {a, b} ⊆ inside C) :
    ∀ z ∈ inside (A ∪ P),
      connectedComponentIn (C ∪ P)ᶜ z = inside (A ∪ P) := by
  have hJ : IsJordanCurve (A ∪ P) := by
    apply isJordanCurve_union hA hP
    intro z hzA hzP
    have hz : z ∈ ({a, b} : Set Plane) := hPC ▸ ⟨hzP, hAC hzA⟩
    simpa using hz
  have hJsep : IsSeparating (A ∪ P) := jordan_curve_theorem hJ
  have hsub : inside (A ∪ P) ⊆ (C ∪ P)ᶜ := by
    intro z hz hzCP
    have hzD : z ∈ inside C \ P := by
      have heq := jordan_crosscut_side_isComponent hC hA hAC hP ha hb hPC hPD z hz
      exact connectedComponentIn_subset _ _ (heq ▸ hz)
    rcases hzCP with hzC | hzP
    · exact inside_subset_compl hzD.1 hzC
    · exact hzD.2 hzP
  intro z hz
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint hJsep.isOpen_inside
    hJsep.isConnected_inside.isPreconnected hsub ?_ hz
  rw [hJsep.frontier_inside]
  apply eq_empty_iff_forall_notMem.2
  intro w hw
  rcases hw.1 with hwA | hwP
  · exact hw.2 (Or.inl (hAC hwA))
  · exact hw.2 (Or.inr hwP)

/-- The complement of a Jordan curve and an arbitrary simple crosscut has
exactly the exterior and two named bounded components. -/
theorem general_crosscut_three_regions_arbitrary
    {C P A₁ A₂ : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P a b)
    (hcut : IsCutPair C a b A₁ A₂)
    (hPD : P \ {a, b} ⊆ inside C) :
    (C ∪ P)ᶜ = outside C ∪ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      (∀ z ∈ outside C, connectedComponentIn (C ∪ P)ᶜ z = outside C) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ (C ∪ P)ᶜ, connectedComponentIn (C ∪ P)ᶜ z = outside C ∨
        connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P) ∨
        connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P)) ∧
      Disjoint (outside C) (inside (A₁ ∪ P)) ∧
      Disjoint (outside C) (inside (A₂ ∪ P)) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      outside C ≠ inside (A₁ ∪ P) ∧ outside C ≠ inside (A₂ ∪ P) ∧
      inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      frontier (outside C) = C ∧
      frontier (inside (A₁ ∪ P)) = A₁ ∪ P ∧
      frontier (inside (A₂ ∪ P)) = A₂ ∪ P := by
  have ha : a ∈ C := hcut.fst_subset hcut.fst.left_mem
  have hb : b ∈ C := hcut.fst_subset hcut.fst.right_mem
  have hPC : P ∩ C = {a, b} := by
    apply Set.Subset.antisymm
    · intro z hz
      by_contra hzpair
      exact inside_subset_compl (hPD ⟨hz.1, hzpair⟩) hz.2
    · intro z hz
      rcases (by simpa using hz : z = a ∨ z = b) with rfl | rfl
      · exact ⟨hP.left_mem, ha⟩
      · exact ⟨hP.right_mem, hb⟩
  obtain ⟨hcover, hdisj, h₁non, h₂non, hsideNe, -, -, -, -, -⟩ :=
    general_crosscut_arbitrary hC hP hcut hPC hPD
  have hsep : IsSeparating C := jordan_curve_theorem hC
  have hJ₁ : IsJordanCurve (A₁ ∪ P) := by
    apply isJordanCurve_union hcut.fst hP
    intro z hzA hzP
    have hz : z ∈ ({a, b} : Set Plane) := hPC ▸ ⟨hzP, hcut.fst_subset hzA⟩
    simpa using hz
  have hJ₂ : IsJordanCurve (A₂ ∪ P) := by
    apply isJordanCurve_union hcut.snd hP
    intro z hzA hzP
    have hz : z ∈ ({a, b} : Set Plane) := hPC ▸ ⟨hzP, hcut.snd_subset hzA⟩
    simpa using hz
  have hout := jordan_crosscut_outside_isComponent_compl hC hP ha hb hPD
  have h₁ := jordan_crosscut_side_isComponent_compl hC hcut.fst hcut.fst_subset
    hP ha hb hPC hPD
  have h₂ := jordan_crosscut_side_isComponent_compl hC hcut.snd hcut.snd_subset
    hP ha hb hPC hPD
  have hthree : (C ∪ P)ᶜ = outside C ∪ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by
    rw [Set.union_assoc, ← hcover]
    ext z
    constructor
    · intro hz
      have hzC : z ∉ C := fun hzc => hz (Or.inl hzc)
      have hzP : z ∉ P := fun hzp => hz (Or.inr hzp)
      have hz' : z ∈ inside C ∪ outside C := by
        rw [inside_union_outside]
        exact hzC
      rcases hz' with hzi | hzo
      · exact Or.inr ⟨hzi, hzP⟩
      · exact Or.inl hzo
    · rintro (hzo | ⟨hzi, hzP⟩) (hzc | hzp)
      · exact hzo.1 hzc
      · have hPout : Disjoint P (outside C) := by
          rw [Set.disjoint_left]
          intro w hwP hwO
          by_cases hw : w ∈ ({a, b} : Set Plane)
          · rcases (by simpa using hw : w = a ∨ w = b) with rfl | rfl
            · exact hwO.1 ha
            · exact hwO.1 hb
          · exact Set.disjoint_left.1 disjoint_inside_outside
              (hPD ⟨hwP, hw⟩) hwO
        exact Set.disjoint_left.1 hPout hzp hzo
      · exact hzi.1 hzc
      · exact hzP hzp
  have hcomponents : ∀ z ∈ (C ∪ P)ᶜ,
      connectedComponentIn (C ∪ P)ᶜ z = outside C ∨
      connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P) ∨
      connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P) := by
    intro z hz
    rw [hthree] at hz
    rcases hz with (hz | hz) | hz
    · exact Or.inl (hout z hz)
    · exact Or.inr (Or.inl (h₁ z hz))
    · exact Or.inr (Or.inr (h₂ z hz))
  have hD₁ : Disjoint (outside C) (inside (A₁ ∪ P)) := by
    rw [Set.disjoint_left]
    intro z hzO hz₁
    have hzD : z ∈ inside C \ P := by
      have heq := jordan_crosscut_side_isComponent hC hcut.fst hcut.fst_subset
        hP ha hb hPC hPD z hz₁
      exact connectedComponentIn_subset _ _ (heq ▸ hz₁)
    exact Set.disjoint_left.1 disjoint_inside_outside hzD.1 hzO
  have hD₂ : Disjoint (outside C) (inside (A₂ ∪ P)) := by
    rw [Set.disjoint_left]
    intro z hzO hz₂
    have hzD : z ∈ inside C \ P := by
      have heq := jordan_crosscut_side_isComponent hC hcut.snd hcut.snd_subset
        hP ha hb hPC hPD z hz₂
      exact connectedComponentIn_subset _ _ (heq ▸ hz₂)
    exact Set.disjoint_left.1 disjoint_inside_outside hzD.1 hzO
  have hO₁ : outside C ≠ inside (A₁ ∪ P) := by
    intro heq
    obtain ⟨z, hz⟩ := h₁non
    exact Set.disjoint_left.1 hD₁ (heq ▸ hz) hz
  have hO₂ : outside C ≠ inside (A₂ ∪ P) := by
    intro heq
    obtain ⟨z, hz⟩ := h₂non
    exact Set.disjoint_left.1 hD₂ (heq ▸ hz) hz
  exact ⟨hthree, hout, h₁, h₂, hcomponents, hD₁, hD₂, hdisj,
    hO₁, hO₂, hsideNe, hsep.frontier_outside,
    (jordan_curve_theorem hJ₁).frontier_inside,
    (jordan_curve_theorem hJ₂).frontier_inside⟩

/-! ### Finite families of local Jordan splits

For a banana family, the local Jordan theorem supplies a split only after the
current face containing the new arc has been identified.  The following
certificate records exactly that local datum and gives the complete finite
induction once such certificates are supplied. -/

/- Legacy finite split invariant retained for compatibility with earlier scratch consumers. -/
def FiniteSplitInvariant (D : Set Plane) (parts : Finset (Set Plane)) : Prop :=
  D = ⋃ R ∈ parts, R ∧
  (∀ R ∈ parts, IsConnected R ∧ IsOpen R) ∧
  (∀ R ∈ parts, ∀ S ∈ parts, R ≠ S → Disjoint R S)

def SplitTriple := Set Plane × Set Plane × Set Plane

noncomputable def splitParts (parts : Finset (Set Plane)) (s : SplitTriple) : Finset (Set Plane) :=
  insert s.2.2 (insert s.2.1 (parts.erase s.1))

noncomputable def splitFold : List SplitTriple → Finset (Set Plane) → Finset (Set Plane)
  | [], parts => parts
  | s :: ss, parts => splitFold ss (splitParts parts s)

end Schoenflies

#print axioms Schoenflies.exists_ambient_straightening_of_jordan_arc_split
#print axioms Schoenflies.hasArcCollars_of_jordan_arc_split
#print axioms Schoenflies.hasArcCollars_of_jordan_crosscut
#print axioms Schoenflies.hasArcCollars_of_jordan_crosscut_of_endpoints
#print axioms Schoenflies.crosscut_components_exhaust_of_jordan_crosscut
#print axioms Schoenflies.exact_two_components_of_jordan_crosscut
#print axioms Schoenflies.jordan_crosscut_side_isComponent
#print axioms Schoenflies.jordan_crosscut_closure_side_inter
#print axioms Schoenflies.general_crosscut_arbitrary
#print axioms Schoenflies.general_crosscut_arbitrary_of_endpoints
#print axioms Schoenflies.general_crosscut_three_regions_arbitrary
#print axioms Schoenflies.FiniteSplitInvariant
