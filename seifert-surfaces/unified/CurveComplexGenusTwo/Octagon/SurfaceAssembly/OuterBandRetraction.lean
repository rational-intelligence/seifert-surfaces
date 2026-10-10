import CurveComplexGenusTwo.Octagon.SurfaceAssembly.SurfaceCoverMaps
import CurveComplexGenusTwo.Octagon.AttachingMap
import Mathlib.Topology.CompactOpen
import CurveComplexGenusTwo.CWHurewicz.CircleHomologyComputation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CurveComplex.Octagon
open Topology
open AttachingMap

theorem bandQuotient : IsQuotientMap outerBandToBand := by
  let e : outerBand ≃ₜ mk ⁻¹' bandSet := Homeomorph.setCongr outerBand_preimage_image.symm
  exact outerBand_restricted_isQuotientMap.comp e.isQuotientMap

noncomputable def bandScale (t : unitInterval) (x : outerBand) : ℝ :=
  1 - (t : ℝ) + (t : ℝ) / ‖(x.val : ℂ)‖

theorem bandScale_pos (t : unitInterval) (x : outerBand) : 0 < bandScale t x := by
  have hn : 0 < ‖(x.val : ℂ)‖ := lt_trans (by norm_num) x.property
  have ht := t.property
  dsimp [bandScale]
  by_cases h : (t : ℝ) = 0
  · simp [h]
  · have hp := div_pos (lt_of_le_of_ne ht.1 (Ne.symm h)) hn
    linarith [ht.2]

theorem bandScale_norm (t : unitInterval) (x : outerBand) :
    ‖bandScale t x • (x.val : ℂ)‖ = (1 - (t : ℝ)) * ‖(x.val : ℂ)‖ + (t : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (bandScale_pos t x)]
  dsimp [bandScale]
  have hn : ‖(x.val : ℂ)‖ ≠ 0 := ne_of_gt (lt_trans (by norm_num) x.property)
  field_simp

theorem bandScale_mem (t : unitInterval) (x : outerBand) :
    (1/2 : ℝ) < ‖bandScale t x • (x.val : ℂ)‖ ∧
      ‖bandScale t x • (x.val : ℂ)‖ ≤ 1 := by
  rw [bandScale_norm]
  have ht := t.property
  have hl : (1/2 : ℝ) < ‖(x.val : ℂ)‖ := x.property
  have hu : ‖(x.val : ℂ)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.val.property
  constructor
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hu)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hu)]

noncomputable def rawBandDeform (p : unitInterval × outerBand) : outerBand :=
  ⟨⟨bandScale p.1 p.2 • (p.2.val : ℂ), by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (bandScale_mem p.1 p.2).2⟩,
    (bandScale_mem p.1 p.2).1⟩

theorem rawBandDeform_continuous : Continuous rawBandDeform := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have ht : Continuous fun p : unitInterval × outerBand => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous fun p : unitInterval × outerBand => (p.2.val : ℂ) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_const.sub ht).add (ht.div₀ hx.norm
    (fun p => ne_of_gt (lt_trans (by norm_num) p.2.property)))).smul hx

theorem rawBandDeform_fixed (t : unitInterval) (x : outerBand)
    (hx : ‖(x.val : ℂ)‖ = 1) : rawBandDeform (t,x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  simp [rawBandDeform, bandScale, hx]

theorem rawBandDeform_zero (x : outerBand) : rawBandDeform (0,x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  simp [rawBandDeform, bandScale]

theorem rawBandDeform_one_norm (x : outerBand) :
    ‖((rawBandDeform (1,x)).val : ℂ)‖ = 1 := by
  change ‖bandScale 1 x • (x.val : ℂ)‖ = 1
  rw [bandScale_norm]
  simp

theorem rawBandDeform_respects (t : unitInterval) {x y : outerBand}
    (h : outerBandToBand x = outerBandToBand y) :
    outerBandToBand (rawBandDeform (t,x)) = outerBandToBand (rawBandDeform (t,y)) := by
  have he : mk x.val = mk y.val := congrArg Subtype.val h
  have hn := eqvGen_normalForm (Quotient.exact he)
  rcases hn with heq | ⟨hx,hy⟩ | ⟨i,u,hx,hy⟩
  · have : x = y := Subtype.ext heq
    subst y
    rfl
  · obtain ⟨i,hi⟩ := hx
    obtain ⟨j,hj⟩ := hy
    have hnx : ‖(x.val : ℂ)‖ = 1 := by rw [← hi]; exact side_norm i 0
    have hny : ‖(y.val : ℂ)‖ = 1 := by rw [← hj]; exact side_norm j 0
    rw [rawBandDeform_fixed t x hnx, rawBandDeform_fixed t y hny]
    exact h
  · have hnx : ‖(x.val : ℂ)‖ = 1 := by rw [hx]; exact side_norm i u
    have hny : ‖(y.val : ℂ)‖ = 1 := by rw [hy]; exact side_norm _ _
    rw [rawBandDeform_fixed t x hnx, rawBandDeform_fixed t y hny]
    exact h

noncomputable def bandDeformAt (t : unitInterval) : C(bandSet,bandSet) :=
  bandQuotient.lift
    (outerBandToBand.comp ⟨fun x => rawBandDeform (t,x),
      rawBandDeform_continuous.comp (continuous_const.prodMk continuous_id)⟩)
    (fun _ _ h => rawBandDeform_respects t h)

theorem bandDeformAt_mk (t : unitInterval) (x : outerBand) :
    bandDeformAt t (outerBandToBand x) = outerBandToBand (rawBandDeform (t,x)) :=
  ContinuousMap.congr_fun (bandQuotient.lift_comp
    (outerBandToBand.comp ⟨fun x => rawBandDeform (t,x),
      rawBandDeform_continuous.comp (continuous_const.prodMk continuous_id)⟩)
    (fun _ _ h => rawBandDeform_respects t h)) x

theorem bandDeform_continuous : Continuous (fun p : unitInterval × bandSet => bandDeformAt p.1 p.2) := by
  apply bandQuotient.continuous_lift_prod_right
  simp_rw [bandDeformAt_mk]
  exact outerBandToBand.continuous.comp rawBandDeform_continuous

def boundaryToBand : C(BoundaryGraph, bandSet) :=
  ⟨fun q => ⟨q.val, by
    obtain ⟨i,t,he⟩ := q.property
    rw [he]
    exact outerBand_paired_edge_mem i t⟩, by fun_prop⟩

theorem bandDeformAt_boundary (t : unitInterval) (q : BoundaryGraph) :
    bandDeformAt t (boundaryToBand q) = boundaryToBand q := by
  rcases q with ⟨q, i, u, rfl⟩
  change bandDeformAt t (outerBandToBand ⟨side i u, side_mem_outerBand i u⟩) = _
  rw [bandDeformAt_mk, rawBandDeform_fixed t _ (side_norm i u)]
  rfl

theorem bandDeformAt_one_boundary (q : bandSet) :
    (bandDeformAt 1 q).val ∈ boundaryImage := by
  obtain ⟨x,rfl⟩ := bandQuotient.surjective q
  rw [bandDeformAt_mk]
  obtain ⟨i,t,h⟩ := boundary_point_on_side (rawBandDeform (1,x)).val
    (rawBandDeform_one_norm x)
  exact ⟨i,t,congrArg mk h.symm⟩

noncomputable def bandRetraction : C(bandSet, BoundaryGraph) :=
  ⟨fun q => ⟨(bandDeformAt 1 q).val, bandDeformAt_one_boundary q⟩,
    (continuous_subtype_val.comp (bandDeformAt 1).continuous).subtype_mk _⟩

theorem bandRetraction_inclusion :
    bandRetraction.comp boundaryToBand = ContinuousMap.id BoundaryGraph := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  change (bandDeformAt 1 (boundaryToBand q)).val = q.val
  exact congrArg Subtype.val (bandDeformAt_boundary 1 q)

noncomputable def bandRadialHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id bandSet) (boundaryToBand.comp bandRetraction) where
  toFun p := bandDeformAt p.1 p.2
  continuous_toFun := bandDeform_continuous
  map_zero_left := by
    intro q
    obtain ⟨x,rfl⟩ := bandQuotient.surjective q
    rw [bandDeformAt_mk, rawBandDeform_zero]
    rfl
  map_one_left := by intro q; rfl

noncomputable def bandBoundaryHomotopyEquiv : ContinuousMap.HomotopyEquiv bandSet BoundaryGraph where
  toFun := bandRetraction
  invFun := boundaryToBand
  left_inv := ⟨bandRadialHomotopy.symm⟩
  right_inv := by
    rw [bandRetraction_inclusion]


open CategoryTheory
open CurveComplexGenusTwo.CWHurewicz

noncomputable def bandBoundaryHomologyIso (n : ℕ) :
    H bandSet n ≅ H BoundaryGraph n :=
  CircleHomologyComputation.homotopyHomologyIso bandBoundaryHomotopyEquiv n


noncomputable def overlapUnitDirection : C(overlapSet, Circle) where
  toFun q :=
    let x := annulusOverlapHomeomorph.symm q
    ⟨(‖(x.val : ℂ)‖⁻¹ : ℝ) • (x.val : ℂ), by
      change (‖(x.val : ℂ)‖⁻¹ : ℝ) • (x.val : ℂ) ∈ Metric.sphere (0 : ℂ) 1
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (lt_trans (by norm_num) x.property.1))]
      exact inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num) x.property.1))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous fun q : overlapSet => ((annulusOverlapHomeomorph.symm q).val : ℂ) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp annulusOverlapHomeomorph.symm.continuous)
    exact (hc.norm.inv₀ (fun q => ne_of_gt
      (lt_trans (by norm_num) (annulusOverlapHomeomorph.symm q).property.1))).smul hc

theorem overlap_band_retraction_attaching :
    bandRetraction.comp overlapToBand = attachingMap.comp overlapUnitDirection := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨x,rfl⟩ := annulusOverlapHomeomorph.surjective q
  apply Subtype.ext
  have hpoint : overlapToBand (annulusOverlapHomeomorph x) =
      outerBandToBand ⟨x.val, x.property.1⟩ := by
    apply Subtype.ext
    change (annulusOverlapHomeomorph x).val = mk x.val
    exact congrArg (fun z : overlapSet => z.val) (annulusOverlapHomeomorph_apply x)
  change (bandDeformAt 1 (overlapToBand (annulusOverlapHomeomorph x))).val = _
  rw [hpoint, bandDeformAt_mk]
  simp only [ContinuousMap.comp_apply, attachingMap, ContinuousMap.coe_mk,
    overlapUnitDirection, Homeomorph.symm_apply_apply]
  apply congrArg mk
  apply Subtype.ext
  dsimp [rawBandDeform, bandScale, circleToDisk]
  simp


end CurveComplex.Octagon
