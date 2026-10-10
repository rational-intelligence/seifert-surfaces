import CurveComplexGenusTwo.Octagon.SurfaceAssembly.SurfaceMV
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import Mathlib.Analysis.Convex.Contractible
import CurveComplexGenusTwo.Octagon.ActualAnnulusTransport
import CurveComplexGenusTwo.CWHurewicz.CircleHomologyComputation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CurveComplex.Octagon
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

noncomputable abbrev surfaceHF (n : ℕ) :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)

noncomputable def surfaceActualDifference (n : ℕ) :
    H overlapSet n ⟶ ModuleCat.of ℤ (H faceSet n × H bandSet n) :=
  actualMVDifference surfaceTop faceSet bandSet n

noncomputable def surfaceActualSum (n : ℕ) :
    ModuleCat.of ℤ (H faceSet n × H bandSet n) ⟶ H Surface n :=
  actualMVSum surfaceTop faceSet bandSet n

noncomputable def surfaceActualConnecting (n : ℕ) :
    H Surface (n + 1) ⟶ H overlapSet n :=
  actualMVConnecting surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

/-- Explicit comparison with the already-approved surface singular-chain model. -/
noncomputable def surfaceHomologyComparison (n : ℕ) :
    surfaceMVComplex.homology n ≅ H Surface n :=
  singularHomologyRepresentation surfaceTop n

theorem surfaceActualDifference_apply (n : ℕ) (x : H overlapSet n) :
    surfaceActualDifference n x =
      ((surfaceHF n).map (TopCat.ofHom overlapToFace) x,
        -(surfaceHF n).map (TopCat.ofHom overlapToBand) x) := by
  exact actualMVDifference_apply surfaceTop faceSet bandSet n x

theorem surfaceActualSum_apply (n : ℕ) (x : H faceSet n × H bandSet n) :
    surfaceActualSum n x =
      (surfaceHF n).map (TopCat.ofHom faceToSurface) x.1 +
        (surfaceHF n).map (TopCat.ofHom bandToSurface) x.2 := by
  exact actualMVSum_apply surfaceTop faceSet bandSet n x

theorem surfaceActualConnecting_difference (n : ℕ) :
    surfaceActualConnecting n ≫ surfaceActualDifference n = 0 := actualMVConnecting_difference surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

theorem surfaceActualDifference_sum (n : ℕ) :
    surfaceActualDifference n ≫ surfaceActualSum n = 0 := actualMVDifference_sum surfaceTop faceSet bandSet n

theorem surfaceActualSum_connecting (n : ℕ) :
    surfaceActualSum (n + 1) ≫ surfaceActualConnecting n = 0 := actualMVSum_connecting surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

theorem surfaceActual_exact_overlap (n : ℕ) :
    (ShortComplex.mk (surfaceActualConnecting n) (surfaceActualDifference n)
      (surfaceActualConnecting_difference n)).Exact := actualMV_exact_intersection surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

theorem surfaceActual_exact_pair (n : ℕ) :
    (ShortComplex.mk (surfaceActualDifference n) (surfaceActualSum n)
      (surfaceActualDifference_sum n)).Exact := actualMV_exact_pair surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

theorem surfaceActual_exact_surface (n : ℕ) :
    (ShortComplex.mk (surfaceActualSum (n + 1)) (surfaceActualConnecting n)
      (surfaceActualSum_connecting n)).Exact := actualMV_exact_ambient surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

theorem surfaceActual_zero_epi : Epi (surfaceActualSum 0) := actualMVSum_zero_epi surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2

/-- The concrete annulus-to-face commuting square induces this actual H square. -/
theorem surfaceActual_annulus_face_naturality (n : ℕ) :
    (surfaceHF n).map (TopCat.ofHom annulusToOverlap) ≫
      (surfaceHF n).map (TopCat.ofHom overlapToFace) =
    (surfaceHF n).map (TopCat.ofHom annulusToInterior) ≫
      (surfaceHF n).map
        (TopCat.ofHom (⟨faceCoordinates, faceCoordinates.continuous⟩ : C(diskInterior, faceSet))) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1


/-- The concrete annulus-to-band commuting square induces this actual H square. -/
theorem surfaceActual_annulus_band_naturality (n : ℕ) :
    (surfaceHF n).map (TopCat.ofHom annulusToOverlap) ≫
      (surfaceHF n).map (TopCat.ofHom overlapToBand) =
    (surfaceHF n).map (TopCat.ofHom annulusToOuterBand) ≫
      (surfaceHF n).map (TopCat.ofHom outerBandToBand) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1


/-- The actual quotient face is contractible, via its open disk coordinates. -/
theorem surfaceFace_contractible : ContractibleSpace faceSet := by
  let e : diskInterior ≃ₜ Metric.ball (0 : ℂ) 1 := {
    toFun := fun x => ⟨x.val.val, by simpa only [diskInterior, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right] using x.property⟩
    invFun := fun z => ⟨⟨z.val, by
      simpa [Metric.mem_closedBall, dist_zero_right] using
        le_of_lt (show ‖z.val‖ < 1 by simpa only [Metric.mem_ball, dist_zero_right] using z.property)⟩,
      by simpa only [diskInterior, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right] using z.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  letI : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩
  exact (faceCoordinates.symm.trans e).contractibleSpace

/-- All positive singular homology of the actual face vanishes. -/
theorem surfaceFace_positive_homology (n : ℕ) (hn : 0 < n) :
    IsZero (H faceSet n) := by
  letI := surfaceFace_contractible
  exact CircleHomologyComputation.contractible_positive_homology faceSet n hn

noncomputable def surfaceFace_H0_iso : H faceSet 0 ≅ ModuleCat.of ℤ ℤ := by
  letI := surfaceFace_contractible
  exact asIso ((TopCat.of faceSet).singularHomology₀ε (ModuleCat.of ℤ ℤ))


noncomputable def midCircleUnitHomeomorph : MidCircle ≃ₜ Circle where
  toFun z := ⟨(2 / 3 : ℂ) * z.val, by
    change (2 / 3 : ℂ) * z.val ∈ Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right]
    rw [norm_mul, z.property]
    norm_num [norm_div]⟩
  invFun z := ⟨(3 / 2 : ℂ) * (z : ℂ), by
    rw [norm_mul, Circle.norm_coe]
    norm_num [norm_div]⟩
  left_inv z := by apply Subtype.ext; dsimp; ring
  right_inv z := by apply Subtype.ext; dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def overlapCircleHomologyIso (n : ℕ) : H overlapSet n ≅ H Circle n :=
  ActualAnnulusTransport.overlapHomologyIso (ModuleCat.of ℤ ℤ) n ≪≫
    CircleHomologyComputation.homotopyHomologyIso midCircleUnitHomeomorph.toHomotopyEquiv n

/-- Actual overlap homology, obtained through annulus radial deformation and circle homology. -/
noncomputable def surfaceOverlap_H1_iso : H overlapSet 1 ≅ ModuleCat.of ℤ ℤ := by
  exact overlapCircleHomologyIso 1 ≪≫ CircleHomologyComputation.circleH1Iso

theorem surfaceOverlap_higher_homology (n : ℕ) (hn : 2 ≤ n) :
    IsZero (H overlapSet n) := by
  exact (CircleHomologyComputation.circle_higher_homology n hn).of_iso
    (overlapCircleHomologyIso n)

noncomputable def surfaceOverlap_H0_iso : H overlapSet 0 ≅ ModuleCat.of ℤ ℤ := by
  exact ActualAnnulusTransport.overlapHomologyZeroIso (ModuleCat.of ℤ ℤ)

/-- Vanishing of the face component does not assert vanishing of the band component. -/
theorem surfaceOverlap_face_positive_map_zero (n : ℕ) (hn : 0 < n) :
    (surfaceHF n).map (TopCat.ofHom overlapToFace) = 0 := by
  exact (surfaceFace_positive_homology n hn).eq_of_tgt _ _

theorem surfaceOverlap_face_H0_isIso :
    IsIso ((surfaceHF 0).map (TopCat.ofHom overlapToFace)) := by
  letI : ContractibleSpace faceSet := surfaceFace_contractible
  letI : PathConnectedSpace MidCircle := midCircleUnitHomeomorph.symm.pathConnectedSpace
  letI : IsIso ((surfaceHF 0).map (TopCat.ofHom ActualAnnulusTransport.overlapRadial)) :=
    ActualAnnulusTransport.overlapRadialHomology_isIso (ModuleCat.of ℤ ℤ) 0
  have hn := CircleHomologyComputation.augmentation_naturality
    (TopCat.ofHom ActualAnnulusTransport.overlapRadial)
  haveI : IsIso ((TopCat.of overlapSet).singularHomology₀ε (ModuleCat.of ℤ ℤ)) := by
    rw [← hn]
    infer_instance
  have hf := CircleHomologyComputation.augmentation_naturality (TopCat.ofHom overlapToFace)
  haveI : IsIso ((surfaceHF 0).map (TopCat.ofHom overlapToFace) ≫
      (TopCat.of faceSet).singularHomology₀ε (ModuleCat.of ℤ ℤ)) := by
    rw [hf]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((TopCat.of faceSet).singularHomology₀ε (ModuleCat.of ℤ ℤ))

theorem surfaceActualConnecting_zero : surfaceActualConnecting 0 = 0 := by
  letI := surfaceOverlap_face_H0_isIso
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (ModuleCat.mono_iff_injective
    ((surfaceHF 0).map (TopCat.ofHom overlapToFace))).mp inferInstance
  have h := congrArg (fun f => f x) (surfaceActualConnecting_difference 0)
  change surfaceActualDifference 0 (surfaceActualConnecting 0 x) = 0 at h
  have hf := congrArg Prod.fst h
  rw [surfaceActualDifference_apply] at hf
  change (surfaceHF 0).map (TopCat.ofHom overlapToFace) (surfaceActualConnecting 0 x) = 0 at hf
  simpa only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero] using hf

theorem surfaceActualSum_one_epi : Epi (surfaceActualSum 1) :=
  (surfaceActual_exact_surface 0).epi_f surfaceActualConnecting_zero

theorem surfaceBand_H1_epi :
    Epi ((surfaceHF 1).map (TopCat.ofHom bandToSurface)) := by
  letI := surfaceActualSum_one_epi
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨⟨u, v⟩, huv⟩ := (ModuleCat.epi_iff_surjective (surfaceActualSum 1)).mp inferInstance y
  refine ⟨v, ?_⟩
  rw [surfaceActualSum_apply] at huv
  have hz : (surfaceHF 1).map (TopCat.ofHom faceToSurface) = 0 :=
    (surfaceFace_positive_homology 1 (by omega)).eq_of_src _ _
  simpa only [hz, ModuleCat.hom_zero, LinearMap.zero_apply, zero_add] using huv


theorem surfaceOverlap_band_surface_H1_zero :
    (surfaceHF 1).map (TopCat.ofHom overlapToBand) ≫
      (surfaceHF 1).map (TopCat.ofHom bandToSurface) = 0 := by
  rw [← Functor.map_comp]
  have he : TopCat.ofHom overlapToBand ≫ TopCat.ofHom bandToSurface =
      TopCat.ofHom overlapToFace ≫ TopCat.ofHom faceToSurface := rfl
  rw [he, Functor.map_comp, surfaceOverlap_face_positive_map_zero 1 (by omega), zero_comp]

theorem surfaceBand_H1_kernel :
    LinearMap.ker ((surfaceHF 1).map (TopCat.ofHom bandToSurface)).hom =
      LinearMap.range ((surfaceHF 1).map (TopCat.ofHom overlapToBand)).hom := by
  apply le_antisymm
  · intro x hx
    have hx' : (surfaceHF 1).map (TopCat.ofHom bandToSurface) x = 0 := hx
    have hpair : (0, x) ∈ LinearMap.ker (surfaceActualSum 1).hom := by
      change surfaceActualSum 1 (0, x) = 0
      rw [surfaceActualSum_apply, map_zero, zero_add]
      exact hx'
    rw [← (surfaceActual_exact_pair 1).moduleCat_range_eq_ker] at hpair
    obtain ⟨z, hz⟩ := hpair
    have hb := congrArg Prod.snd hz
    rw [surfaceActualDifference_apply] at hb
    exact ⟨-z, by simpa only [map_neg] using hb⟩
  · rintro x ⟨z, rfl⟩
    have h := congrArg (fun f => f z) surfaceOverlap_band_surface_H1_zero
    exact h

noncomputable def surfaceBand_H1_quotientIso :
    ModuleCat.of ℤ (H bandSet 1 ⧸
      LinearMap.range ((surfaceHF 1).map (TopCat.ofHom overlapToBand)).hom) ≅ H Surface 1 := by
  letI := surfaceBand_H1_epi
  have hs := (ModuleCat.epi_iff_surjective
    ((surfaceHF 1).map (TopCat.ofHom bandToSurface))).mp inferInstance
  let q := ((surfaceHF 1).map (TopCat.ofHom bandToSurface)).hom.quotKerEquivOfSurjective hs
  let e := Submodule.quotEquivOfEq _ _ surfaceBand_H1_kernel.symm
  let a : (H bandSet 1 ⧸ LinearMap.range ((surfaceHF 1).map (TopCat.ofHom overlapToBand)).hom)
      ≃+ H Surface 1 := {
    toFun := fun x => q (e x)
    invFun := fun y => e.symm (q.symm y)
    left_inv := by intro x; simp
    right_inv := by intro x; simp
    map_add' := by intro x y; simp }
  exact {
    hom := ModuleCat.ofHom a.toIntLinearEquiv.toLinearMap
    inv := ModuleCat.ofHom a.symm.toIntLinearEquiv.toLinearMap
    hom_inv_id := by ext x; exact a.symm_apply_apply x
    inv_hom_id := by ext x; exact a.apply_symm_apply x }


theorem surfaceH2_connecting_range :
    LinearMap.range (surfaceActualConnecting 1).hom =
      LinearMap.ker ((surfaceHF 1).map (TopCat.ofHom overlapToBand)).hom := by
  rw [(surfaceActual_exact_overlap 1).moduleCat_range_eq_ker]
  ext x
  change surfaceActualDifference 1 x = 0 ↔
    (surfaceHF 1).map (TopCat.ofHom overlapToBand) x = 0
  rw [surfaceActualDifference_apply,
    surfaceOverlap_face_positive_map_zero 1 (by omega)]
  change (0, -(surfaceHF 1).map (TopCat.ofHom overlapToBand) x) = (0, 0) ↔ _
  simp only [Prod.mk.injEq, true_and, neg_eq_zero, and_self]

theorem surfaceH2_connecting_kernel :
    LinearMap.ker (surfaceActualConnecting 1).hom =
      LinearMap.range ((surfaceHF 2).map (TopCat.ofHom bandToSurface)).hom := by
  rw [← (surfaceActual_exact_surface 1).moduleCat_range_eq_ker]
  ext x
  constructor
  · rintro ⟨⟨u,v⟩, h⟩
    refine ⟨v, ?_⟩
    rw [surfaceActualSum_apply] at h
    have hz : (surfaceHF 2).map (TopCat.ofHom faceToSurface) = 0 :=
      (surfaceFace_positive_homology 2 (by omega)).eq_of_src _ _
    simpa only [hz, ModuleCat.hom_zero, LinearMap.zero_apply, zero_add] using h
  · rintro ⟨v, h⟩
    refine ⟨(0,v), ?_⟩
    change surfaceActualSum 2 (0,v) = x
    rw [surfaceActualSum_apply, map_zero, zero_add]
    exact h

noncomputable def surfaceH2Boundary : H Surface 2 ⟶ ModuleCat.of ℤ ℤ :=
  surfaceActualConnecting 1 ≫ surfaceOverlap_H1_iso.hom

noncomputable def surfaceAttachingH1 : ModuleCat.of ℤ ℤ ⟶ H bandSet 1 :=
  surfaceOverlap_H1_iso.inv ≫ (surfaceHF 1).map (TopCat.ofHom overlapToBand)

theorem surfaceH2Boundary_range :
    LinearMap.range surfaceH2Boundary.hom = LinearMap.ker surfaceAttachingH1.hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (surfaceHF 1).map (TopCat.ofHom overlapToBand)
      (surfaceOverlap_H1_iso.inv (surfaceOverlap_H1_iso.hom (surfaceActualConnecting 1 y))) = 0
    rw [Iso.hom_inv_id_apply]
    have h : surfaceActualConnecting 1 y ∈ LinearMap.range (surfaceActualConnecting 1).hom := ⟨y,rfl⟩
    rw [surfaceH2_connecting_range] at h
    exact h
  · intro hx
    have h : surfaceOverlap_H1_iso.inv x ∈ LinearMap.range (surfaceActualConnecting 1).hom := by
      rw [surfaceH2_connecting_range]
      exact hx
    obtain ⟨y, hy⟩ := h
    refine ⟨y, ?_⟩
    change surfaceOverlap_H1_iso.hom (surfaceActualConnecting 1 y) = x
    rw [hy, Iso.inv_hom_id_apply]

theorem surfaceAttachingH1_range :
    LinearMap.range surfaceAttachingH1.hom =
      LinearMap.ker ((surfaceHF 1).map (TopCat.ofHom bandToSurface)).hom := by
  rw [surfaceBand_H1_kernel]
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨surfaceOverlap_H1_iso.inv y,rfl⟩
  · rintro ⟨y,rfl⟩
    refine ⟨surfaceOverlap_H1_iso.hom y, ?_⟩
    change (surfaceHF 1).map (TopCat.ofHom overlapToBand)
      (surfaceOverlap_H1_iso.inv (surfaceOverlap_H1_iso.hom y)) = _
    rw [Iso.hom_inv_id_apply]


theorem surfaceH2Boundary_kernel :
    LinearMap.ker surfaceH2Boundary.hom =
      LinearMap.range ((surfaceHF 2).map (TopCat.ofHom bandToSurface)).hom := by
  rw [← surfaceH2_connecting_kernel]
  ext x
  change surfaceOverlap_H1_iso.hom (surfaceActualConnecting 1 x) = 0 ↔
    surfaceActualConnecting 1 x = 0
  constructor
  · intro h
    apply (ModuleCat.mono_iff_injective surfaceOverlap_H1_iso.hom).mp inferInstance
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]


end CurveComplex.Octagon
