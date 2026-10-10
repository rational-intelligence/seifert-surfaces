import B1ImageTransitions
import B1SectorCornerCover
import AreaSectorInteriorSupport
open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory
namespace SeifertSurfaces.MetricFoundations.B1Bridges
open SeifertSurfaces.Foundations
universe u v
noncomputable section
set_option autoImplicit false
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

def sectorCrossDomain {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (i : Fin G.pieceCount) (j : Fin (G.domain i).count)
    (r : Fin F.pieceCount) (l : Fin (F.domain r).count) : Set (Euc 2) :=
  interior ((G.domain i).chart j).map.target ∩
    (G.parametrization i ∘ ((G.domain i).chart j).map.symm) ⁻¹'
      ((G.seam.carrier ∪ R.boundary)ᶜ ∩ a ⁻¹'
        ((F.parametrization r) '' ((F.domain r).interior ∩ ((F.domain r).chart l).map.source)))

structure SectorImageTransition {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (i : Fin G.pieceCount) (j : Fin (G.domain i).count)
    (r : Fin F.pieceCount) (l : Fin (F.domain r).count) where
  coordinate : PartialHomeomorph (Euc 2) (Euc 2)
  source_eq : coordinate.source = sectorCrossDomain F G a i j r l
  target_eq : coordinate.target = sectorCrossDomain G F a.symm r l i j
  open_source : IsOpen coordinate.source
  open_target : IsOpen coordinate.target
  parametrization_matches : ∀ y ∈ coordinate.source,
    F.parametrization r (((F.domain r).chart l).map.symm (coordinate y)) =
      a (G.parametrization i (((G.domain i).chart j).map.symm y))
  smooth : ContDiffOn ℝ ∞ coordinate coordinate.source
  smooth_inverse : ContDiffOn ℝ ∞ coordinate.symm coordinate.target
  derivative_injective : ∀ y ∈ coordinate.source, Function.Injective (fderiv ℝ coordinate y)
  jacobian_ne_zero : ∀ y ∈ coordinate.source, (fderiv ℝ coordinate y).det ≠ 0

theorem sector_same_image_transition_exists {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (ha : ∀ x, F.map (a x) = G.map x)
    (hb : a ⁻¹' S.boundary = R.boundary)
    (i : Fin G.pieceCount) (j : Fin (G.domain i).count)
    (r : Fin F.pieceCount) (l : Fin (F.domain r).count) :
    Nonempty (SectorImageTransition F G a i j r l) := by
  classical
  have localchart {S : CompactOrientedSurface.{u}} (H : GeometricPiecewiseSurface S M)
      (i : Fin H.pieceCount) (j : Fin (H.domain i).count) :
      ∃ e : PartialHomeomorph (Euc 2) S,
        e.source = interior ((H.domain i).chart j).map.target ∧
        e.target = (H.parametrization i) ''
          ((H.domain i).interior ∩ ((H.domain i).chart j).map.source) ∧
        (∀ y, e y = H.parametrization i (((H.domain i).chart j).map.symm y)) ∧
        (∀ x ∈ e.target, x ∈ (H.seam.carrier ∪ S.boundary)ᶜ) ∧
        IsOpen e.source ∧ IsOpen e.target := by
    letI : Nonempty (H.domain i) := ⟨((H.domain i).chart j).map.symm 0⟩
    let A := ((H.domain i).chart j).map
    let B := (H.parametrization_embedding i).toPartialHomeomorph (H.parametrization i)
    let target := H.parametrization i '' ((H.domain i).interior ∩ A.source)
    have hbpre : ∀ z ∈ target, B.symm z ∈ (H.domain i).interior ∩ A.source := by
      rintro _ ⟨x, hx, rfl⟩
      rw [(H.parametrization_embedding i).toPartialHomeomorph_left_inv]
      exact hx
    let d : PartialEquiv (Euc 2) S := {
      toFun := H.parametrization i ∘ A.symm
      invFun := A ∘ B.symm
      source := interior A.target
      target := target
      map_source' := fun y hy => ⟨A.symm y,
        AreaCertificates.sector_chart_inverse_interior (H.domain i) j hy, rfl⟩
      map_target' := by
        intro z hz
        change A (B.symm z) ∈ interior A.target
        rw [← AreaCertificates.sector_chart_piece_interior (H.domain i) j]
        exact ⟨B.symm z, hbpre z hz, rfl⟩
      left_inv' := by
        intro y hy
        change A (B.symm (H.parametrization i (A.symm y))) = y
        rw [(H.parametrization_embedding i).toPartialHomeomorph_left_inv,
          A.right_inv (interior_subset hy)]
      right_inv' := by
        rintro _ ⟨x, hx, rfl⟩
        change H.parametrization i (A.symm (A (B.symm (H.parametrization i x)))) = _
        rw [(H.parametrization_embedding i).toPartialHomeomorph_left_inv, A.left_inv hx.2] }
    let e : PartialHomeomorph (Euc 2) S := {
      toPartialEquiv := d
      continuousOn_toFun := (H.parametrization i).continuous.comp_continuousOn
        (A.symm.continuousOn.mono interior_subset)
      continuousOn_invFun := A.continuousOn.comp (B.symm.continuousOn.mono
        (by rintro _ ⟨x, hx, rfl⟩; exact ⟨x, mem_univ x, rfl⟩))
        (fun z hz => (hbpre z hz).2) }
    have hefun : ∀ y, e y = H.parametrization i (A.symm y) := fun _ => rfl
    have hesource : e.source = interior A.target := rfl
    have hetarget : e.target = H.parametrization i ''
        ((H.domain i).interior ∩ A.source) := rfl
    have hoff : ∀ x ∈ e.target, x ∈ (H.seam.carrier ∪ S.boundary)ᶜ := by
      intro x hx
      rw [hetarget] at hx
      have hi : x ∈ H.parametrization i '' (H.domain i).interior :=
        image_mono inter_subset_left hx
      obtain ⟨z, hz, hcomponent⟩ := H.piece_interior_component i
      rw [hcomponent] at hi
      exact connectedComponentIn_subset _ _ hi
    exact ⟨e, hesource, hetarget, hefun, hoff, hesource ▸ isOpen_interior,
      hetarget ▸ AreaCertificates.geometric_piece_chart_interior_image_open H i j⟩
  obtain ⟨eG, hsG, htG, hfG, hoffG, hoGs, hoGt⟩ := localchart G i j
  obtain ⟨eF, hsF, htF, hfF, hoffF, hoFs, hoFt⟩ := localchart F r l
  let d : PartialEquiv (Euc 2) (Euc 2) := {
    toFun := eF.symm ∘ a ∘ eG
    invFun := eG.symm ∘ a.symm ∘ eF
    source := eG.source ∩ eG ⁻¹' (a ⁻¹' eF.target)
    target := eF.source ∩ eF ⁻¹' (a.symm ⁻¹' eG.target)
    map_source' := by
      intro y hy
      refine ⟨eF.map_target hy.2, ?_⟩
      change a.symm (eF (eF.symm (a (eG y)))) ∈ eG.target
      rw [eF.right_inv hy.2, a.symm_apply_apply]
      exact eG.map_source hy.1
    map_target' := by
      intro y hy
      refine ⟨eG.map_target hy.2, ?_⟩
      change a (eG (eG.symm (a.symm (eF y)))) ∈ eF.target
      rw [eG.right_inv hy.2, a.apply_symm_apply]
      exact eF.map_source hy.1
    left_inv' := by
      intro y hy
      change eG.symm (a.symm (eF (eF.symm (a (eG y))))) = y
      rw [eF.right_inv hy.2, a.symm_apply_apply, eG.left_inv hy.1]
    right_inv' := by
      intro y hy
      change eF.symm (a (eG (eG.symm (a.symm (eF y))))) = y
      rw [eG.right_inv hy.2, a.apply_symm_apply, eF.left_inv hy.1] }
  let T : PartialHomeomorph (Euc 2) (Euc 2) := {
    toPartialEquiv := d
    continuousOn_toFun := eF.symm.continuousOn.comp
      (a.continuous.comp_continuousOn (eG.continuousOn.mono (fun y hy => hy.1)))
      (fun y hy => hy.2)
    continuousOn_invFun := eG.symm.continuousOn.comp
      (a.symm.continuous.comp_continuousOn (eF.continuousOn.mono (fun y hy => hy.1)))
      (fun y hy => hy.2) }
  have hsT : T.source = sectorCrossDomain F G a i j r l := by
    ext y
    change (y ∈ eG.source ∧ a (eG y) ∈ eF.target) ↔ _
    rw [hsG, hfG, htF]
    constructor
    · intro hy
      refine ⟨hy.1, ?_, hy.2⟩
      have hm := eG.map_source (hsG ▸ hy.1)
      rw [hfG] at hm
      exact hoffG _ hm
    · exact fun hy => ⟨hy.1, hy.2.2⟩
  have htT : T.target = sectorCrossDomain G F a.symm r l i j := by
    ext y
    change (y ∈ eF.source ∧ a.symm (eF y) ∈ eG.target) ↔ _
    rw [hsF, hfF, htG]
    constructor
    · intro hy
      refine ⟨hy.1, ?_, hy.2⟩
      have hm := eF.map_source (hsF ▸ hy.1)
      rw [hfF] at hm
      exact hoffF _ hm
    · exact fun hy => ⟨hy.1, hy.2.2⟩
  have hopenS : IsOpen T.source := by
    change IsOpen (eG.source ∩ eG ⁻¹' (a ⁻¹' eF.target))
    apply eG.continuousOn.isOpen_inter_preimage hoGs
    exact hoFt.preimage a.continuous
  have hopenT : IsOpen T.target := by
    change IsOpen (eF.source ∩ eF ⁻¹' (a.symm ⁻¹' eG.target))
    exact eF.continuousOn.isOpen_inter_preimage hoFs (hoGt.preimage a.symm.continuous)
  have hmatch : ∀ y ∈ T.source,
      F.parametrization r (((F.domain r).chart l).map.symm (T y)) =
        a (G.parametrization i (((G.domain i).chart j).map.symm y)) := by
    intro y hy
    change y ∈ eG.source ∧ a (eG y) ∈ eF.target at hy
    rw [← hfF]
    change eF (eF.symm (a (eG y))) = _
    rw [eF.right_inv hy.2, hfG]
  have euclidean_cancel (f : Euc 2 → Euc 3) (t : Euc 2 → Euc 2) (y : Euc 2)
      (hf : ContDiffAt ℝ ∞ f (t y)) (hinj : Function.Injective (fderiv ℝ f (t y)))
      (ht : ContinuousAt t y) (hcomp : ContDiffAt ℝ ∞ (f ∘ t) y) :
      ContDiffAt ℝ ∞ t y := by
    obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
    have hder : HasFDerivAt (L ∘ f)
        (ContinuousLinearEquiv.refl ℝ (Euc 2) : Euc 2 →L[ℝ] Euc 2) (t y) := by
      have h := L.hasFDerivAt.comp (t y) (hf.differentiableAt (by simp)).hasFDerivAt
      have hcomp : L.comp (fderiv ℝ f (t y)) =
          (ContinuousLinearEquiv.refl ℝ (Euc 2) : Euc 2 →L[ℝ] Euc 2) := by
        apply ContinuousLinearMap.ext
        intro w
        exact hL w
      simpa only [hcomp] using h
    have hsm : ContDiffAt ℝ ∞ (L ∘ f) (t y) := L.contDiff.contDiffAt.comp (t y) hf
    have hsmcomp : ContDiffAt ℝ ∞ (L ∘ f ∘ t) y := L.contDiff.contDiffAt.comp y hcomp
    have hinv := hsm.to_localInverse hder (by simp)
    have heq := (hsm.hasStrictFDerivAt' hder (by simp)).eventually_left_inverse
    exact (hinv.comp y hsmcomp).congr_of_eventuallyEq
      (Filter.EventuallyEq.symm (ht.eventually heq))
  have ambient_cancel (f : Euc 2 → M) (t : Euc 2 → Euc 2) (y : Euc 2)
      (hf : ContMDiffAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞ f (t y))
      (hinj : Function.Injective (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) f (t y)))
      (ht : ContinuousAt t y)
      (hcomp : ContMDiffAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞ (f ∘ t) y) :
      ContDiffAt ℝ ∞ t y := by
    let e := extChartAt (𝓡∂ 3) (f (t y))
    let H := e ∘ f
    have hH : ContDiffAt ℝ ∞ H (t y) :=
      ((contMDiffAt_extChartAt (I := 𝓡∂ 3) (x := f (t y)) (n := ∞)).comp (t y) hf).contDiffAt
    have hdH := mfderiv_comp (t y)
      (mdifferentiableAt_extChartAt (I := 𝓡∂ 3)
        (mem_chart_source (EuclideanHalfSpace 3) (f (t y))))
      (hf.mdifferentiableAt (by simp))
    have hHinj : Function.Injective (fderiv ℝ H (t y)) := by
      have hi : Function.Injective (mfderiv 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3) H (t y)) := by
        rw [hdH]
        exact (isInvertible_mfderiv_extChartAt
          (mem_extChartAt_source (I := 𝓡∂ 3) (f (t y)))).injective.comp hinj
      intro v w hvw
      have he : (NormedSpace.fromTangentSpace (𝕜 := ℝ) (t y)).symm v =
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) (t y)).symm w := by
        apply hi
        rw [mfderiv_eq_fderiv]
        simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply] using
          congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (H (t y))).symm hvw
      exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (t y)).symm.injective he
    have hHcomp : ContDiffAt ℝ ∞ (H ∘ t) y :=
      ((contMDiffAt_extChartAt (I := 𝓡∂ 3) (x := f (t y)) (n := ∞)).comp y hcomp).contDiffAt
    exact euclidean_cancel H t y hH hHinj ht hHcomp
  have direction (U : PartialHomeomorph (Euc 2) (Euc 2))
      (ho : IsOpen U.source) (hot : IsOpen U.target) (fA fB : Euc 2 → M)
      (hA : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞ fA U.source)
      (hB : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞ fB U.target)
      (hBi : ∀ y ∈ U.target, Function.Injective (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) fB y))
      (hAB : ∀ y ∈ U.source, fB (U y) = fA y) : ContDiffOn ℝ ∞ U U.source := by
    intro y hy
    have heq : fB ∘ U =ᶠ[𝓝 y] fA := by
      filter_upwards [ho.mem_nhds hy] with z hz
      exact hAB z hz
    apply ContDiffAt.contDiffWithinAt
    exact ambient_cancel fB U y ((hB _ (U.map_source hy)).contMDiffAt
      (hot.mem_nhds (U.map_source hy))) (hBi _ (U.map_source hy))
      ((U.continuousOn y hy).continuousAt (ho.mem_nhds hy))
      (((hA y hy).contMDiffAt (ho.mem_nhds hy)).congr_of_eventuallyEq heq)
  let fG := sectorCoordinateMap (G.map ∘ G.parametrization i) j
  let fF := sectorCoordinateMap (F.map ∘ F.parametrization r) l
  have hsubG : T.source ⊆ interior ((G.domain i).chart j).map.target := by
    intro y hy
    rw [hsT] at hy
    exact hy.1
  have hsubF : T.target ⊆ interior ((F.domain r).chart l).map.target := by
    intro y hy
    rw [htT] at hy
    exact hy.1
  have hiG : ∀ y ∈ T.source, Function.Injective
      (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) fG y) := by
    intro y hy
    have hi := G.piece_differential_injective i j y (interior_subset (hsubG hy))
    rw [mfderivWithin_of_mem_nhds
      (Filter.mem_of_superset (isOpen_interior.mem_nhds (hsubG hy)) interior_subset)] at hi
    exact hi
  have hiF : ∀ y ∈ T.target, Function.Injective
      (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) fF y) := by
    intro y hy
    have hi := F.piece_differential_injective r l y (interior_subset (hsubF hy))
    rw [mfderivWithin_of_mem_nhds
      (Filter.mem_of_superset (isOpen_interior.mem_nhds (hsubF hy)) interior_subset)] at hi
    exact hi
  have hambient : ∀ y ∈ T.source, fF (T y) = fG y := by
    intro y hy
    change F.map (F.parametrization r (((F.domain r).chart l).map.symm (T y))) = _
    rw [hmatch y hy]
    exact ha _
  have hsmooth := direction T hopenS hopenT fG fF
    ((G.piece_smooth_interior i j).mono hsubG)
    ((F.piece_smooth_interior r l).mono hsubF) hiF hambient
  have hinverse := direction T.symm hopenT hopenS fF fG
    ((F.piece_smooth_interior r l).mono hsubF)
    ((G.piece_smooth_interior i j).mono hsubG) hiG (by
      intro y hy
      have he := hambient (T.symm y) (T.map_target hy)
      rw [T.right_inv hy] at he
      exact he.symm)
  have hderiv : ∀ y ∈ T.source, HasFDerivAt T (fderiv ℝ T y) y ∧
      Function.Injective (fderiv ℝ T y) ∧ (fderiv ℝ T y).det ≠ 0 := by
    intro y hy
    have hT := (hsmooth.contDiffAt (hopenS.mem_nhds hy)).differentiableAt (by simp)
    have hU := (hinverse.contDiffAt (hopenT.mem_nhds (T.map_source hy))).differentiableAt (by simp)
    have heq : T.symm ∘ T =ᶠ[𝓝 y] id := by
      filter_upwards [hopenS.mem_nhds hy] with z hz
      exact T.left_inv hz
    have hid := (hU.hasFDerivAt.comp y hT.hasFDerivAt).congr_of_eventuallyEq heq.symm
    have hlin := hid.fderiv
    rw [fderiv_id] at hlin
    have hi : Function.Injective (fderiv ℝ T y) := by
      intro v w hvw
      have he := congrArg (fderiv ℝ T.symm (T y)) hvw
      have hv := congrArg (fun L : Euc 2 →L[ℝ] Euc 2 => L v) hlin
      have hw := congrArg (fun L : Euc 2 →L[ℝ] Euc 2 => L w) hlin
      exact hv.trans (he.trans hw.symm)
    refine ⟨hT.hasFDerivAt, hi, ?_⟩
    intro hzero
    have hbot := LinearMap.bot_lt_ker_of_det_eq_zero (f := (fderiv ℝ T y).toLinearMap) hzero
    rw [LinearMap.ker_eq_bot.2 hi] at hbot
    exact lt_irrefl _ hbot
  exact ⟨⟨T, hsT, htT, hopenS, hopenT, hmatch, hsmooth, hinverse,
    fun y hy => (hderiv y hy).2.1, fun y hy => (hderiv y hy).2.2⟩⟩

theorem sector_same_image_ambient_factor {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (a : R ≃ₜ S) (ha : ∀ x, F.map (a x) = G.map x)
    (hb : a ⁻¹' S.boundary = R.boundary)
    (i : Fin G.pieceCount) (j : Fin (G.domain i).count)
    (r : Fin F.pieceCount) (l : Fin (F.domain r).count)
    (T : SectorImageTransition F G a i j r l) (y : Euc 2) (hy : y ∈ T.coordinate.source) :
    let fG := sectorCoordinateMap (G.map ∘ G.parametrization i) j
    let fF := sectorCoordinateMap (F.map ∘ F.parametrization r) l
    ∃ hpoint : fF (T.coordinate y) = fG y,
      ∀ w : Euc 2,
        mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fG ((G.domain i).chart j).map.target y
          ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm w) =
        imageTangentTransport hpoint
          (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fF ((F.domain r).chart l).map.target
            (T.coordinate y) ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) (T.coordinate y)).symm
              (fderiv ℝ T.coordinate y w))) := by
  let fG := sectorCoordinateMap (G.map ∘ G.parametrization i) j
  let fF := sectorCoordinateMap (F.map ∘ F.parametrization r) l
  have hmatch : ∀ z ∈ T.coordinate.source, fF (T.coordinate z) = fG z := by
    intro z hz
    change F.map (F.parametrization r (((F.domain r).chart l).map.symm (T.coordinate z))) =
      G.map (G.parametrization i (((G.domain i).chart j).map.symm z))
    rw [T.parametrization_matches z hz]
    exact ha _
  have hG : y ∈ interior ((G.domain i).chart j).map.target := by
    have hs := hy
    rw [T.source_eq] at hs
    exact hs.1
  have hF : T.coordinate y ∈ interior ((F.domain r).chart l).map.target := by
    have ht := T.coordinate.map_source hy
    rw [T.target_eq] at ht
    exact ht.1
  have hdF : MDifferentiableAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) fF (T.coordinate y) := by
    exact ((F.piece_smooth_interior r l).mdifferentiableOn (by simp)) _ hF
      |>.mdifferentiableAt (isOpen_interior.mem_nhds hF)
  have hdT : MDifferentiableAt 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 2) T.coordinate y := by
    exact (T.smooth.contDiffAt (T.open_source.mem_nhds hy)).differentiableAt (by simp)
      |>.mdifferentiableAt
  have heq : fG =ᶠ[𝓝 y] fF ∘ T.coordinate := by
    filter_upwards [T.open_source.mem_nhds hy] with z hz
    exact (hmatch z hz).symm
  refine ⟨hmatch y hy, ?_⟩
  intro w
  have hder := heq.mfderiv_eq (I := 𝓘(ℝ, Euc 2)) (I' := 𝓡∂ 3)
  have hcomp := mfderiv_comp y hdF hdT
  rw [mfderivWithin_of_mem_nhds (Filter.mem_of_superset (isOpen_interior.mem_nhds hG)
    interior_subset), mfderivWithin_of_mem_nhds
    (Filter.mem_of_superset (isOpen_interior.mem_nhds hF) interior_subset)]
  change mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) fG y w =
    imageTangentTransport (hmatch y hy)
      (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) fF (T.coordinate y)
        (fderiv ℝ T.coordinate y w))
  have happ := congrArg (fun L : Euc 2 →L[ℝ] Euc 3 => L w) hder
  rw [hcomp, mfderiv_eq_fderiv] at happ
  have htransport : ∀ {x z : M} (hx : x = z) (v : TangentSpace (𝓡∂ 3) x),
      @Eq (Euc 3) (imageTangentTransport hx v) v := by
    intro x z hx v
    cases hx
    rfl
  exact happ.trans (htransport (hmatch y hy) _).symm

theorem sector_same_image_density_integral_transport {S R : CompactOrientedSurface.{u}}
    (g : SmoothMetric M) (F : GeometricPiecewiseSurface S M)
    (G : GeometricPiecewiseSurface R M) (a : R ≃ₜ S)
    (ha : ∀ x, F.map (a x) = G.map x) (hb : a ⁻¹' S.boundary = R.boundary)
    (i : Fin G.pieceCount) (j : Fin (G.domain i).count)
    (r : Fin F.pieceCount) (l : Fin (F.domain r).count)
    (T : SectorImageTransition F G a i j r l) (s : Set (Euc 2))
    (hs : MeasurableSet s) (hsub : s ⊆ T.coordinate.source) :
    (∀ y ∈ s, sectorCoordinateDensity g (G.map ∘ G.parametrization i) j y =
      |(fderiv ℝ T.coordinate y).det| *
        sectorCoordinateDensity g (F.map ∘ F.parametrization r) l (T.coordinate y)) ∧
    IntegrableOn (sectorCoordinateDensity g (G.map ∘ G.parametrization i) j) s ∧
    IntegrableOn (sectorCoordinateDensity g (F.map ∘ F.parametrization r) l)
      (T.coordinate '' s) ∧
    (∫ y in s, sectorCoordinateDensity g (G.map ∘ G.parametrization i) j y) =
      (∫ y in T.coordinate '' s,
        sectorCoordinateDensity g (F.map ∘ F.parametrization r) l y) := by
  have covariance : ∀ y ∈ s, sectorCoordinateDensity g (G.map ∘ G.parametrization i) j y =
      |(fderiv ℝ T.coordinate y).det| *
        sectorCoordinateDensity g (F.map ∘ F.parametrization r) l (T.coordinate y) := by
    open Bundle in
    intro y hy
    obtain ⟨hpoint, hder⟩ := sector_same_image_ambient_factor F G a ha hb i j r l T y (hsub hy)
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) := ⟨g.toRiemannianMetric⟩
    let fG := sectorCoordinateMap (G.map ∘ G.parametrization i) j
    let fF := sectorCoordinateMap (F.map ∘ F.parametrization r) l
    let dG := (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fG
      ((G.domain i).chart j).map.target y).toLinearMap.comp
        (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm.toLinearMap
    let dF := (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fF
      ((F.domain r).chart l).map.target (T.coordinate y)).toLinearMap.comp
        (tangentSpaceCastModel 𝓘(ℝ, Euc 2) (T.coordinate y)).symm.toLinearMap
    have density {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
        (d : Euc 2 →ₗ[ℝ] V) :
        Real.sqrt (Matrix.gram ℝ (fun k : Fin 2 => d (EuclideanSpace.single k 1))).det =
          (d.normDet : ℝ) := by
      have hd := d.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin 2) ℝ)
      simp only [EuclideanSpace.basisFun_apply] at hd
      rw [← hd]
      exact Real.sqrt_sq (by exact d.normDet_nonneg)
    change Real.sqrt (Matrix.gram ℝ (fun k : Fin 2 => dG (EuclideanSpace.single k 1))).det =
      |(fderiv ℝ T.coordinate y).det| *
        Real.sqrt (Matrix.gram ℝ (fun k : Fin 2 => dF (EuclideanSpace.single k 1))).det
    have hdensityG := density (V := TangentSpace (𝓡∂ 3) (fG y)) dG
    have hdensityF := density (V := TangentSpace (𝓡∂ 3) (fF (T.coordinate y))) dF
    rw [hdensityG, hdensityF]
    have factor : ∀ (x z : M) (hp : x = z)
        (dG : Euc 2 →ₗ[ℝ] TangentSpace (𝓡∂ 3) z)
        (dF : Euc 2 →ₗ[ℝ] TangentSpace (𝓡∂ 3) x)
        (A : Euc 2 →ₗ[ℝ] Euc 2),
        (∀ w, dG w = imageTangentTransport hp (dF (A w))) →
        (dG.normDet : ℝ) = |A.det| * (dF.normDet : ℝ) := by
      intro x z hp
      cases hp
      intro dG dF A hd
      have hm : dG = dF.comp A := by
        ext w
        exact hd w
      rw [hm, LinearMap.normDet_comp_of_finrank_eq A dF rfl,
        LinearMap.normDet_eq_abs_det]
      simp only [mul_comm]
    exact factor _ _ hpoint dG dF (fderiv ℝ T.coordinate y).toLinearMap hder
  refine ⟨covariance, ?_⟩
  have hderivative : ∀ y ∈ s, HasFDerivWithinAt T.coordinate
      (fderiv ℝ T.coordinate y) s y := by
    intro y hy
    exact ((T.smooth.contDiffAt (T.open_source.mem_nhds (hsub hy))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hinjective : InjOn T.coordinate s := T.coordinate.injOn.mono hsub
  have weighted_integrable : IntegrableOn
      (fun y => |(fderiv ℝ T.coordinate y).det| •
        sectorCoordinateDensity g (F.map ∘ F.parametrization r) l (T.coordinate y)) s := by
    obtain ⟨n, Q, b, p, hemb, hsource, hcover, hsmooth, hrank, hinterior⟩ :=
      SeifertSurfaces.OriginalEndpoints.sector_corner_chart_cover_exists (G.domain i)
    have hcompact : ∀ k, IsCompact (Set.range (p k)) :=
      fun k => isCompact_range (p k).continuous
    have hc1 : ∀ k, ContMDiff CornerModel (𝓡∂ 3) 1
        (G.map ∘ G.parametrization i ∘ p k) := by
      intro k
      have hcoordinate : ContMDiff CornerModel 𝓘(ℝ, Euc 2) 1
          (((G.domain i).chart (b k)).map ∘ p k) := (hsmooth k).of_le (by simp)
      have hcomp := (G.piece_c1 i (b k)).comp_contMDiff hcoordinate
        (fun x => ((G.domain i).chart (b k)).map.map_source (hsource k (mem_univ x)))
      apply hcomp.congr
      intro x
      change G.map (G.parametrization i (p k x)) = G.map (G.parametrization i
        (((G.domain i).chart (b k)).map.symm (((G.domain i).chart (b k)).map (p k x))))
      rw [((G.domain i).chart (b k)).map.left_inv (hsource k (mem_univ x))]
    have hregular : ∀ k x, x ∈ CornerModel.interior (Q k) → Function.Injective
        (mfderiv CornerModel (𝓡∂ 3) (G.map ∘ G.parametrization i ∘ p k) x) := by
      intro k x hx
      let q := ((G.domain i).chart (b k)).map ∘ p k
      let H := sectorCoordinateMap (G.map ∘ G.parametrization i) (b k)
      have hy : q x ∈ interior ((G.domain i).chart (b k)).map.target := hinterior k hx
      have hdH : MDifferentiableAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) H (q x) :=
        ((G.piece_smooth_interior i (b k)).mdifferentiableOn (by simp) _ hy).mdifferentiableAt
          (isOpen_interior.mem_nhds hy)
      have hqinjection : Function.Injective (mfderiv CornerModel 𝓘(ℝ, Euc 2) q x) := hrank k x
      have hHinjection : Function.Injective (mfderiv 𝓘(ℝ, Euc 2) (𝓡∂ 3) H (q x)) := by
        have hh := G.piece_differential_injective i (b k) (q x) (interior_subset hy)
        rw [mfderivWithin_of_mem_nhds
          (Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)] at hh
        exact hh
      have heq : G.map ∘ G.parametrization i ∘ p k = H ∘ q := by
        funext z
        change G.map (G.parametrization i (p k z)) = G.map (G.parametrization i
          (((G.domain i).chart (b k)).map.symm (((G.domain i).chart (b k)).map (p k z))))
        rw [((G.domain i).chart (b k)).map.left_inv (hsource k (mem_univ z))]
      rw [heq, mfderiv_comp x hdH ((hsmooth k).mdifferentiableAt (by simp))]
      exact hHinjection.comp hqinjection
    have hbounded : ∀ k, IntegrableOn
        (sectorCoordinateDensity g (G.map ∘ G.parametrization i) (b k))
        (Set.range (((G.domain i).chart (b k)).map ∘ p k)) := by
      open Bundle in
      intro k
      let q := ((G.domain i).chart (b k)).map ∘ p k
      let K := Set.range q
      have hf := G.piece_c1 i (b k)
      let H := sectorCoordinateMap (G.map ∘ G.parametrization i) (b k)
      have hK : IsCompact K := isCompact_range (hsmooth k).continuous
      have hsub : K ⊆ ((G.domain i).chart (b k)).map.target := by
        rintro _ ⟨x, rfl⟩
        exact ((G.domain i).chart (b k)).map.map_source (hsource k (mem_univ x))
      have hsurj : ∀ x, Function.Surjective (mfderiv CornerModel 𝓘(ℝ, Euc 2) q x) := by
        intro x
        exact LinearMap.surjective_of_injective (hrank k x)
      have hu : UniqueMDiffOn 𝓘(ℝ, Euc 2) K := by
        simpa only [image_univ] using
          (uniqueMDiffOn_univ (I := CornerModel)).image_denseRange'
            (fun x _ => ((hsmooth k).mdifferentiableAt (by simp)).hasMFDerivAt.hasMFDerivWithinAt)
            (fun x _ => (hsurj x).denseRange)
      have hd := hf.mono hsub
      have ht := hd.continuousOn_tangentMapWithin (by simp) hu
      have hder : ∀ y ∈ K, mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) H
          ((G.domain i).chart (b k)).map.target y = mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) H K y := by
        intro y hy
        exact (((hf.mdifferentiableOn (by simp)) y (hsub hy)).mfderivWithin_mono (hu y hy) hsub).symm
      have hv (d : Fin 2) : ContinuousOn (fun y =>
          (⟨H y, mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) H K y
            ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single d 1))⟩ :
              TangentBundle (𝓡∂ 3) M)) K := by
        exact ht.comp ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, Euc 2)).symm.continuous.comp
          (continuous_id.prodMk continuous_const)).continuousOn (fun y hy => hy)
      letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) := ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle (Euc 3) (fun x : M => TangentSpace (𝓡∂ 3) x) :=
        ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
      have hgram : ∀ d l : Fin 2, ContinuousOn (fun y => sectorCoordinateGram g (G.map ∘ G.parametrization i) (b k) y d l) K := by
        intro d l
        apply ((hv d).inner_bundle (hv l)).congr
        intro y hy
        change g.inner (H y)
          (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) H ((G.domain i).chart (b k)).map.target y (EuclideanSpace.single d 1))
          (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) H ((G.domain i).chart (b k)).map.target y (EuclideanSpace.single l 1)) =
          g.inner (H y)
          (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) H K y (EuclideanSpace.single d 1))
          (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) H K y (EuclideanSpace.single l 1))
        rw [hder y hy]
      have hdensity : ContinuousOn (sectorCoordinateDensity g (G.map ∘ G.parametrization i) (b k)) K := by
        apply ContinuousOn.sqrt
        exact continuous_id.matrix_det.comp_continuousOn (continuousOn_pi.mpr
          (fun d => continuousOn_pi.mpr (fun l => hgram d l)))
      exact hdensity.integrableOn_compact hK
    let a := ((G.domain i).chart j).map
    let V := fun k : Fin n => a '' (Set.range (p k) ∩ a.source)
    have hlocal : ∀ k, IntegrableOn
        (sectorCoordinateDensity g (G.map ∘ G.parametrization i) j) (s ∩ V k) := by
      intro k
      let B := ((G.domain i).chart (b k)).map
      let U := s ∩ V k
      let t := B ∘ a.symm
      let D := interior a.target ∩ a.symm ⁻¹' B.source
      have hU : MeasurableSet U := by
        letI : BorelSpace (G.domain i) := ⟨rfl⟩
        letI : MetricSpace (G.domain i) := TopologicalSpace.metrizableSpaceMetric (G.domain i)
        have hm : MeasurableSet (Set.range (p k) ∩ a.source) :=
          (hcompact k).isClosed.measurableSet.inter ((G.domain i).chart j).source_open.measurableSet
        exact hs.inter (hm.image_of_continuousOn_injOn
          (a.continuousOn.mono inter_subset_right) (a.injOn.mono inter_subset_right))
      have hopen : IsOpen D :=
        (a.symm.continuousOn.mono interior_subset).isOpen_inter_preimage
          isOpen_interior ((G.domain i).chart (b k)).source_open
      have hsubD : U ⊆ D := by
        intro y hy
        have hiy := hsub hy.1
        rw [T.source_eq] at hiy
        refine ⟨hiy.1, ?_⟩
        obtain ⟨z, ⟨⟨x, rfl⟩, hz⟩, he⟩ := hy.2
        change a.symm y ∈ B.source
        rw [← he, a.left_inv hz]
        exact hsource k (mem_univ x)
      have hsmoothT : ContDiffOn ℝ ∞ t D := (G.domain i).transition_smooth_interior j (b k)
      have hmaps : MapsTo t D (interior B.target) := by
        intro y hy
        rw [← AreaCertificates.sector_chart_piece_interior (G.domain i) (b k)]
        refine ⟨a.symm y, ⟨?_, hy.2⟩, rfl⟩
        exact (AreaCertificates.sector_chart_inverse_interior (G.domain i) j hy.1).1
      have hinj : InjOn t U := by
        intro x hx y hy hxy
        apply a.symm.injOn (interior_subset (hsubD hx).1) (interior_subset (hsubD hy).1)
        exact B.injOn (hsubD hx).2 (hsubD hy).2 hxy
      have hdt : ∀ y ∈ U, HasFDerivWithinAt t (fderiv ℝ t y) U y :=
        fun y hy => ((hsmoothT.contDiffAt (hopen.mem_nhds (hsubD hy))).differentiableAt
          (by simp)).hasFDerivAt.hasFDerivWithinAt
      have himage : t '' U ⊆ Set.range (B ∘ p k) := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨z, ⟨⟨x, rfl⟩, hz⟩, he⟩ := hy.2
        refine ⟨x, ?_⟩
        change B (p k x) = B (a.symm y)
        rw [← he, a.left_inv hz]
      have hcov : ∀ y ∈ U,
          sectorCoordinateDensity g (G.map ∘ G.parametrization i) j y =
          |(fderiv ℝ t y).det| •
            sectorCoordinateDensity g (G.map ∘ G.parametrization i) (b k) (t y) := by
        open Bundle in
        intro y hy
        let fA := sectorCoordinateMap (G.map ∘ G.parametrization i) j
        let fB := sectorCoordinateMap (G.map ∘ G.parametrization i) (b k)
        have hmatch : ∀ z ∈ D, fB (t z) = fA z := by
          intro z hz
          change G.map (G.parametrization i (B.symm (B (a.symm z)))) = _
          rw [B.left_inv hz.2]
          rfl
        have heq : fA =ᶠ[𝓝 y] fB ∘ t := by
          filter_upwards [hopen.mem_nhds (hsubD hy)] with z hz
          exact (hmatch z hz).symm
        have hiy : y ∈ interior a.target := (hsubD hy).1
        have hty : t y ∈ interior B.target := hmaps (hsubD hy)
        have hdB : MDifferentiableAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) fB (t y) :=
          ((G.piece_smooth_interior i (b k)).mdifferentiableOn (by simp) _ hty).mdifferentiableAt
            (isOpen_interior.mem_nhds hty)
        have hdtAt : MDifferentiableAt 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 2) t y :=
          (hsmoothT.contDiffAt (hopen.mem_nhds (hsubD hy))).differentiableAt (by simp)
            |>.mdifferentiableAt
        have hder : ∀ w : Euc 2, @Eq (Euc 3)
            (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fA a.target y w)
            (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fB B.target (t y) (fderiv ℝ t y w)) := by
          intro w
          rw [mfderivWithin_of_mem_nhds
            (Filter.mem_of_superset (isOpen_interior.mem_nhds hiy) interior_subset),
            mfderivWithin_of_mem_nhds
            (Filter.mem_of_superset (isOpen_interior.mem_nhds hty) interior_subset)]
          have hd := congrArg (fun L : Euc 2 →L[ℝ] Euc 3 => L w)
            (heq.mfderiv_eq (I := 𝓘(ℝ, Euc 2)) (I' := 𝓡∂ 3))
          rw [mfderiv_comp y hdB hdtAt, mfderiv_eq_fderiv] at hd
          exact hd
        letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) := ⟨g.toRiemannianMetric⟩
        let dA := (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fA a.target y).toLinearMap.comp
          (tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm.toLinearMap
        let dB := (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) fB B.target (t y)).toLinearMap.comp
          (tangentSpaceCastModel 𝓘(ℝ, Euc 2) (t y)).symm.toLinearMap
        have density {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
            (d : Euc 2 →ₗ[ℝ] V) :
            Real.sqrt (Matrix.gram ℝ (fun z : Fin 2 => d (EuclideanSpace.single z 1))).det =
              (d.normDet : ℝ) := by
          have hd := d.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin 2) ℝ)
          simp only [EuclideanSpace.basisFun_apply] at hd
          rw [← hd]
          exact Real.sqrt_sq d.normDet_nonneg
        change Real.sqrt (Matrix.gram ℝ (fun z : Fin 2 => dA (EuclideanSpace.single z 1))).det =
          |(fderiv ℝ t y).det| *
          Real.sqrt (Matrix.gram ℝ (fun z : Fin 2 => dB (EuclideanSpace.single z 1))).det
        rw [density dA, density dB]
        have factor : ∀ (x z : M) (hp : x = z)
            (dA : Euc 2 →ₗ[ℝ] TangentSpace (𝓡∂ 3) z)
            (dB : Euc 2 →ₗ[ℝ] TangentSpace (𝓡∂ 3) x)
            (L : Euc 2 →ₗ[ℝ] Euc 2),
            (∀ w, @Eq (Euc 3) (dA w) (dB (L w))) →
            (dA.normDet : ℝ) = |L.det| * (dB.normDet : ℝ) := by
          intro x z hp
          cases hp
          intro dA dB L hd
          have he : dA = dB.comp L := by
            ext w
            exact hd w
          rw [he, LinearMap.normDet_comp_of_finrank_eq L dB rfl,
            LinearMap.normDet_eq_abs_det]
          exact mul_comm _ _
        exact factor _ _ (hmatch y (hsubD hy)) dA dB (fderiv ℝ t y).toLinearMap hder
      have hw := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
        hU hdt hinj (sectorCoordinateDensity g (G.map ∘ G.parametrization i) (b k))).1
          ((hbounded k).mono_set himage)
      exact hw.congr_fun (fun y hy => (hcov y hy).symm) hU
    have hsplit : s = ⋃ k, s ∩ V k := by
      apply Subset.antisymm
      · intro y hy
        have ht : y ∈ a.target := by
          have hd := hsub hy
          rw [T.source_eq] at hd
          exact interior_subset hd.1
        have hx : a.symm y ∈ ⋃ k, Set.range (p k) := by rw [hcover]; trivial
        obtain ⟨k, hk⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨k, hy, a.symm y, ⟨hk, a.map_target ht⟩, a.right_inv ht⟩
      · intro y hy
        obtain ⟨_, hk⟩ := mem_iUnion.mp hy
        exact hk.1
    have hG : IntegrableOn (sectorCoordinateDensity g (G.map ∘ G.parametrization i) j) s := by
      rw [hsplit]
      exact integrableOn_finite_iUnion.mpr (fun k => hlocal k)
    exact hG.congr_fun covariance hs
  have hGintegrable : IntegrableOn
      (sectorCoordinateDensity g (G.map ∘ G.parametrization i) j) s :=
    weighted_integrable.congr_fun (fun y hy => (covariance y hy).symm) hs
  have hFintegrable := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume hs hderivative hinjective
      (sectorCoordinateDensity g (F.map ∘ F.parametrization r) l)).2 weighted_integrable
  refine ⟨hGintegrable, hFintegrable, ?_⟩
  calc
    (∫ y in s, sectorCoordinateDensity g (G.map ∘ G.parametrization i) j y) =
        ∫ y in s, |(fderiv ℝ T.coordinate y).det| •
          sectorCoordinateDensity g (F.map ∘ F.parametrization r) l (T.coordinate y) :=
      setIntegral_congr_fun hs covariance
    _ = ∫ y in T.coordinate '' s,
        sectorCoordinateDensity g (F.map ∘ F.parametrization r) l y :=
      (integral_image_eq_integral_abs_det_fderiv_smul volume hs hderivative hinjective
        (sectorCoordinateDensity g (F.map ∘ F.parametrization r) l)).symm
end
end SeifertSurfaces.MetricFoundations.B1Bridges
