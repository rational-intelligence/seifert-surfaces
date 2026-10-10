import MetricAreaGeometryDefinitions
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.SpecialFunctions.PolarCoord

set_option maxSynthPendingDepth 3
set_option autoImplicit false
open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle
namespace SeifertSurfaces.MetricFoundations.AreaCertificates
open Foundations AreaAnalysis
universe u v
noncomputable section

theorem planar_sector_closed (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) :
    IsClosed (planarSector θ) := by
  have hunit (t : ℝ) : ‖sectorUnit t‖ = 1 := by
    have hs : ‖sectorUnit t‖ ^ 2 = 1 := by
      simp only [EuclideanSpace.real_norm_sq_eq, sectorUnit, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
      exact Real.cos_sq_add_sin_sq t
    nlinarith [norm_nonneg (sectorUnit t)]
  letI : CompactSpace (Icc (0 : ℝ) θ) := isCompact_iff_compactSpace.mp isCompact_Icc
  let B : Set (Euc 2 × Icc (0 : ℝ) θ) :=
    {p | p.1 = ‖p.1‖ • sectorUnit p.2}
  have hB : IsClosed B := by
    apply isClosed_eq continuous_fst
    apply Continuous.smul continuous_fst.norm
    unfold sectorUnit
    fun_prop
  have heq : planarSector θ = Prod.fst '' B := by
    ext x
    constructor
    · rintro ⟨r, hr, t, ht, hxt⟩
      refine ⟨⟨x, ⟨t, ht⟩⟩, ?_, rfl⟩
      change x = ‖x‖ • sectorUnit t
      rw [hxt, norm_smul, hunit, Real.norm_of_nonneg hr, mul_one]
    · rintro ⟨⟨z, t⟩, hz, rfl⟩
      exact ⟨‖z‖, norm_nonneg z, t, t.property, hz⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ hB

theorem sector_boundary_rays_closed (θ : ℝ) : IsClosed (sectorBoundary θ) := by
  have heq : sectorBoundary θ =
      ((fun r : ℝ => r • sectorUnit 0) '' Ici 0) ∪
        ((fun r : ℝ => r • sectorUnit θ) '' Ici 0) := by
    ext x
    simp only [sectorBoundary, mem_setOf_eq, mem_union, mem_image, mem_Ici]
    constructor
    · rintro ⟨r, hr, hx | hx⟩
      · exact Or.inl ⟨r, hr, hx.symm⟩
      · exact Or.inr ⟨r, hr, hx.symm⟩
    · rintro (⟨r, hr, hx⟩ | ⟨r, hr, hx⟩)
      · exact ⟨r, hr, Or.inl hx.symm⟩
      · exact ⟨r, hr, Or.inr hx.symm⟩
  rw [heq]
  exact ((isClosedMap_smul_left (sectorUnit 0)) _ isClosed_Ici).union
    ((isClosedMap_smul_left (sectorUnit θ)) _ isClosed_Ici)

/-- The exact open polar sector; openings above pi are retained. -/
theorem planar_sector_interior_polar (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) :
    interior (planarSector θ) =
      {x | ∃ r : ℝ, 0 < r ∧ ∃ t ∈ Ioo (0 : ℝ) θ, x = r • sectorUnit t} := by
  let d : Euc 2 ≃ₜ ℂ :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).toHomeomorph.trans
      (Homeomorph.piFinTwo (fun _ : Fin 2 => ℝ))).trans
      Complex.equivRealProdCLM.symm.toHomeomorph
  let rot := d.trans (Homeomorph.mulLeft₀
    (Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I)) (Complex.exp_ne_zero _))
  let P := rot.transOpenPartialHomeomorph Complex.polarCoord
  have hinv (r t : ℝ) : P.symm (r, t) = r • sectorUnit (t + θ / 2) := by
    apply d.injective
    change (Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I))⁻¹ *
      Complex.polarCoord.symm (r, t) = d (r • sectorUnit (t + θ / 2))
    rw [← Complex.exp_neg]
    have hn : -(-((θ / 2 : ℝ) : ℂ) * Complex.I) = ((θ / 2 : ℝ) : ℂ) * Complex.I := by ring
    rw [hn, Complex.exp_mul_I, Complex.polarCoord_symm_apply]
    simp [d, sectorUnit, Homeomorph.piFinTwo, Real.cos_add, Real.sin_add,
      Complex.equivRealProdCLM_symm_apply, Complex.ofReal_add, Complex.ofReal_mul]
    ring_nf
    simp [Complex.I_sq]
    ring
  have htarget : P.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := by
    simp [P, Homeomorph.transOpenPartialHomeomorph, Complex.polarCoord_target]
  let W := Ioi (0 : ℝ) ×ˢ Icc (-θ / 2) (θ / 2)
  have hWP : W ⊆ P.target := by
    rintro ⟨r, t⟩ ⟨hr, ht⟩
    dsimp at hr ht
    rw [htarget]
    exact ⟨hr, by constructor <;> linarith [ht.1, ht.2, Real.pi_pos]⟩
  have hnonzero : planarSector θ \ {0} = P.symm '' W := by
    ext x
    constructor
    · rintro ⟨⟨r, hr, t, ht, hxt⟩, hx⟩
      have hrp : 0 < r := by
        apply lt_of_le_of_ne hr
        intro he
        apply hx
        simp only [mem_singleton_iff]
        rw [hxt, ← he, zero_smul]
      refine ⟨(r, t - θ / 2), ⟨hrp, by constructor <;> linarith [ht.1, ht.2]⟩, ?_⟩
      rw [hinv]
      have he : t - θ / 2 + θ / 2 = t := by ring
      rw [he, ← hxt]
    · rintro ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩
      dsimp at hr ht
      rw [hinv]
      refine ⟨⟨r, hr.le, t + θ / 2, by constructor <;> linarith [ht.1, ht.2], rfl⟩, ?_⟩
      intro he
      have hz : r • sectorUnit (t + θ / 2) = 0 := mem_singleton_iff.mp he
      have hn := congrArg (fun z : Euc 2 => ‖z‖ ^ 2) hz
      simp only [norm_smul, Real.norm_of_nonneg hr.le, norm_zero, zero_pow (by decide : 2 ≠ 0),
        mul_pow, EuclideanSpace.real_norm_sq_eq, sectorUnit, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one] at hn
      rw [Real.cos_sq_add_sin_sq, mul_one] at hn
      nlinarith [show 0 < r from hr]
  have hinter : interior (P.symm '' W) = P.symm '' (Ioi (0 : ℝ) ×ˢ Ioo (-θ / 2) (θ / 2)) := by
    have him : P.symm.IsImage W (P.symm '' W) := by
      intro z hz
      constructor
      · rintro ⟨w, hw, he⟩
        exact (P.symm.injOn (hWP hw) hz he) ▸ hw
      · intro hw
        exact ⟨z, hw, rfl⟩
    have hs : P.symm '' W ⊆ P.source := by
      rintro z ⟨w, hw, rfl⟩
      exact P.map_target (hWP hw)
    have hi := him.interior.image_eq
    rw [P.symm_source, P.symm_target,
      inter_eq_right.mpr (interior_subset.trans hWP),
      inter_eq_right.mpr (interior_subset.trans hs)] at hi
    rw [← hi]
    simp only [W, interior_prod_eq, isOpen_Ioi.interior_eq, interior_Icc]
  have hzero : (0 : Euc 2) ∉ interior (planarSector θ) := by
    have hu (t : ℝ) : ‖sectorUnit t‖ = 1 := by
      have hh : ‖sectorUnit t‖ ^ 2 = 1 := by
        simp only [EuclideanSpace.real_norm_sq_eq, sectorUnit, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        exact Real.cos_sq_add_sin_sq t
      nlinarith [norm_nonneg (sectorUnit t)]
    intro h
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h)
    let z := P.symm (-ε / 2, 0)
    have hznorm : ‖z‖ = ε / 2 := by
      change ‖P.symm (-ε / 2, 0)‖ = _
      rw [hinv, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_neg (by linarith)]
      ring
    have hzS : z ∈ planarSector θ := hball (by
      simp only [Metric.mem_ball, dist_zero_right, hznorm]
      linarith)
    have hz0 : z ∉ ({0} : Set (Euc 2)) := by
      intro hz
      have hh := congrArg norm (mem_singleton_iff.mp hz)
      rw [hznorm, norm_zero] at hh
      linarith
    have hzP : z ∈ P.source := by
      have hh : z ∈ planarSector θ \ {0} := ⟨hzS, hz0⟩
      rw [hnonzero] at hh
      obtain ⟨w, hw, hew⟩ := hh
      exact hew ▸ P.map_target (hWP hw)
    change rot z ∈ Complex.slitPlane at hzP
    have he : rot z = Complex.polarCoord.symm (-ε / 2, 0) := rot.apply_symm_apply _
    rw [he, Complex.polarCoord_symm_apply] at hzP
    simp only [Real.cos_zero, Real.sin_zero, Complex.ofReal_zero, Complex.ofReal_one,
      zero_mul, add_zero, mul_one, Complex.mem_slitPlane_iff,
      Complex.ofReal_re, Complex.ofReal_im, ne_self_iff_false, or_false] at hzP
    linarith
  have hintereq : interior (planarSector θ) = interior (planarSector θ \ {0}) := by
    apply subset_antisymm
    · exact interior_maximal (fun x hx => ⟨interior_subset hx, fun he =>
        hzero (mem_singleton_iff.mp he ▸ hx)⟩) isOpen_interior
    · exact interior_mono diff_subset
  rw [hintereq, hnonzero, hinter]
  ext x
  constructor
  · rintro ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩
    exact ⟨r, hr, t + θ / 2, by constructor <;> linarith [ht.1, ht.2], hinv r t⟩
  · rintro ⟨r, hr, t, ht, hxt⟩
    refine ⟨(r, t - θ / 2), ⟨hr, by constructor <;> linarith [ht.1, ht.2]⟩, ?_⟩
    rw [hinv]
    have he : t - θ / 2 + θ / 2 = t := by ring
    rw [he, ← hxt]

theorem planar_sector_boundary_complement (θ : ℝ)
    (hθ : 0 < θ) (hθπ : θ < 2 * Real.pi) :
    planarSector θ \ sectorBoundary θ = interior (planarSector θ) := by
  rw [planar_sector_interior_polar θ hθ hθπ]
  have hunit (t : ℝ) : ‖sectorUnit t‖ = 1 := by
    have hs : ‖sectorUnit t‖ ^ 2 = 1 := by
      simp only [EuclideanSpace.real_norm_sq_eq, sectorUnit, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      exact Real.cos_sq_add_sin_sq t
    nlinarith [norm_nonneg (sectorUnit t)]
  have hinj : InjOn sectorUnit (Icc (0 : ℝ) θ) := by
    intro t ht s hs he
    apply Circle.exp_injOn_Icc (by simpa using hθπ) ht hs
    apply Subtype.ext
    have hc := congrArg (fun z : Euc 2 => z 0) he
    have hs' := congrArg (fun z : Euc 2 => z 1) he
    simp only [sectorUnit, Matrix.cons_val_zero, Matrix.cons_val_one] at hc hs'
    change Complex.exp ((t : ℂ) * Complex.I) = Complex.exp ((s : ℂ) * Complex.I)
    simp only [Complex.exp_mul_I]
    norm_cast
    rw [hc, hs']
  ext x
  constructor
  · rintro ⟨⟨r, hr, t, ht, hxt⟩, hxb⟩
    have hrp : 0 < r := by
      apply lt_of_le_of_ne hr
      intro he
      exact hxb ⟨0, le_rfl, Or.inl (by rw [hxt, ← he, zero_smul, zero_smul])⟩
    have ht0 : t ≠ 0 := by
      intro he
      exact hxb ⟨r, hr, Or.inl (by rwa [he] at hxt)⟩
    have htθ : t ≠ θ := by
      intro he
      exact hxb ⟨r, hr, Or.inr (by rwa [he] at hxt)⟩
    exact ⟨r, hrp, t, ⟨lt_of_le_of_ne ht.1 ht0.symm, lt_of_le_of_ne ht.2 htθ⟩, hxt⟩
  · rintro ⟨r, hr, t, ht, hxt⟩
    refine ⟨⟨r, hr.le, t, ⟨ht.1.le, ht.2.le⟩, hxt⟩, ?_⟩
    rintro ⟨s, hs, he0 | heθ⟩
    · have hrs : r = s := by
        have hn := congrArg norm (hxt.symm.trans he0)
        simpa only [norm_smul, hunit, Real.norm_of_nonneg hr.le,
          Real.norm_of_nonneg hs, mul_one] using hn
      have hu : sectorUnit t = sectorUnit 0 := by
        apply (smul_right_injective (Euc 2) (ne_of_gt hr))
        simpa only [hrs] using hxt.symm.trans he0
      have he := hinj ⟨ht.1.le, ht.2.le⟩ ⟨le_rfl, hθ.le⟩ hu
      exact ht.1.ne' he
    · have hrs : r = s := by
        have hn := congrArg norm (hxt.symm.trans heθ)
        simpa only [norm_smul, hunit, Real.norm_of_nonneg hr.le,
          Real.norm_of_nonneg hs, mul_one] using hn
      have hu : sectorUnit t = sectorUnit θ := by
        apply (smul_right_injective (Euc 2) (ne_of_gt hr))
        simpa only [hrs] using hxt.symm.trans heθ
      have he := hinj ⟨ht.1.le, ht.2.le⟩ ⟨hθ.le, le_rfl⟩ hu
      exact ht.2.ne he

theorem sector_model_interior (A : SectorModel) :
    interior A.domain = A.domain \ A.boundary := by
  cases h : A.interiorChart
  · simp only [SectorModel.domain, SectorModel.boundary, h, Bool.false_eq_true,
      if_false, interior_inter, Metric.isOpen_ball.interior_eq]
    rw [← planar_sector_boundary_complement A.angle A.angle_positive A.angle_lt_two_pi]
    ext x
    simp only [mem_inter_iff, mem_diff]
    tauto
  · simp [SectorModel.domain, SectorModel.boundary, h, Metric.isOpen_ball.interior_eq]

theorem sector_chart_piece_interior (P : CompactSectorPiece.{u}) (j : Fin P.count) :
    (P.chart j).map '' (P.interior ∩ (P.chart j).map.source) =
      interior (P.chart j).map.target := by
  rw [(P.chart j).target_eq, sector_model_interior, ← (P.chart j).target_eq,
    ← P.boundary_charts j]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxs⟩, rfl⟩
    refine ⟨(P.chart j).map.map_source hxs, ?_⟩
    rintro ⟨z, ⟨hz, hzs⟩, he⟩
    have hzx := (P.chart j).map.injOn hzs hxs he
    exact hx (hzx ▸ hz)
  · rintro ⟨hyt, hyb⟩
    refine ⟨(P.chart j).map.symm y, ⟨?_, (P.chart j).map.map_target hyt⟩,
      (P.chart j).map.right_inv hyt⟩
    intro hb
    exact hyb ⟨_, ⟨hb, (P.chart j).map.map_target hyt⟩, (P.chart j).map.right_inv hyt⟩

theorem sector_chart_inverse_interior (P : CompactSectorPiece.{u}) (j : Fin P.count) :
    MapsTo (P.chart j).map.symm (interior (P.chart j).map.target)
      (P.interior ∩ (P.chart j).map.source) := by
  intro y hy
  rw [← sector_chart_piece_interior P j] at hy
  rcases hy with ⟨x, hx, rfl⟩
  simpa only [(P.chart j).map.left_inv hx.2] using hx

theorem sector_piece_boundary_closed (P : CompactSectorPiece.{u}) :
    IsClosed P.boundary := by
  apply isOpen_compl_iff.mp
  have heq : P.boundaryᶜ = ⋃ j, P.boundaryᶜ ∩ (P.chart j).map.source := by
    rw [← inter_iUnion, P.covers, inter_univ]
  rw [heq]
  apply isOpen_iUnion
  intro j
  have he : P.boundaryᶜ ∩ (P.chart j).map.source =
      (P.chart j).map.source ∩ (P.chart j).map ⁻¹'
        interior (P.chart j).map.target := by
    ext x
    constructor
    · rintro ⟨hx, hxs⟩
      refine ⟨hxs, ?_⟩
      rw [← sector_chart_piece_interior P j]
      exact ⟨x, ⟨hx, hxs⟩, rfl⟩
    · rintro ⟨hxs, hxi⟩
      have h := sector_chart_inverse_interior P j hxi
      simpa only [CompactSectorPiece.interior, (P.chart j).map.left_inv hxs] using h
  rw [he]
  exact (P.chart j).map.continuousOn.isOpen_inter_preimage
    (P.chart j).source_open isOpen_interior

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

theorem geometric_seam_carrier_closed {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) : IsClosed F.seam.carrier := by
  unfold SeamGraph.carrier
  apply IsClosed.union
  · exact isClosed_iUnion_of_finite (fun i => isCompact_range (F.seam.arc i).continuous |>.isClosed)
  · exact isClosed_iUnion_of_finite (fun i => isCompact_range (F.seam.circle i).continuous |>.isClosed)

/-- Openness in the supplied source surface, from its exact component field. -/
theorem geometric_piece_interior_image_open {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount) :
    IsOpen (F.parametrization i '' (F.domain i).interior) := by
  let : LocallyConnectedSpace S :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 2) S
  obtain ⟨x, hx, heq⟩ := F.piece_interior_component i
  rw [heq]
  exact ((geometric_seam_carrier_closed F).union
    ((𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by simp))).isOpen_compl.connectedComponentIn

theorem geometric_piece_chart_interior_image_open {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) :
    IsOpen (F.parametrization i ''
      ((F.domain i).interior ∩ ((F.domain i).chart j).map.source)) := by
  obtain ⟨O, hO, he⟩ := (F.parametrization_embedding i).isInducing.isOpen_iff.mp
    ((F.domain i).chart j).source_open
  rw [← he, image_inter_preimage]
  exact (geometric_piece_interior_image_open F i).inter hO

/-- The literal target image, including the supplied source chart p. -/
theorem sector_source_coordinate_target_open {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) (p : S) :
    IsOpen (sectorToSourceCoordinates F i j p '' sectorToSourceDomain F i j p) := by
  let U := F.parametrization i ''
    ((F.domain i).interior ∩ ((F.domain i).chart j).map.source) ∩ (surfaceChart p).source
  have hU : IsOpen U := (geometric_piece_chart_interior_image_open F i j).inter
    (isOpen_extChartAt_source p)
  have heq : sectorToSourceCoordinates F i j p '' sectorToSourceDomain F i j p =
      surfaceChart p '' U := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨F.parametrization i (((F.domain i).chart j).map.symm y),
        ⟨⟨_, sector_chart_inverse_interior (F.domain i) j hy.1, rfl⟩, hy.2⟩, rfl⟩
    · rintro ⟨x, ⟨⟨q, hq, rfl⟩, hp⟩, rfl⟩
      have hy : ((F.domain i).chart j).map q ∈ interior ((F.domain i).chart j).map.target := by
        rw [← sector_chart_piece_interior (F.domain i) j]
        exact ⟨q, hq, rfl⟩
      refine ⟨((F.domain i).chart j).map q, ⟨hy, ?_⟩, ?_⟩
      · change F.parametrization i (((F.domain i).chart j).map.symm
          (((F.domain i).chart j).map q)) ∈ (surfaceChart p).source
        simpa only [((F.domain i).chart j).map.left_inv hq.2] using hp
      · simp only [sectorToSourceCoordinates, Function.comp_apply,
          ((F.domain i).chart j).map.left_inv hq.2]
  rw [heq]
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨x, hx, rfl⟩
  have hxb : x ∉ S.boundary := by
    obtain ⟨q, hq, rfl⟩ := hx.1
    obtain ⟨r, hr, hc⟩ := F.piece_interior_component i
    have hm : F.parametrization i q ∈ connectedComponentIn (F.seam.carrier ∪ S.boundary)ᶜ r := by
      rw [← hc]
      exact ⟨q, hq.1, rfl⟩
    exact fun hb => connectedComponentIn_subset _ _ hm (Or.inr hb)
  have hi : (𝓡∂ 2).IsInteriorPoint x :=
    ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mpr hxb
  have hxsource : x ∈ (chartAt (EuclideanHalfSpace 2) p).source := by
    simpa only [surfaceChart, extChartAt_source] using hx.2
  have htarget : surfaceChart p x ∈ interior (surfaceChart p).target := by
    exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p) hxsource).mp hi
  exact (chartAt (EuclideanHalfSpace 2) p).extend_image_nhds_mem_nhds_of_mem_interior_range
    hxsource ((chartAt (EuclideanHalfSpace 2) p).interior_extend_target_subset_interior_range htarget)
    (hU.mem_nhds hx)

theorem sector_source_point_avoids_boundary {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (i : Fin F.pieceCount)
    (j : Fin (F.domain i).count) {y : Euc 2}
    (hy : y ∈ interior ((F.domain i).chart j).map.target) :
    F.parametrization i (((F.domain i).chart j).map.symm y) ∈ S.boundaryᶜ := by
  obtain ⟨x, hx, heq⟩ := F.piece_interior_component i
  have hpiece := (sector_chart_inverse_interior (F.domain i) j hy).1
  have hmem : F.parametrization i (((F.domain i).chart j).map.symm y) ∈
      connectedComponentIn (F.seam.carrier ∪ S.boundary)ᶜ x := by
    rw [← heq]
    exact ⟨_, hpiece, rfl⟩
  exact fun hb => (connectedComponentIn_subset _ _ hmem) (Or.inr hb)

end
end SeifertSurfaces.MetricFoundations.AreaCertificates
