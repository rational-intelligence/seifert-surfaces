import NativeSharedSeamDataProbe
import NativeHalfStripConormalProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped Manifold ContDiff Bundle
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- Full native two-piece seam construction for a given original regular
clock. Two incident pieces, all halfstrip data and all conormals are outputs. -/
theorem native_shared_seam_geometry (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (β : SeamLocalTime → S) (γ : ℝ → ThreeSphere)
    (hformula : ∀ t : SeamLocalTime, γ t = E.toSphere (F.map (β t)))
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ γ (Ioo (-1 : ℝ) 1))
    (hreg : ∀ t : SeamLocalTime, mfderiv 𝓘(ℝ) (𝓡 3) γ (t : ℝ) 1 ≠ 0)
    (hemb : IsEmbedding (fun t : SeamLocalTime => γ t))
    (hxseam : β ⟨0, neg_one_lt_zero, zero_lt_one⟩ ∈ F.seam.carrier)
    (hxboundary : β ⟨0, neg_one_lt_zero, zero_lt_one⟩ ∉ S.boundary)
    (Q : Set ℝ) (hQ : IsOpen Q) (hQW : Q ⊆ Ioo (-1 : ℝ) 1) (h0Q : 0 ∈ Q)
    (hlifts : ∀ i : Fin F.pieceCount,
      β ⟨0, neg_one_lt_zero, zero_lt_one⟩ ∈ range (F.parametrization i) →
      ∃ j : Fin (F.domain i).count, ∃ q : ℝ → Euc 2,
        MapsTo q Q (((F.domain i).chart j).map.target ∩ frontier ((F.domain i).chart j).map.target) ∧
        (∀ t ∈ Q, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t) ∧
        ContDiffOn ℝ 1 q Q ∧ (∀ t ∈ Q, deriv q t ≠ 0)) :
    Nonempty (NativeSharedSeamData E G F β) := by
  classical
  obtain ⟨i, k, hik, hi, hk⟩ := native_seam_at_least_two_incident_pieces E F _ hxseam hxboundary
  obtain ⟨j, q, hqb, hqi, hqc, hqr⟩ := hlifts i hi
  obtain ⟨l, r, hrb, hri, hrc, hrr⟩ := hlifts k hk
  have hγQ : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 γ Q := (hγ.of_le (by simp)).mono hQW
  have hγembQ : IsEmbedding (fun t : Q => γ t) := hemb.comp (IsEmbedding.inclusion hQW)
  have hregQ : ∀ t ∈ Q, mfderiv 𝓘(ℝ) (𝓡 3) γ t 1 ≠ 0 :=
    fun t ht => hreg ⟨t, hQW ht⟩
  obtain ⟨C⟩ := native_regular_boundary_halfstrip_template E F i j Q hQ h0Q γ q
    hγQ hγembQ hregQ hqb hqi
  obtain ⟨D⟩ := native_regular_boundary_halfstrip_template E F k l Q hQ h0Q γ r
    hγQ hγembQ hregQ hrb hri
  obtain ⟨δ, hδ, hδQ⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds h0Q)
  let d := min 1 (min δ (min C.scaleBound D.scaleBound)) / 2
  have hd : 0 < d := half_pos (lt_min zero_lt_one
    (lt_min hδ (lt_min C.scaleBound_pos D.scaleBound_pos)))
  have hd1 : d < 1 := by dsimp [d]; linarith [min_le_left 1 (min δ (min C.scaleBound D.scaleBound))]
  have hdδ : d < δ := by
    have hb := (min_le_right 1 (min δ (min C.scaleBound D.scaleBound))).trans
      (min_le_left δ (min C.scaleBound D.scaleBound))
    dsimp [d]
    nlinarith [hb, hδ]
  have hdC : d ≤ C.scaleBound := by
    have hb := (min_le_right 1 (min δ (min C.scaleBound D.scaleBound))).trans
      ((min_le_right δ (min C.scaleBound D.scaleBound)).trans
        (min_le_left C.scaleBound D.scaleBound))
    dsimp [d]
    nlinarith [hb, C.scaleBound_pos]
  have hdD : d ≤ D.scaleBound := by
    have hb := (min_le_right 1 (min δ (min C.scaleBound D.scaleBound))).trans
      ((min_le_right δ (min C.scaleBound D.scaleBound)).trans
        (min_le_right C.scaleBound D.scaleBound))
    dsimp [d]
    nlinarith [hb, D.scaleBound_pos]
  have hsmall (t : SeamLocalTime) : d * (t : ℝ) ∈ Q := by
    apply hδQ
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos hd]
    have hat : |(t : ℝ)| < 1 := abs_lt.mpr t.property
    nlinarith [mul_lt_mul_of_pos_left hat hd]
  let qd : SeamLocalTime → Euc 2 := fun t => q (d * (t : ℝ))
  let rd : SeamLocalTime → Euc 2 := fun t => r (d * (t : ℝ))
  let γd : ℝ → ThreeSphere := fun t => γ (d * t)
  have hqd : ∀ t, qd t ∈ ((F.domain i).chart j).map.target ∩ frontier ((F.domain i).chart j).map.target :=
    fun t => hqb (hsmall t)
  have hrd : ∀ t, rd t ∈ ((F.domain k).chart l).map.target ∩ frontier ((F.domain k).chart l).map.target :=
    fun t => hrb (hsmall t)
  have hqid : ∀ t, pieceSphereCoordinate E F i j (qd t) = γd t :=
    fun t => hqi _ (hsmall t)
  have hrid : ∀ t, pieceSphereCoordinate E F k l (rd t) = γd t :=
    fun t => hri _ (hsmall t)
  let HC := nativeHalfStripOfTemplate E F i j q C d hd hdC
  let HD := nativeHalfStripOfTemplate E F k l r D d hd hdD
  let h := min C.height D.height
  have hh : 0 < h := lt_min C.height_pos D.height_pos
  let H := nativeHalfStripShorten E F i j HC h hh (min_le_left _ _)
  let J := nativeHalfStripShorten E F k l HD h hh (min_le_right _ _)
  obtain ⟨hγd, hregd⟩ := shortened_native_edge_smooth_regular γ hγ hreg d hd hd1
  have hγdemb : IsEmbedding (fun t : SeamLocalTime => γd t) := hemb.comp (seamScale_embedding d hd hd1)
  obtain ⟨V⟩ := native_halfstrip_full_conormal E G F i j qd γd H hqd hqid
  obtain ⟨Z⟩ := native_halfstrip_full_conormal E G F k l rd γd J hrd hrid
  obtain ⟨N, hN, h0N, hcover, hcross, hincident⟩ := native_halfstrips_actual_ambient_window E S F i k hik
    j l qd rd H J rfl γd hγdemb hqid hrid
  obtain ⟨c, hc, hc1, hcore⟩ := continuous_seam_core_closure γd hγd.continuousOn N hN h0N
  have hsource (t : SeamLocalTime) :
      F.parametrization i (((F.domain i).chart j).map.symm (qd t)) = β (seamScale d hd hd1 t) := by
    have hE : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
    apply F.embedding.injective
    apply hE.isEmbedding.injective
    exact (hqid t).trans (hformula (seamScale d hd hd1 t))
  refine ⟨{
    scale := d
    scale_pos := hd
    scale_lt_one := hd1
    edge := γd
    edge_formula := fun t => hformula (seamScale d hd hd1 t)
    edge_smooth := hγd
    edge_regular := hregd
    one := i
    two := k
    chartOne := j
    chartTwo := l
    liftOne := qd
    liftTwo := rd
    liftOne_boundary := hqd
    liftTwo_boundary := hrd
    imageOne := hqid
    imageTwo := hrid
    outwardOne := V.vector
    outwardTwo := Z.vector
    outwardOne_direction := V.outward
    outwardTwo_direction := Z.outward
    conormalOne_unit := V.unit
    conormalTwo_unit := Z.unit
    conormalOne_orthogonal := V.orthogonal
    conormalTwo_orthogonal := Z.orthogonal
    neighbourhood := N
    neighbourhood_open := hN
    contains_point := ?_
    covers_two_sheets := hcover
    otherwise_disjoint := hcross
    one_ne_two := hik
    incident_exact := ?_
    coreRadius := c
    coreRadius_pos := hc
    coreRadius_lt_one := hc1
    core_edge_closure_in_neighbourhood := hcore
    halfStripOne := H
    halfStripTwo := J
    outwardOne_continuous := V.continuous
    outwardTwo_continuous := Z.continuous
    conormalOne_continuous := V.section_continuous
    conormalTwo_continuous := Z.section_continuous
  }⟩
  · have heq0 : γd 0 = E.toSphere (F.map (β ⟨0, neg_one_lt_zero, zero_lt_one⟩)) := by
      simpa only [γd, mul_zero] using hformula ⟨0, neg_one_lt_zero, zero_lt_one⟩
    rwa [heq0] at h0N
  · intro t a
    rw [← hsource t]
    exact hincident t a

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
