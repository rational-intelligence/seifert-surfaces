import SectorHalfStripTemplateProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

theorem native_exact_sphere_clock_coordinate_embedding
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (γ : ℝ → ThreeSphere) (q : ℝ → Euc 2)
    (hγ : IsEmbedding (fun t : U => γ t))
    (hqm : MapsTo q U ((F.domain i).chart j).map.target)
    (heq : ∀ t ∈ U, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t) :
    IsEmbedding (fun t : U => q t) := by
  let A := ((F.domain i).chart j).map.target
  have hqc := native_piece_curve_coordinates_continuous E F i j U γ q
    (continuousOn_iff_continuous_domRestrict.mpr hγ.continuous) hqm heq
  let q' : U → A := fun t => ⟨q t, hqm t.property⟩
  let f : A → ThreeSphere := fun y => E.toSphere
    (sectorCoordinateMap (F.map ∘ F.parametrization i) j y)
  have hfemb : IsEmbedding f := (IsEmbedding.subtypeVal.comp (F.piece_topological_embedding i)).comp
    ((F.domain i).chart j).map.symm.isEmbedding_restrict
  have hq'c : Continuous q' := hqc.domRestrict.subtype_mk _
  have hcomp : IsEmbedding (f ∘ q') := by
    have heq' : f ∘ q' = (fun t : U => γ t) := funext (fun t => heq t t.property)
    rwa [heq']
  exact IsEmbedding.subtypeVal.comp (IsEmbedding.of_comp hq'c hfemb.continuous hcomp)

/-- The constructed exact native seam lift produces actual affine
halfstrips. No straightness, lifted regularity or collar is assumed. -/
theorem native_regular_boundary_halfstrip_template
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (hU : IsOpen U) (h0 : 0 ∈ U) (γ : ℝ → ThreeSphere) (q : ℝ → Euc 2)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 γ U)
    (hγemb : IsEmbedding (fun t : U => γ t))
    (hreg : ∀ t ∈ U, mfderiv 𝓘(ℝ) (𝓡 3) γ t 1 ≠ 0)
    (hqb : MapsTo q U (((F.domain i).chart j).map.target ∩ frontier ((F.domain i).chart j).map.target))
    (heq : ∀ t ∈ U, E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j (q t)) = γ t) :
    Nonempty (SectorHalfStripTemplate ((F.domain i).chart j).model q) := by
  have hqt : MapsTo q U ((F.domain i).chart j).map.target := fun _ ht => (hqb ht).1
  have hqc := native_piece_curve_coordinates_c1_all E F i j U hU γ q hγ hqt heq
  have hqr := native_piece_curve_coordinates_regular E F i j U hU γ q hγ hqt heq hreg
  have hqemb := native_exact_sphere_clock_coordinate_embedding E F i j U γ q hγemb hqt heq
  have hregular : q 0 ≠ 0 ∨ ((F.domain i).chart j).model.angle = Real.pi := by
    by_cases hn : q 0 = 0
    · let c : SeifertSurfaces.OriginalEndpoints.SmoothAmbientChart ThreeSphere := {
        chart := chartAt (Euc 3) (γ 0)
        smooth := contMDiffOn_chart
        inverse_smooth := contMDiffOn_chart_symm }
      exact Or.inr (native_regular_seam_through_sector_origin E F i j U hU h0 γ q
        hγ (hreg 0 h0) hqb heq hn c (mem_chart_source _ _)).2
    · exact Or.inl hn
  apply regular_sector_boundary_halfstrip_template _ q U hU h0 _ hqc hqr hqemb hregular
  simpa only [((F.domain i).chart j).target_eq] using hqb

theorem native_halfstrip_template_source_embedding
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (q : ℝ → Euc 2)
    (C : SectorHalfStripTemplate ((F.domain i).chart j).model q)
    (d : ℝ) (hd : 0 < d) (hdC : d ≤ C.scaleBound) :
    IsEmbedding (fun z : seamHalfstrip C.height => F.parametrization i
      (((F.domain i).chart j).map.symm
        (affineSeamCoordinates (q 0) C.tangent C.inward (fun t => C.clock (d * t)) z))) := by
  have hΦ := affineSeamCoordinates_embedding (q 0) C.tangent C.inward
    (fun t => C.clock (d * t)) C.height C.tangent_unit C.inward_unit C.orthogonal
    (C.clock_embedding d hd hdC)
  have hm : MapsTo (affineSeamCoordinates (q 0) C.tangent C.inward (fun t => C.clock (d * t)))
      (seamHalfstrip C.height) ((F.domain i).chart j).map.target := by
    simpa only [((F.domain i).chart j).target_eq] using C.maps_to_sector d hd hdC
  exact (F.parametrization_embedding i).comp
    (((F.domain i).chart j).map.symm.isEmbedding_restrict.comp
      (hΦ.codRestrict ((F.domain i).chart j).map.target (fun z => hm z.property)))

theorem native_halfstrip_template_positive_piece_interior
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (q : ℝ → Euc 2)
    (C : SectorHalfStripTemplate ((F.domain i).chart j).model q)
    (d : ℝ) (hd : 0 < d) (hdC : d ≤ C.scaleBound) :
    MapsTo (fun z => ((F.domain i).chart j).map.symm
      (affineSeamCoordinates (q 0) C.tangent C.inward (fun t => C.clock (d * t)) z))
      (Ioo (-1 : ℝ) 1 ×ˢ Ioo (0 : ℝ) C.height) (F.domain i).interior := by
  intro z hz
  have hi := C.positive_interior d hd hdC hz
  rw [← ((F.domain i).chart j).target_eq] at hi
  exact (AreaCertificates.sector_chart_inverse_interior (F.domain i) j hi).1

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
