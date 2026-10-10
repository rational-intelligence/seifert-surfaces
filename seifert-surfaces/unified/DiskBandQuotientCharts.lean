import DiskBandCellRefinement

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
noncomputable section

variable {P : PolygonalKnot} {D : RegularOrientedDiagram P}
  {R : OrientedResolution D}

/-- The ambient coordinate of a halfspace chart. No smoothness of this chart is asserted. -/
def halfspaceCoordinates {X : Type*} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (EuclideanHalfSpace 2)) (x : X) : Euc 2 := (c x).val

def DiskBandQuotientCharts.freeDiskBoundary (B : DiskBandData R) (i : Fin R.count) : Set (B.disk i).Carrier :=
  {x | (x : Euc 2) ∈ frontier (B.disk i).region ∧
    ¬ ∃ (k : Fin D.crossingCount) (e : Fin 2) (t : Time),
      (Sum.inl ⟨i, x⟩ : B.RawPieces) = Sum.inl ⟨B.incident k e, B.attaching k e t⟩}

def polarPoint (r θ : ℝ) : Euc 2 := !₂[r * Real.cos θ, r * Real.sin θ]

def polygonSector (angle : ℝ) : Set (Euc 2) :=
  {x | ∃ r θ : ℝ, 0 ≤ r ∧ θ ∈ Icc (0 : ℝ) angle ∧ x = polarPoint r θ}

/-- Angular rescaling is a topological sector model, including reflex sectors.
It is not asserted differentiable at the vertex. -/
structure PolygonSectorHalfspace (angle : ℝ) where
  homeomorph : ↥(polygonSector angle) ≃ₜ EuclideanHalfSpace 2
  angular_formula : ∀ (r θ : ℝ) (hr : 0 ≤ r) (hθ : θ ∈ Icc (0 : ℝ) angle)
    (hpoint : polarPoint r θ ∈ polygonSector angle),
    (homeomorph ⟨polarPoint r θ, hpoint⟩).val =
      !₂[r * Real.sin (Real.pi * θ / angle), r * Real.cos (Real.pi * θ / angle)]

structure ActualDiskInteriorChart (B : DiskBandData R) (i : Fin R.count)
    (p : (B.disk i).Carrier) where
  radius : ℝ
  radius_pos : 0 < radius
  chart : OpenPartialHomeomorph B.Carrier (EuclideanHalfSpace 2)
  center_mem : B.diskInclusion i p ∈ chart.source
  source_in_disk : chart.source ⊆ Set.range (B.diskInclusion i)
  disk_source_inside : ∀ q, B.diskInclusion i q ∈ chart.source →
    (q : Euc 2) ∈ interior (B.disk i).region
  formula : ∀ q, B.diskInclusion i q ∈ chart.source →
    halfspaceCoordinates chart (B.diskInclusion i q) =
      !₂[1 + ((q : Euc 2) 0 - (p : Euc 2) 0) / radius,
        ((q : Euc 2) 1 - (p : Euc 2) 1) / radius]
  interior_target : ∀ u ∈ chart.target, 0 < u.val 0
  avoids_boundary : Disjoint chart.source B.boundarySet

structure ActualBandInteriorChart (B : DiskBandData R) (k : Fin D.crossingCount)
    (p : Time × Time) where
  radius : ℝ
  radius_pos : 0 < radius
  chart : OpenPartialHomeomorph B.Carrier (EuclideanHalfSpace 2)
  center_mem : B.bandInclusion k p ∈ chart.source
  source_in_band : chart.source ⊆ Set.range (B.bandInclusion k)
  band_source_inside : ∀ q, B.bandInclusion k q ∈ chart.source →
    (q.1 : ℝ) ∈ Ioo (0 : ℝ) 1 ∧ (q.2 : ℝ) ∈ Ioo (0 : ℝ) 1
  formula : ∀ q, B.bandInclusion k q ∈ chart.source →
    halfspaceCoordinates chart (B.bandInclusion k q) =
      !₂[1 + ((q.1 : ℝ) - (p.1 : ℝ)) / radius, ((q.2 : ℝ) - (p.2 : ℝ)) / radius]
  interior_target : ∀ u ∈ chart.target, 0 < u.val 0
  avoids_boundary : Disjoint chart.source B.boundarySet

structure ActualFreeBandChart (B : DiskBandData R) (k : Fin D.crossingCount)
    (t : Time) (v : Fin 2) where
  scale : ℝ
  scale_pos : 0 < scale
  chart : OpenPartialHomeomorph B.Carrier (EuclideanHalfSpace 2)
  center_mem : B.bandInclusion k (t, (if v = 0 then 0 else 1)) ∈ chart.source
  source_in_band : chart.source ⊆ Set.range (B.bandInclusion k)
  band_source_away_ends : ∀ q, B.bandInclusion k q ∈ chart.source →
    (q.1 : ℝ) ∈ Ioo (0 : ℝ) 1
  formula : ∀ q, B.bandInclusion k q ∈ chart.source →
    halfspaceCoordinates chart (B.bandInclusion k q) =
      !₂[(if v = 0 then (q.2 : ℝ) else 1 - (q.2 : ℝ)) / scale,
        ((q.1 : ℝ) - (t : ℝ)) / scale]
  boundary_coordinate : ∀ x ∈ chart.source,
    x ∈ B.boundarySet ↔ (chart x).val 0 = 0

structure ActualSeamChart (B : DiskBandData R)
    (k : Fin D.crossingCount) (e : Fin 2) (t : Time) where
  diskCollar : OpenPartialHomeomorph (B.disk (B.incident k e)).Carrier (EuclideanHalfSpace 2)
  bandCollar : OpenPartialHomeomorph (Time × Time) (EuclideanHalfSpace 2)
  interval : Set Time
  interval_open : IsOpen interval
  parameter_mem : t ∈ interval
  interval_inside : ∀ s ∈ interval, (s : ℝ) ∈ Ioo (0 : ℝ) 1
  disk_seam : ∀ s ∈ interval,
    B.attaching k e s ∈ diskCollar.source ∧
      halfspaceCoordinates diskCollar (B.attaching k e s) = !₂[0, (s : ℝ)]
  band_seam : ∀ s ∈ interval,
    DiskBandData.bandEnd e s ∈ bandCollar.source ∧
      halfspaceCoordinates bandCollar (DiskBandData.bandEnd e s) = !₂[0, (s : ℝ)]
  shift : ℝ
  shift_pos : 0 < shift
  chart : OpenPartialHomeomorph B.Carrier (EuclideanHalfSpace 2)
  center_mem : B.bandInclusion k (DiskBandData.bandEnd e t) ∈ chart.source
  disk_source : ∀ p, B.diskInclusion (B.incident k e) p ∈ chart.source →
    p ∈ diskCollar.source
  band_source : ∀ p, B.bandInclusion k p ∈ chart.source → p ∈ bandCollar.source
  source_pieces : chart.source ⊆
    Set.range (B.diskInclusion (B.incident k e)) ∪ Set.range (B.bandInclusion k)
  disk_formula : ∀ p, B.diskInclusion (B.incident k e) p ∈ chart.source →
    halfspaceCoordinates chart (B.diskInclusion (B.incident k e) p) =
      !₂[shift + (diskCollar p).val 0, (diskCollar p).val 1]
  band_formula : ∀ p, B.bandInclusion k p ∈ chart.source →
    halfspaceCoordinates chart (B.bandInclusion k p) =
      !₂[shift - (bandCollar p).val 0, (bandCollar p).val 1]
  interior_target : ∀ u ∈ chart.target, 0 < u.val 0
  avoids_boundary : Disjoint chart.source B.boundarySet

def incidentEndpointRawPatch (B : DiskBandData R) (k : Fin D.crossingCount)
    (e : Fin 2) (diskPatch : Set (B.disk (B.incident k e)).Carrier)
    (bandPatch : Set (Time × Time)) : Set B.RawPieces :=
  (fun p => (Sum.inl ⟨B.incident k e, p⟩ : B.RawPieces)) '' diskPatch ∪
    (fun p => (Sum.inr (k, p) : B.RawPieces)) '' bandPatch

structure ActualEndpointPatch (B : DiskBandData R)
    (k : Fin D.crossingCount) (e v : Fin 2) where
  diskPatch : Set (B.disk (B.incident k e)).Carrier
  bandPatch : Set (Time × Time)
  disk_open : IsOpen diskPatch
  band_open : IsOpen bandPatch
  disk_center : B.attaching k e (if v = 0 then 0 else 1) ∈ diskPatch
  band_center : DiskBandData.bandEnd e (if v = 0 then 0 else 1) ∈ bandPatch
  saturated : ∀ x ∈ incidentEndpointRawPatch B k e diskPatch bandPatch,
    ∀ y, B.gluingSetoid.r x y → y ∈ incidentEndpointRawPatch B k e diskPatch bandPatch

namespace ActualEndpointPatch
variable {B : DiskBandData R} {k : Fin D.crossingCount} {e v : Fin 2}
  (N : ActualEndpointPatch B k e v)

def rawPatch : Set B.RawPieces := incidentEndpointRawPatch B k e N.diskPatch N.bandPatch

def localSetoid : Setoid ↥N.rawPatch := Setoid.comap Subtype.val B.gluingSetoid

abbrev LocalQuotient := Quotient N.localSetoid

def neighborhood : Set B.Carrier :=
  Set.range (fun p : ↥N.rawPatch => Quotient.mk B.gluingSetoid p.val)

def quotientEquiv : N.LocalQuotient ≃ ↥N.neighborhood :=
  Setoid.comapQuotientEquiv Subtype.val B.gluingSetoid

theorem quotientEquiv_isInducing : IsInducing N.quotientEquiv := by
  have hraw : IsOpen N.rawPatch := by
    apply IsOpen.union
    · have hs : IsOpen (Sigma.mk (B.incident k e) '' N.diskPatch) :=
        (@isOpenMap_sigmaMk (Fin R.count) (fun i => (B.disk i).Carrier)
          (fun i => inferInstance) (B.incident k e)) _ N.disk_open
      simpa only [Set.image_image, Function.comp_def] using
        (isOpenMap_inl (Y := Fin D.crossingCount × (Time × Time)) _ hs)
    · have hs : IsOpen ((fun p : Time × Time => (k, p)) '' N.bandPatch) := by
        have hprod : (fun p : Time × Time => (k, p)) '' N.bandPatch = {k} ×ˢ N.bandPatch := by
          ext ⟨a, p⟩
          constructor
          · rintro ⟨q, hq, h⟩
            exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h) ▸ hq⟩
          · rintro ⟨ha, hp⟩
            exact ⟨p, hp, by simpa using ha.symm⟩
        rw [hprod]
        exact (isOpen_discrete {k}).prod N.band_open
      simpa only [Set.image_image, Function.comp_def] using
        (isOpenMap_inr (X := Σ i : Fin R.count, (B.disk i).Carrier) _ hs)
  have hpre : Quotient.mk B.gluingSetoid ⁻¹' N.neighborhood = N.rawPatch := by
    ext x
    constructor
    · rintro ⟨p, hp⟩
      exact N.saturated p.val p.property x (Quotient.exact hp)
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hopen : IsOpen N.neighborhood :=
    isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp (hpre.symm ▸ hraw)
  let f : ↥N.rawPatch → ↥N.neighborhood := fun p => ⟨Quotient.mk B.gluingSetoid p.val, p, rfl⟩
  have hf : IsQuotientMap f := by
    have hres := isQuotientMap_quotient_mk'.restrictPreimage_isOpen hopen
    have he := (Homeomorph.setCongr hpre.symm).isQuotientMap
    exact hres.comp he
  have hcomp : N.quotientEquiv ∘ Quotient.mk N.localSetoid = f := rfl
  have he : IsQuotientMap N.quotientEquiv :=
    isQuotientMap_quotient_mk'.of_comp_iff.mp (hcomp.symm ▸ hf)
  exact (N.quotientEquiv.toHomeomorphOfContinuousOpen he.continuous
    (he.isCoinducing.isOpenMap_of_injective N.quotientEquiv.injective)).isInducing

def quotientHomeomorph : N.LocalQuotient ≃ₜ ↥N.neighborhood :=
  N.quotientEquiv.toHomeomorphOfIsInducing N.quotientEquiv_isInducing

theorem quotientHomeomorph_mk (p : ↥N.rawPatch) :
    (N.quotientHomeomorph (Quotient.mk N.localSetoid p) : B.Carrier) =
      Quotient.mk B.gluingSetoid p.val := by
  rfl

theorem neighborhood_open : IsOpen N.neighborhood := by
  have hraw : IsOpen N.rawPatch := by
    apply IsOpen.union
    · have hs : IsOpen (Sigma.mk (B.incident k e) '' N.diskPatch) :=
        (@isOpenMap_sigmaMk (Fin R.count) (fun i => (B.disk i).Carrier)
          (fun i => inferInstance) (B.incident k e)) _ N.disk_open
      simpa only [Set.image_image, Function.comp_def] using
        (isOpenMap_inl (Y := Fin D.crossingCount × (Time × Time)) _ hs)
    · have hs : IsOpen ((fun p : Time × Time => (k, p)) '' N.bandPatch) := by
        have hprod : (fun p : Time × Time => (k, p)) '' N.bandPatch = {k} ×ˢ N.bandPatch := by
          ext ⟨a, p⟩
          constructor
          · rintro ⟨q, hq, h⟩
            have h₁ := congrArg Prod.fst h
            have h₂ := congrArg Prod.snd h
            exact ⟨h₁.symm, h₂ ▸ hq⟩
          · rintro ⟨ha, hp⟩
            exact ⟨p, hp, by simpa using ha.symm⟩
        rw [hprod]
        exact (isOpen_discrete {k}).prod N.band_open
      simpa only [Set.image_image, Function.comp_def] using
        (isOpenMap_inr (X := Σ i : Fin R.count, (B.disk i).Carrier) _ hs)
  apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
  have hpre : Quotient.mk B.gluingSetoid ⁻¹' N.neighborhood = N.rawPatch := by
    ext x
    constructor
    · rintro ⟨p, hp⟩
      exact N.saturated p.val p.property x (Quotient.exact hp)
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  exact hpre.symm ▸ hraw

theorem neighborhood_pieces : N.neighborhood =
    B.diskInclusion (B.incident k e) '' N.diskPatch ∪ B.bandInclusion k '' N.bandPatch := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    rcases p.property with hd | hb
    · rcases hd with ⟨q, hq, hp⟩
      exact Or.inl ⟨q, hq, congrArg (Quotient.mk B.gluingSetoid) hp⟩
    · rcases hb with ⟨q, hq, hp⟩
      exact Or.inr ⟨q, hq, congrArg (Quotient.mk B.gluingSetoid) hp⟩
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact ⟨⟨Sum.inl ⟨B.incident k e, q⟩, Or.inl ⟨q, hq, rfl⟩⟩, rfl⟩
    · exact ⟨⟨Sum.inr (k, q), Or.inr ⟨q, hq, rfl⟩⟩, rfl⟩

theorem local_attachment_gluing (t : Time)
    (hd : (Sum.inl ⟨B.incident k e, B.attaching k e t⟩ : B.RawPieces) ∈ N.rawPatch)
    (hb : (Sum.inr (k, DiskBandData.bandEnd e t) : B.RawPieces) ∈ N.rawPatch) :
    Quotient.mk N.localSetoid ⟨Sum.inl ⟨B.incident k e, B.attaching k e t⟩, hd⟩ =
      Quotient.mk N.localSetoid ⟨Sum.inr (k, DiskBandData.bandEnd e t), hb⟩ := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨k, e, t, rfl, rfl⟩)
end ActualEndpointPatch

def clippedPolygonSector (angle radius : ℝ) : Set (Euc 2) :=
  polygonSector angle ∩ Metric.ball (0 : Euc 2) radius

structure SectorAngularRescaling (sourceAngle targetAngle : ℝ) where
  homeomorph : ↥(polygonSector sourceAngle) ≃ₜ ↥(polygonSector targetAngle)
  formula : ∀ (r θ : ℝ) (hr : 0 ≤ r) (hθ : θ ∈ Icc (0 : ℝ) sourceAngle)
    (hpoint : polarPoint r θ ∈ polygonSector sourceAngle),
    (homeomorph ⟨polarPoint r θ, hpoint⟩ : Euc 2) =
      polarPoint r (targetAngle * θ / sourceAngle)

def endpointBandSectorVector (B : DiskBandData R) (k : Fin D.crossingCount)
    (e v : Fin 2) (frame : Euc 2 ≃L[ℝ] Euc 2) (q : Time × Time) : Euc 2 :=
  !₂[B.width k * (if e = 0 then (q.1 : ℝ) else 1 - (q.1 : ℝ)),
    ‖frame.symm ((B.attaching k e q.2 : Euc 2) - B.attachmentEndpoint k e v)‖]

def rotatedReflectedSectorPoint (angle : ℝ) (u : Euc 2) : Euc 2 :=
  !₂[Real.cos angle * u 0 + Real.sin angle * u 1,
    Real.sin angle * u 0 - Real.cos angle * u 1]

def halfspaceTangentReflection (u : Euc 2) : Euc 2 := !₂[u 0, -u 1]


end

end SeifertSurfaces.LongitudeProducers
