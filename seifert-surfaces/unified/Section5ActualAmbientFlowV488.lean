import Section5PolarConjugateFlowV488
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers SeifertSurfaces.LongitudeProducers.CollarCutHelpers
noncomputable section
local instance : TopologicalSpace PolarDomain := inferInstanceAs (TopologicalSpace (Circle × (Circle × Time)))
local instance : ChartedSpace (ModelProd (Euc 1) (ModelProd (Euc 1) (EuclideanHalfSpace 1))) PolarDomain :=
  inferInstanceAs (ChartedSpace (ModelProd (Euc 1) (ModelProd (Euc 1) (EuclideanHalfSpace 1))) (Circle × (Circle × Time)))
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {D : TubeCoordinates T} (P : GivenExteriorPolarCollar E D) (J : LongitudeFoliation.{0} E)

def longitudeCollarFullMap (p : (Circle × Circle) × Time) : E.Carrier :=
  givenExteriorPolarMap E (((polarLongitudeDiffeomorph P J).symm p.1).1,
    ((polarLongitudeDiffeomorph P J).symm p.1).2,p.2)

theorem longitude_collar_full_smooth :
    ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ (longitudeCollarFullMap P J) := by
  have hq : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ((𝓡 1).prod (𝓡 1)) ∞
      (fun p : (Circle × Circle) × Time => (polarLongitudeDiffeomorph P J).symm p.1) :=
    (polarLongitudeDiffeomorph P J).symm.contMDiff.comp contMDiff_fst
  exact P.smooth.comp (hq.fst.prodMk (hq.snd.prodMk contMDiff_snd))

theorem longitude_collar_full_coordinates (p : longitudeProductStrip) :
    longitudeCollarFullMap P J p.val = (longitudeCollarDiffeomorph P J p : E.Carrier) :=
  (P.equation (longitudeToPolarCoordinates P J p)).symm

def longitudeFlowCore : Set E.Carrier :=
  longitudeCollarFullMap P J '' {p : (Circle × Circle) × Time | (p.2 : ℝ) ≤ 1/2}

theorem longitude_flow_core_compact : IsCompact (longitudeFlowCore P J) := by
  exact (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact.image
    (longitude_collar_full_smooth P J).continuous

theorem longitude_flow_core_subset : longitudeFlowCore P J ⊆ P.image := by
  rintro x ⟨p,hp,rfl⟩
  let q : longitudeProductStrip := ⟨p,by
    change (p.2 : ℝ) < 1
    change (p.2 : ℝ) ≤ 1/2 at hp
    linarith⟩
  rw [longitude_collar_full_coordinates P J q]
  exact (longitudeCollarDiffeomorph P J q).property

theorem polar_conjugate_flow_fixed_off_core (t : ℝ) (x : P.image)
    (hx : (x : E.Carrier) ∉ longitudeFlowCore P J) : polarConjugateFlow P J t x = x := by
  let q := (longitudeCollarDiffeomorph P J).symm x
  have hq : 1/2 ≤ (q.val.2 : ℝ) := by
    by_contra h
    have hlt : (q.val.2 : ℝ) < 1/2 := lt_of_not_ge h
    apply hx
    refine ⟨q.val,hlt.le,?_⟩
    rw [longitude_collar_full_coordinates P J q]
    exact congrArg Subtype.val ((longitudeCollarDiffeomorph P J).apply_symm_apply x)
  change longitudeCollarDiffeomorph P J (longitudeStripFlow t q) = x
  rw [longitude_strip_flow_fixed t q hq]
  exact (longitudeCollarDiffeomorph P J).apply_symm_apply x

def actualLongitudeAmbientFlow : Flow ℝ E.Carrier :=
  extendOpenFlow P.image (polarConjugateFlow P J) (polar_conjugate_flow_smooth P J)
    (longitude_flow_core_compact P J).isClosed (longitude_flow_core_subset P J)
    (polar_conjugate_flow_fixed_off_core P J)

theorem actual_longitude_ambient_flow_smooth :
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun p : ℝ × E.Carrier => actualLongitudeAmbientFlow P J p.1 p.2) :=
  extend_open_flow_smooth P.image (polarConjugateFlow P J) (polar_conjugate_flow_smooth P J)
    (longitude_flow_core_compact P J).isClosed (longitude_flow_core_subset P J)
    (polar_conjugate_flow_fixed_off_core P J)

theorem actual_longitude_ambient_flow_boundary (t : ℝ) (p : Circle × Circle) :
    actualLongitudeAmbientFlow P J t (J.torus p) = J.torus (longitudeLabelFlow t p.1,p.2) := by
  rw [← longitude_collar_boundary P J p]
  change extendOpenFlowMap P.image (polarConjugateFlow P J) t
      (longitudeCollarDiffeomorph P J (longitudeBoundarySection p) : E.Carrier) = _
  rw [extend_open_flow_map_inside,polar_conjugate_flow_coordinates,longitude_strip_flow_boundary]
  exact longitude_collar_boundary P J _

theorem actual_longitude_ambient_flow_leaf (t : ℝ) (a : Circle) :
    actualLongitudeAmbientFlow P J t '' J.leaf a = J.leaf (longitudeLabelFlow t a) := by
  ext x
  constructor
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    exact ⟨z,(actual_longitude_ambient_flow_boundary P J t (a,z)).symm⟩
  · rintro ⟨z,rfl⟩
    exact ⟨J.torus (a,z),⟨z,rfl⟩,actual_longitude_ambient_flow_boundary P J t (a,z)⟩

def actualB1SourceFlow : B1SourceFoliationFlow J where
  ambient := actualLongitudeAmbientFlow P J
  labels := longitudeLabelFlow
  ambient_smooth := actual_longitude_ambient_flow_smooth P J
  labels_smooth := longitude_label_flow_smooth
  leaf_image := actual_longitude_ambient_flow_leaf P J
  labels_transverse := longitude_label_flow_transverse

theorem b1_source_foliation_flow_exists (J : LongitudeFoliation.{0} E) :
    Nonempty (B1SourceFoliationFlow J) := by
  obtain ⟨P⟩ := actual_polar_collar_exists (E:=E)
  exact ⟨actualB1SourceFlow P J⟩

#print axioms b1_source_foliation_flow_exists
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
