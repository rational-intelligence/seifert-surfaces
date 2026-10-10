import Section5PolarBoundaryCoordinatesV488
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

def polarLongitudeHomeomorph : (Circle × Circle) ≃ₜ (Circle × Circle) :=
  (polarBoundaryHomeomorph P).trans (longitudeBoundaryHomeomorph J).symm

theorem polar_longitude_parameter (p : Circle × Circle) :
    J.torus (polarLongitudeHomeomorph P J p) = polarBoundaryParameter P p := by
  exact congrArg Subtype.val ((longitudeBoundaryHomeomorph J).apply_symm_apply
    (polarBoundaryHomeomorph P p))

theorem polar_longitude_inverse_parameter (p : Circle × Circle) :
    polarBoundaryParameter P ((polarLongitudeHomeomorph P J).symm p) = J.torus p := by
  have h := polar_longitude_parameter P J ((polarLongitudeHomeomorph P J).symm p)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

theorem polar_longitude_smooth :
    ContMDiff ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ∞ (polarLongitudeHomeomorph P J) := by
  apply (ContMDiff.iff_comp_isImmersion J.smoothEmbedding.isImmersion).mpr
  refine ⟨(polarLongitudeHomeomorph P J).continuous,?_⟩
  exact (polar_boundary_parameter_smooth P).congr (fun p => polar_longitude_parameter P J p)

theorem polar_longitude_inverse_smooth :
    ContMDiff ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ∞ (polarLongitudeHomeomorph P J).symm := by
  let y : (Circle × Circle) → P.image := fun p =>
    ⟨J.torus p, polar_image_contains_boundary P (J.torus_lands_boundary p)⟩
  have hy : ContMDiff ((𝓡 1).prod (𝓡 1)) (𝓡∂ 3) ∞ y := by
    apply (ContMDiff.subtypeVal_comp_iff P.image y).mp
    exact J.smoothEmbedding.contMDiff
  have hc : ContMDiff ((𝓡 1).prod (𝓡 1)) PolarModel ∞
      (fun p => (P.coordinates.symm (y p)).val) :=
    contMDiff_subtype_val.comp (P.coordinates.symm.contMDiff.comp hy)
  have hs : ContMDiff ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) ∞
      (fun p => ((P.coordinates.symm (y p)).val.1,(P.coordinates.symm (y p)).val.2.1)) :=
    hc.fst.prodMk hc.snd.fst
  apply hs.congr
  intro p
  let q := (polarLongitudeHomeomorph P J).symm p
  have he : P.coordinates (polarZeroSection q) = y p :=
    Subtype.ext (polar_longitude_inverse_parameter P J p)
  have h := congrArg (fun z => (P.coordinates.symm z).val) he
  rw [Diffeomorph.symm_apply_apply] at h
  exact Prod.ext (congrArg (fun z : PolarDomain => z.1) h) (congrArg (fun z : PolarDomain => z.2.1) h)

def polarLongitudeDiffeomorph :
    Diffeomorph ((𝓡 1).prod (𝓡 1)) ((𝓡 1).prod (𝓡 1)) (Circle × Circle) (Circle × Circle) ∞ :=
  ⟨(polarLongitudeHomeomorph P J).toEquiv, polar_longitude_smooth P J,
    polar_longitude_inverse_smooth P J⟩

#print axioms polarLongitudeDiffeomorph
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
