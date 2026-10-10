import Section5PolarLongitudeDiffeomorphV488
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

def longitudeProductStrip : TopologicalSpace.Opens ((Circle × Circle) × Time) :=
  ⟨{p | (p.2 : ℝ)<1},isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
def longitudePolarStrip : TopologicalSpace.Opens (Circle × (Circle × Time)) :=
  ⟨{p | (p.2.2 : ℝ)<1},isOpen_lt (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)) continuous_const⟩

variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {D : TubeCoordinates T} (P : GivenExteriorPolarCollar E D) (J : LongitudeFoliation.{0} E)

def longitudeToPolarCoordinates :
    Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) PolarModel
      longitudeProductStrip longitudePolarStrip ∞ where
  toFun p := ⟨(((polarLongitudeDiffeomorph P J).symm p.val.1).1,
    ((polarLongitudeDiffeomorph P J).symm p.val.1).2,p.val.2),p.property⟩
  invFun q := ⟨(polarLongitudeDiffeomorph P J (q.val.1,q.val.2.1),q.val.2.2),q.property⟩
  left_inv p := by
    apply Subtype.ext
    change ((polarLongitudeDiffeomorph P J) ((polarLongitudeDiffeomorph P J).symm p.val.1),p.val.2)=p.val
    rw [Diffeomorph.apply_symm_apply]
  right_inv q := by
    apply Subtype.ext
    change (((polarLongitudeDiffeomorph P J).symm ((polarLongitudeDiffeomorph P J) (q.val.1,q.val.2.1))).1,
      ((polarLongitudeDiffeomorph P J).symm ((polarLongitudeDiffeomorph P J) (q.val.1,q.val.2.1))).2,q.val.2.2)=q.val
    rw [Diffeomorph.symm_apply_apply]
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff longitudePolarStrip _).mp
    have hq : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ((𝓡 1).prod (𝓡 1)) ∞
        (fun p : longitudeProductStrip => (polarLongitudeDiffeomorph P J).symm p.val.1) :=
      (polarLongitudeDiffeomorph P J).symm.contMDiff.comp contMDiff_subtype_val.fst
    exact hq.fst.prodMk (hq.snd.prodMk contMDiff_subtype_val.snd)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff longitudeProductStrip _).mp
    exact ((polarLongitudeDiffeomorph P J).contMDiff.comp
      (contMDiff_subtype_val.fst.prodMk contMDiff_subtype_val.snd.fst)).prodMk
      contMDiff_subtype_val.snd.snd

def longitudeCollarDiffeomorph :
    Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3)
      longitudeProductStrip P.image ∞ :=
  (longitudeToPolarCoordinates P J).trans P.coordinates

def longitudeBoundarySection (p : Circle × Circle) : longitudeProductStrip :=
  ⟨(p,0),by change (0:ℝ)<1; norm_num⟩

theorem longitude_collar_boundary (p : Circle × Circle) :
    (longitudeCollarDiffeomorph P J (longitudeBoundarySection p) : E.Carrier) = J.torus p := by
  exact polar_longitude_inverse_parameter P J p

#print axioms longitudeCollarDiffeomorph
#print axioms longitude_collar_boundary
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
