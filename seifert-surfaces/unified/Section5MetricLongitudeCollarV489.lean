import Section5MetricPolarCollarV489
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

/-- An actual smooth collar of the entire exterior boundary, with the original
longitude parametrization on the boundary and the actual inward distance as
its radial coordinate. The collar extends to the compact closed strip. -/
theorem actual_metric_longitude_collar (G : A7.SourceGeometry E) (J : LongitudeFoliation.{0} E) :
    ∃ U : Set E.Carrier, IsOpen U ∧ (𝓡∂ 3).boundary E.Carrier ⊆ U ∧
    ∃ r : E.Carrier → ℝ, IsInwardDistanceCoordinate G.metric U r ∧
    ∃ b : ℝ, 0 < b ∧ ∃ V : TopologicalSpace.Opens E.Carrier,
    ∃ C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞,
    ∃ m : ((Circle × Circle) × Time) → E.Carrier,
      ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ m ∧
      (∀ q : longitudeProductStrip, m q.val = (C q : E.Carrier)) ∧
      (∀ p : Circle × Circle, m (p,0) = J.torus p) ∧
      (∀ q, m q ∈ U ∧ r (m q) = b*(q.2 : ℝ)) ∧
      ((V : Set E.Carrier) ⊆ U) ∧ (𝓡∂ 3).boundary E.Carrier ⊆ V := by
  obtain ⟨U,hU,hb,r,hr⟩ := actual_inward_distance_near_entire_boundary G J
  obtain ⟨P⟩ := actual_polar_collar_exists (E := E)
  obtain ⟨b,hbpos,V,C,m,hm,hmc,hmb,hmr⟩ := metric_polar_collar P G.metric hU hr hb
  let B : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))
      (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) longitudeProductStrip longitudeProductStrip ∞ :=
    (longitudeToPolarCoordinates P J).trans polarProductAssociation.symm
  let R : ((Circle × Circle) × Time) → ((Circle × Circle) × Time) := fun q =>
    ((polarLongitudeDiffeomorph P J).symm q.1,q.2)
  have hR : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))
      (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ∞ R :=
    ((polarLongitudeDiffeomorph P J).symm.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  have hBR (q : longitudeProductStrip) : (B q).val = R q.val := rfl
  let M := m ∘ R
  have hM : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ M := hm.comp hR
  have hMC (q : longitudeProductStrip) : M q.val = ((B.trans C) q : E.Carrier) := by
    change m (R q.val) = (C (B q) : E.Carrier)
    rw [← hBR,hmc]
  have hMB (p : Circle × Circle) : M (p,0) = J.torus p := by
    change m ((polarLongitudeDiffeomorph P J).symm p,0) = _
    rw [hmb]
    rw [← polar_boundary_parameter_eq]
    exact polar_longitude_inverse_parameter P J p
  refine ⟨U,hU,hb,r,hr,b,hbpos,V,B.trans C,M,hM,hMC,hMB,fun q => hmr (R q),?_,?_⟩
  · intro x hx
    let y : V := ⟨x,hx⟩
    let q := C.symm y
    have heq : m q.val = x := (hmc q).trans
      (congrArg Subtype.val (C.apply_symm_apply y))
    exact heq ▸ (hmr q.val).1
  · intro x hx
    obtain ⟨p,hp⟩ := J.covers_boundary ▸ hx
    have heq : (((B.trans C) (longitudeBoundarySection p)) : E.Carrier) = J.torus p :=
      (hMC (longitudeBoundarySection p)).symm.trans (hMB p)
    exact hp ▸ (heq ▸ ((B.trans C) (longitudeBoundarySection p)).property)

#print axioms actual_metric_longitude_collar
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
