import Section5ActualPolarDonorV488
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
variable {D : TubeCoordinates T} (P : GivenExteriorPolarCollar E D)

theorem tube_norm_one_of_boundary {x : E.Carrier} (hx : x ∈ (𝓡∂ 3).boundary E.Carrier)
    {q : TubeDomain} (hq : T.tube 0 q = E.toSphere x) : ‖(q.2 : Euc 2)‖ = 1 := by
  have hm : E.toSphere x ∈ ⋃ i, T.shell i := by
    rw [← E.boundary_image]
    exact ⟨x,hx,rfl⟩
  obtain ⟨i,p,hp,hpx⟩ := mem_iUnion.mp hm
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hpq := (T.smoothEmbedding 0).isEmbedding.injective (hpx.trans hq.symm)
  change ‖(p.2 : Euc 2)‖ = 1 at hp
  simpa only [hpq] using hp

theorem polar_image_contains_boundary {x : E.Carrier}
    (hx : x ∈ (𝓡∂ 3).boundary E.Carrier) : x ∈ P.image := by
  change x ∈ (P.image : Set E.Carrier)
  rw [P.image_eq]
  have hm : E.toSphere x ∈ ⋃ i, T.shell i := by
    rw [← E.boundary_image]
    exact ⟨x,hx,rfl⟩
  obtain ⟨i,q,hq,hqx⟩ := mem_iUnion.mp hm
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact ⟨q,hqx,by rw [hq]; norm_num⟩

def polarZeroSection (p : Circle × Circle) : {p : PolarDomain // (p.2.2 : ℝ) < 1} :=
  ⟨(p.1,p.2,0),by change (0:ℝ)<1; norm_num⟩

def polarBoundaryParameter (p : Circle × Circle) : E.Carrier :=
  P.coordinates (polarZeroSection p)

theorem polar_boundary_parameter_eq (p : Circle × Circle) :
    polarBoundaryParameter P p = givenExteriorPolarMap E (p.1,p.2,0) := P.equation _

theorem polar_boundary_parameter_smooth :
    ContMDiff ((𝓡 1).prod (𝓡 1)) (𝓡∂ 3) ∞ (polarBoundaryParameter P) := by
  have heq : polarBoundaryParameter P =
      fun p : Circle × Circle => givenExteriorPolarMap E (p.1,p.2,0) := funext (polar_boundary_parameter_eq P)
  rw [heq]
  exact P.smooth.comp (contMDiff_fst.prodMk (contMDiff_snd.prodMk contMDiff_const))

theorem polar_boundary_parameter_injective : Injective (polarBoundaryParameter P) := by
  intro p q hpq
  have h : P.coordinates (polarZeroSection p) = P.coordinates (polarZeroSection q) := Subtype.ext hpq
  have h0 := congrArg Subtype.val (P.coordinates.injective h)
  exact Prod.ext (congrArg (fun z : PolarDomain => z.1) h0) (congrArg (fun x : PolarDomain => x.2.1) h0)

theorem polar_boundary_parameter_boundary (p : Circle × Circle) :
    polarBoundaryParameter P p ∈ (𝓡∂ 3).boundary E.Carrier := by
  rw [polar_boundary_parameter_eq]
  exact P.boundary p.1 p.2

theorem polar_coordinate_zero_of_boundary (x : P.image)
    (hx : (x : E.Carrier) ∈ (𝓡∂ 3).boundary E.Carrier) :
    (((P.coordinates.symm x).val.2.2 : Time) : ℝ) = 0 := by
  let p := P.coordinates.symm x
  have hpx : givenExteriorPolarMap E p.val = (x : E.Carrier) :=
    (P.equation p).symm.trans (congrArg Subtype.val (P.coordinates.apply_symm_apply x))
  have htube : T.tube 0 (polarTubePoint p.val) = E.toSphere x := congrArg E.toSphere hpx
  have hn := tube_norm_one_of_boundary hx htube
  have hrad : ‖((polarTubePoint p.val).2 : Euc 2)‖ = 1 + (p.val.2.2 : ℝ)/2 := by
    change ‖(1+(p.val.2.2:ℝ)/2) • unitVector p.val.2.1‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (polar_radius_bounds p.val.2.2).1,
      unitVector_norm, mul_one]
  change (p.val.2.2 : ℝ) = 0
  linarith

theorem polar_boundary_parameter_range : range (polarBoundaryParameter P) =
    (𝓡∂ 3).boundary E.Carrier := by
  apply Subset.antisymm
  · rintro x ⟨p,rfl⟩
    exact polar_boundary_parameter_boundary P p
  · intro x hx
    let y : P.image := ⟨x,polar_image_contains_boundary P hx⟩
    let p := P.coordinates.symm y
    have ht : p.val.2.2 = 0 := Subtype.ext (polar_coordinate_zero_of_boundary P y hx)
    refine ⟨(p.val.1,p.val.2.1),?_⟩
    have hp : polarZeroSection (p.val.1,p.val.2.1) = p := by
      apply Subtype.ext
      exact Prod.ext rfl (Prod.ext rfl ht.symm)
    change (P.coordinates (polarZeroSection (p.val.1,p.val.2.1)) : E.Carrier) = x
    rw [hp]
    exact congrArg Subtype.val (P.coordinates.apply_symm_apply y)

def polarBoundaryHomeomorph : (Circle × Circle) ≃ₜ ((𝓡∂ 3).boundary E.Carrier) := by
  let f : (Circle × Circle) → ((𝓡∂ 3).boundary E.Carrier) :=
    fun p => ⟨polarBoundaryParameter P p,polar_boundary_parameter_boundary P p⟩
  have hf : Continuous f := (polar_boundary_parameter_smooth P).continuous.subtype_mk _
  have hi : Injective f := fun p q h => polar_boundary_parameter_injective P (congrArg (fun z : (𝓡∂ 3).boundary E.Carrier => (z : E.Carrier)) h)
  apply hf.isClosedEmbedding hi |>.isEmbedding.toHomeomorphOfSurjective
  intro x
  have hx : (x : E.Carrier) ∈ range (polarBoundaryParameter P) :=
    (polar_boundary_parameter_range P).symm ▸ x.property
  obtain ⟨p,hp⟩ := hx
  exact ⟨p,Subtype.ext hp⟩

#print axioms polar_boundary_parameter_range
#print axioms polarBoundaryHomeomorph
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
