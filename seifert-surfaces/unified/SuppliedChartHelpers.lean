import CollarHelpers

set_option maxSynthPendingDepth 3
set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers.CollarCutHelpers
open Foundations MetricFoundations
noncomputable section

theorem cut_boundary_exact_level {K : OrientedKnot} {T : TubularNeighborhood K}
    {F : SphereSpanningSurface.{0} K} {R : FramedRibbon T F} (C : CutSurface R) :
    (∀ x z, C.inclusion x = R.collar (z, halfTime) ↔ x = C.boundary.toFun z) ∧
    (∀ x, x ∈ C.surface.boundary ↔ ∃ z, C.inclusion x = R.collar (z, halfTime)) ∧
    (∀ z (t : Time), 1 / 2 ≤ (t : ℝ) → R.collar (z, t) ∈ cutSet R) ∧
    (∀ z (t : Time), 1 / 2 ≤ (t : ℝ) → ∃! x, C.inclusion x = R.collar (z, t)) := by
  have hbd (z : Circle) : C.inclusion (C.boundary.toFun z) = R.collar (z, halfTime) := by
    obtain ⟨t, ht, heq⟩ := C.boundary_graph z
    have htime : t = halfTime := Subtype.ext ht
    simpa [htime] using heq
  have hcut (z : Circle) (t : Time) (ht : 1 / 2 ≤ (t : ℝ)) :
      R.collar (z, t) ∈ cutSet R := by
    rintro ⟨p, hp, heq⟩
    have heq' := R.collar_embedding.isEmbedding.injective heq
    subst p
    exact (not_lt_of_ge ht) hp
  refine ⟨?_, ?_, hcut, ?_⟩
  · intro x z
    constructor
    · intro hx
      exact C.embedding.injective (hx.trans (hbd z).symm)
    · rintro rfl
      exact hbd z
  · intro x
    rw [← C.boundary_covers]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, hbd z⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, (C.embedding.injective ((hbd z).trans hz.symm))⟩
  · intro z t ht
    obtain ⟨x, hx⟩ : ∃ x, C.inclusion x = R.collar (z, t) := by
      have hm := hcut z t ht
      rw [← C.image_eq] at hm
      exact hm
    exact ⟨x, hx, fun y hy => C.embedding.injective (hy.trans hx.symm)⟩

theorem affine_half_time_mem (t : Time) : 1 / 2 + (t : ℝ) / 4 ∈ Icc (0 : ℝ) 1 := by
  constructor <;> linarith [t.property.1, t.property.2]
def affineHalfTime (t : Time) : Time := ⟨1 / 2 + (t : ℝ) / 4, affine_half_time_mem t⟩


structure CollarModelBridge where
  homeo : (Euc 1 × EuclideanHalfSpace 1) ≃ₜ EuclideanHalfSpace 2
  linear : (Euc 1 × Euc 1) ≃L[ℝ] Euc 2
  formula : ∀ p, (𝓡∂ 2) (homeo p) = !₂[((𝓡∂ 1) p.2) 0, p.1 0]
  linear_formula : ∀ p, linear p = !₂[p.2 0, p.1 0]
  compatible : ∀ p, (𝓡∂ 2) (homeo p) = linear (CollarModel p)

abbrev PolarModel := (𝓡 1).prod ((𝓡 1).prod (𝓡∂ 1))
abbrev PolarDomain := Circle × (Circle × Time)
structure PolarModelBridge where
  homeo : (Euc 1 × (Euc 1 × EuclideanHalfSpace 1)) ≃ₜ EuclideanHalfSpace 3
  linear : (Euc 1 × (Euc 1 × Euc 1)) ≃L[ℝ] Euc 3
  formula : ∀ p, (𝓡∂ 3) (homeo p) = !₂[((𝓡∂ 1) p.2.2) 0, p.1 0, p.2.1 0]
  linear_formula : ∀ p, linear p = !₂[p.2.2 0, p.1 0, p.2.1 0]
  compatible : ∀ p, (𝓡∂ 3) (homeo p) = linear (PolarModel p)

structure GivenCutHalfCollar {K : OrientedKnot} {T : TubularNeighborhood K}
    {F : SphereSpanningSurface.{0} K} {R : FramedRibbon T F} (C : CutSurface R) where
  map : Circle × Time → C.surface
  equation : ∀ p, C.inclusion (map p) = R.collar (p.1, affineHalfTime p.2)
  unique : ∀ p x, C.inclusion x = R.collar (p.1, affineHalfTime p.2) ↔ x = map p
  boundary : ∀ z, map (z, 0) = C.boundary.toFun z
  inward : ∀ z, 0 < inwardCoordinate (C.boundary.toFun z)
    (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => map (z, t)) 0 timeUnit)
  continuous : Continuous map
  embedding : Manifold.IsSmoothEmbedding CollarModel (𝓡∂ 2) ∞ map
  image : TopologicalSpace.Opens C.surface
  image_eq : (image : Set C.surface) = map '' {p : Circle × Time | (p.2 : ℝ) < 1}
  coordinates : Diffeomorph CollarModel (𝓡∂ 2) (openTimeStrip 1) image ∞
  coordinates_eq : ∀ p, (coordinates p : C.surface) = map p.val
  model : CollarModelBridge
  derivative_equation : ∀ p (w : TangentSpace CollarModel p),
    mfderiv (𝓡∂ 2) (𝓡∂ 2) C.inclusion (map p)
      (mfderiv CollarModel (𝓡∂ 2) map p w) =
    mfderiv CollarModel (𝓡∂ 2) (fun q => R.collar (q.1, affineHalfTime q.2)) p w

theorem polar_radius_bounds (t : Time) :
    0 ≤ 1 + (t : ℝ) / 2 ∧ 1 + (t : ℝ) / 2 < 2 := by
  constructor <;> linarith [t.property.1, t.property.2]
def polarTubePoint (p : PolarDomain) : TubeDomain :=
  (p.1, radialDisk p.2.1 (1 + (p.2.2 : ℝ) / 2)
    (polar_radius_bounds p.2.2).1 (polar_radius_bounds p.2.2).2)

theorem polar_point_in_exterior {K : OrientedKnot} (T : TubularNeighborhood K) (p : PolarDomain) :
    T.tube 0 (polarTubePoint p) ∈ T.exteriorSet := by
  intro hm
  obtain ⟨i, hi⟩ := mem_iUnion.mp hm
  have hi0 : i = 0 := Subsingleton.elim _ _
  subst i
  obtain ⟨q, hq, heq⟩ := hi
  have hqp := (T.smoothEmbedding 0).isEmbedding.injective heq
  subst q
  have hn : ‖((polarTubePoint p).2 : Euc 2)‖ = 1 + (p.2.2 : ℝ) / 2 := by
    change ‖(1 + (p.2.2 : ℝ) / 2) • unitVector p.2.1‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (polar_radius_bounds p.2.2).1,
      unitVector_norm, mul_one]
  change ‖((polarTubePoint p).2 : Euc 2)‖ < 1 at hq
  rw [hn] at hq
  linarith [p.2.2.property.1]

def givenExteriorPolarMap {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (p : PolarDomain) : E.Carrier :=
  ⟨T.tube 0 (polarTubePoint p), polar_point_in_exterior T p⟩

def exteriorPolarRegion {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) : Set E.Carrier :=
  {x | ∃ p : TubeDomain, T.tube 0 p = E.toSphere x ∧ ‖(p.2 : Euc 2)‖ < 3 / 2}
theorem polar_strip_open : IsOpen {p : PolarDomain | (p.2.2 : ℝ) < 1} := by
  exact isOpen_lt
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)) continuous_const
def openPolarStrip : TopologicalSpace.Opens PolarDomain :=
  ⟨{p | (p.2.2 : ℝ) < 1}, polar_strip_open⟩

structure GivenExteriorPolarCollar {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (D : TubeCoordinates T) where
  image : TopologicalSpace.Opens E.Carrier
  image_eq : (image : Set E.Carrier) = exteriorPolarRegion E
  coordinates : Diffeomorph PolarModel (𝓡∂ 3) openPolarStrip image ∞
  equation : ∀ p, (coordinates p : E.Carrier) = givenExteriorPolarMap E p.val
  model : PolarModelBridge
  tubeInverse : image → TubeDomain
  tube_inverse_eq : ∀ x (y : tubeImageOpen T), (y : ThreeSphere) = E.toSphere x.val →
    tubeInverse x = D.map.symm y
  inverse_formula : ∀ x,
    let p := coordinates.symm x
    let q := tubeInverse x
    p.val.1 = q.1 ∧
      unitVector p.val.2.1 = ‖(q.2 : Euc 2)‖⁻¹ • (q.2 : Euc 2) ∧
      (p.val.2.2 : ℝ) = 2 * (‖(q.2 : Euc 2)‖ - 1)
  radius_lower : ∀ x, 1 ≤ ‖((tubeInverse x).2 : Euc 2)‖
  smooth : ContMDiff PolarModel (𝓡∂ 3) ∞ (givenExteriorPolarMap E)
  boundary : ∀ z theta, givenExteriorPolarMap E (z, theta, 0) ∈ (𝓡∂ 3).boundary E.Carrier
  normal_positive : ∀ z theta,
    0 < inwardCoordinate (givenExteriorPolarMap E (z, theta, 0))
      (mfderiv (𝓡∂ 1) (𝓡∂ 3) (fun t => givenExteriorPolarMap E (z, theta, t)) 0 timeUnit)

end
end SeifertSurfaces.LongitudeProducers.CollarCutHelpers
