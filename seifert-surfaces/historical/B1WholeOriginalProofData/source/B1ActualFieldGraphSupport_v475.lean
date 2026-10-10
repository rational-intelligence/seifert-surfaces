import B1CompactVerticalFlow_v475

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
open DifferentialGeometry.Analysis.ODE
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem native_actual_exterior_flow_eq_self_v475 (X : NativeInteriorSmoothVectorField_v475 E)
    (p : E.Carrier) (hzero : X.field (E.toSphere p) = 0) (t : ℝ) :
    native_actual_exterior_flow_v475 X t p = p := by
  apply Subtype.ext
  change E.toSphere (native_actual_exterior_flow_v475 X t p) = E.toSphere p
  rw [native_actual_exterior_flow_sphere_v475]
  exact curveAt_eq_self_of_eq_zero X.field (X.smooth.of_le (by simp))
    (native_actual_field_complete_v475 X) hzero t

/-- The literal collar graph excludes extra surface sheets from the support
of the ambient vertical field. -/
theorem native_actual_chart_field_support_on_graph_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S E.Carrier)
    (q : E2 → S) (u φ : E2 → ℝ) (A : Set E2)
    (hφA : tsupport φ ⊆ A)
    (hq : ∀ x ∈ A, f.toFun (q x) = localCollar D s (jetPoint (x,u x,0)))
    (c : SmoothAmbientChart ThreeSphere) (X : NativeInteriorSmoothVectorField_v475 E)
    (χ : ThreeSphere → ℝ)
    (hX : ∀ p ∈ c.chart.source, chartDifferential c p (X.field p) =
      χ p • (φ (native_collar_base_v475 (c.chart p)) • coordinateVector 3 2))
    (hXs : closure {p | X.field p ≠ 0} ⊆ c.chart.source)
    (hc : ∀ y ∈ c.chart.target, y ∈ collarDomain D W.R ∧ 0 < y 1 ∧
      c.chart.symm y = E.toSphere (localCollar D s y))
    (hgraph : ∀ y ∈ collarDomain D W.R, localCollar D s y ∈ f.image →
      y 2 = u (native_collar_base_v475 y)) :
    ∀ z ∉ q '' A, X.field (E.toSphere (f.toFun z)) = 0 := by
  intro z hz
  let p : ThreeSphere := E.toSphere (f.toFun z)
  by_cases hp : p ∈ c.chart.source
  · let y := c.chart p
    have hy : y ∈ c.chart.target := c.chart.map_source hp
    have hcp : E.toSphere (localCollar D s y) = p :=
      (hc y hy).2.2.symm.trans (c.chart.left_inv hp)
    have hf : localCollar D s y = f.toFun z := Subtype.ext hcp
    have hyheight : y 2 = u (native_collar_base_v475 y) := hgraph y (hc y hy).1 ⟨z,hf.symm⟩
    have hφzero : φ (native_collar_base_v475 y) = 0 := by
      by_contra hφn
      have hb : native_collar_base_v475 y ∈ A :=
        hφA (subset_tsupport φ (by exact hφn))
      apply hz
      refine ⟨native_collar_base_v475 y,hb,?_⟩
      apply f.embedding.injective
      rw [hq _ hb]
      have hj : jetPoint (native_collar_base_v475 y,u (native_collar_base_v475 y),0) = y := by
        ext i
        fin_cases i <;> simp [jetPoint,native_collar_base_v475,hyheight]
      rw [hj,hf]
    have hd : chartDifferential c p (X.field p) = 0 := by
      rw [hX p hp]
      change χ p • (φ (native_collar_base_v475 y) • coordinateVector 3 2) = 0
      rw [hφzero,zero_smul,smul_zero]
    have hinj := (native_actual_chart_differential_invertible_v475 c p hp).injective
    exact hinj (hd.trans (map_zero _).symm)
  · by_contra hnonzero
    exact hp (hXs (subset_closure hnonzero))

#print axioms native_actual_exterior_flow_eq_self_v475
#print axioms native_actual_chart_field_support_on_graph_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
