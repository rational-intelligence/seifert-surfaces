import A5NativeOffSeamGraph

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- The whole-piece closure and covering clauses imply density of the
literal complement of the seams and source boundary. -/
theorem native_piece_interiors_dense
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M) :
    Dense (F.seam.carrier ∪ S.boundary)ᶜ := by
  intro x
  have hc : x ∈ ⋃ i, range (F.parametrization i) := by rw [F.covers]; trivial
  obtain ⟨i, hi⟩ := mem_iUnion.mp hc
  rw [F.piece_closure i] at hi
  apply closure_mono (s := F.parametrization i '' (F.domain i).interior) _ hi
  obtain ⟨a, _, he⟩ := F.piece_interior_component i
  rw [he]
  exact connectedComponentIn_subset _ _

/-- Relative density survives taking any open region in the actual
projection chart and centering its coordinates. -/
theorem native_projected_piece_interiors_dense
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M]
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (e : OpenPartialHomeomorph S E2) (a : E2)
    (U : Set E2) (hU : IsOpen U) (heU : ∀ y ∈ U, a + y ∈ e.target) :
    U ⊆ closure {y ∈ U | e.symm (a + y) ∉ F.seam.carrier ∪ S.boundary} := by
  intro y hy
  apply mem_closure_iff_nhds.mpr
  intro V hV
  obtain ⟨W, hWV, hW, hyW⟩ := mem_nhds_iff.mp hV
  let A : Set S := e.source ∩ (fun x => e x - a) ⁻¹' (U ∩ W)
  have hA : IsOpen A :=
    (e.continuousOn.sub continuousOn_const).isOpen_inter_preimage e.open_source (hU.inter hW)
  have hya : e.symm (a + y) ∈ A := by
    refine ⟨e.map_target (heU y hy), ?_⟩
    change e (e.symm (a + y)) - a ∈ U ∩ W
    rw [e.right_inv (heU y hy)]
    rw [add_sub_cancel_left]
    exact ⟨hy, hyW⟩
  obtain ⟨x, hxA, hxoff⟩ := mem_closure_iff_nhds.mp
    (native_piece_interiors_dense F (e.symm (a + y))) A (hA.mem_nhds hya)
  refine ⟨e x - a, hWV hxA.2.2, hxA.2.1, ?_⟩
  have heq : a + (e x - a) = e x := by abel
  rw [heq, e.left_inv hxA.1]
  exact hxoff

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
