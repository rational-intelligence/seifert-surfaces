import B1ActualGraphMembership_v474
import B1NativeRegularRecovery

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u v
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- Recover the smooth source parameter of an actual embedded interior graph.
Continuity is derived through the original embedding, and smoothness through
its injective differential; no inverse regularity is assumed. -/
theorem native_embedded_graph_parameter_v475
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S M) (q₀ : S)
    (O : Set E2) (hO : IsOpen O) (Γ : E2 → M)
    (hΓ : ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 3) ∞ Γ O)
    (hmaps : ∀ x ∈ O, Γ x ∈ f.image)
    (hinterior : ∀ x ∈ O, Γ x ∉ (𝓡∂ 3).boundary M) :
    ∃ q : E2 → S,
      (∀ x ∈ O, f.toFun (q x) = Γ x) ∧
      (∀ x ∈ O, q x ∉ S.boundary) ∧
      ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ q O := by
  classical
  let q : E2 → S := fun x => if hx : x ∈ O then (hmaps x hx).choose else q₀
  have heq : ∀ x ∈ O, f.toFun (q x) = Γ x := by
    intro x hx
    simp only [q,dif_pos hx]
    exact (hmaps x hx).choose_spec
  have hqcont : ContinuousOn q O := by
    apply f.embedding.isInducing.continuousOn_iff.mpr
    exact hΓ.continuousOn.congr heq
  have hqint : ∀ x ∈ O, q x ∉ S.boundary := by
    intro x hx hxb
    have hh : f.toFun (q x) ∈ (𝓡∂ 3).boundary M := by
      rwa [← f.boundary_preimage] at hxb
    rw [heq x hx] at hh
    exact hinterior x hx hh
  refine ⟨q,heq,hqint,?_⟩
  intro x hx
  have hcomp : ContMDiffAt 𝓘(ℝ,E2) (𝓡∂ 3) ∞ (f.toFun ∘ q) x := by
    apply (hΓ.contMDiffAt (hO.mem_nhds hx)).congr_of_eventuallyEq
    exact Filter.eventuallyEq_of_mem (hO.mem_nhds hx) (fun y hy => heq y hy)
  exact (B1Bridges.proper_smooth_embedding_interior_parameter_smooth f q x
    ((hqcont x hx).continuousAt (hO.mem_nhds hx)) (hqint x hx) hcomp).contMDiffWithinAt

variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

/-- Both exact B1 collar graphs are smooth interior parametrizations in the
actual exterior manifold. -/
theorem actual_halfdisc_graph_smooth_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 3) ∞
      (fun x => D.collar (localCircle D s (x 0),x 1,localHeight D s x)) (halfDisc W.R) ∧
    ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 3) ∞
      (fun x => D.collar (localCircle D s (x 0),x 1,0)) (halfDisc W.R) := by
  have h0 : ContDiff ℝ ∞ (fun x : E2 => x 0) := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
  have h1 : ContDiff ℝ ∞ (fun x : E2 => x 1) := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff
  have hcircle : ContMDiff 𝓘(ℝ,E2) (𝓡 1) ∞ (fun x : E2 => localCircle D s (x 0)) :=
    contMDiff_const.mul (contMDiff_circleExp.comp
      (((contDiff_const.mul h0).div_const D.leafLength).contMDiff))
  have hhalfU : halfDisc W.R ⊆ W.U := fun x hx =>
    W.U_contains ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  have hprea : ContMDiffOn 𝓘(ℝ,E2) ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) ∞
      (fun x => (localCircle D s (x 0),x 1,localHeight D s x)) (halfDisc W.R) :=
    hcircle.contMDiffOn.prodMk (h1.contMDiff.contMDiffOn.prodMk
      (W.height_smooth.mono hhalfU).contMDiffOn)
  have hpreb : ContMDiffOn 𝓘(ℝ,E2) ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) ∞
      (fun x : E2 => (localCircle D s (x 0),x 1,(0 : ℝ))) (halfDisc W.R) :=
    hcircle.contMDiffOn.prodMk (h1.contMDiff.contMDiffOn.prodMk contMDiffOn_const)
  constructor
  · exact D.collar_smooth.comp hprea (fun x hx =>
      ⟨⟨(actual_halfdisc_radial_membership_v474 D s W x hx).1.le,
         (actual_halfdisc_radial_membership_v474 D s W x hx).2.le⟩,
        D.graph_inside _ _ ⟨(actual_halfdisc_radial_membership_v474 D s W x hx).1.le,
         (actual_halfdisc_radial_membership_v474 D s W x hx).2.le⟩⟩)
  · exact D.collar_smooth.comp hpreb (fun x hx =>
      ⟨⟨(actual_halfdisc_radial_membership_v474 D s W x hx).1.le,
         (actual_halfdisc_radial_membership_v474 D s W x hx).2.le⟩,
        by simpa using D.eta_pos⟩)

/-- The original neat embeddings recover genuine smooth graph coordinates on
both surfaces, with exact ambient maps and interior source points. -/
theorem actual_halfdisc_graph_source_parameters_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    (∃ q : E2 → D.A.1.surface,
      (∀ x ∈ halfDisc W.R, D.A.1.embedding.toFun (q x) =
        D.collar (localCircle D s (x 0),x 1,localHeight D s x)) ∧
      (∀ x ∈ halfDisc W.R, q x ∉ D.A.1.surface.boundary) ∧
      ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ q (halfDisc W.R)) ∧
    (∃ q : E2 → D.B.1.surface,
      (∀ x ∈ halfDisc W.R, D.B.1.embedding.toFun (q x) =
        D.collar (localCircle D s (x 0),x 1,0)) ∧
      (∀ x ∈ halfDisc W.R, q x ∉ D.B.1.surface.boundary) ∧
      ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ q (halfDisc W.R)) := by
  have hO : IsOpen (halfDisc W.R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  obtain ⟨ha,hb⟩ := actual_halfdisc_graph_smooth_v475 D s W
  exact ⟨native_embedded_graph_parameter_v475 (ProperSmoothEmbedding.ofNeat D.A.1.embedding)
      ((D.A.1.boundaryCircle 0).toFun 1) _ hO _ ha
      (fun x hx => (actual_halfdisc_graph_membership_v474 D s W x hx).1)
      (fun x hx => (actual_halfdisc_graph_membership_v474 D s W x hx).2.2.1),
    native_embedded_graph_parameter_v475 (ProperSmoothEmbedding.ofNeat D.B.1.embedding)
      ((D.B.1.boundaryCircle 0).toFun 1) _ hO _ hb
      (fun x hx => (actual_halfdisc_graph_membership_v474 D s W x hx).2.1)
      (fun x hx => (actual_halfdisc_graph_membership_v474 D s W x hx).2.2.2)⟩

#print axioms native_embedded_graph_parameter_v475
#print axioms actual_halfdisc_graph_smooth_v475
#print axioms actual_halfdisc_graph_source_parameters_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
