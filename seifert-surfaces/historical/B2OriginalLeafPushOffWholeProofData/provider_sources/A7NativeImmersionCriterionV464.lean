import A7NativeBoundarySignV464
import A7HalfSpaceStraighteningV464
import A7NativeImmersionAssemblyV464
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter Manifold
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates
universe u v
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]
  {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

theorem native_transverse_isImmersion {f : S → M}
    (hf : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ f)
    (hinj : ∀ x, Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) f x))
    (hboundary : ∀ y, f y ∈ (𝓡∂ 3).boundary M ↔ y ∈ (𝓡∂ 2).boundary S)
    (htrans : ∀ x ∈ (𝓡∂ 2).boundary S,
      ∃ w : TangentSpace (𝓡∂ 2) x,
        inwardCoordinate (f x) (mfderiv (𝓡∂ 2) (𝓡∂ 3) f x w) ≠ 0) :
    IsImmersion (𝓡∂ 2) (𝓡∂ 3) ∞ f := by
  apply DifferentialGeometry.Topology.Manifold.isImmersion_of_isImmersionAt
  intro x
  let a := extChartAt (𝓡∂ 2) x x
  let b := extChartAt (𝓡∂ 3) (f x) (f x)
  let L := nativeCoordinateDifferential f x
  obtain ⟨g,hg,hge,hd⟩ := native_target_coordinate_extension hf x
  have hga : g a = b := by
    have h := hge.eq_of_nhdsWithin (mem_range_self (chartAt (EuclideanHalfSpace 2) x x))
    change g a = (extChartAt (𝓡∂ 3) (f x)) (f ((extChartAt (𝓡∂ 2) x).symm a)) at h
    rwa [(extChartAt (𝓡∂ 2) x).left_inv (mem_extChartAt_source x)] at h
  have hL : Injective L :=
    (tangentSpaceCastModel (𝓡∂ 3) (f x)).injective.comp
      ((hinj x).comp (tangentSpaceCastModel (𝓡∂ 2) x).symm.injective)
  have hdata : ∃ n : E3, ∃ A : (E2 × ℝ) ≃L[ℝ] E3,
      (∀ q, A q = L q.1 + q.2 • n) ∧
      ∀ e : OpenPartialHomeomorph (E2 × ℝ) E3,
        (a,0) ∈ e.source → (∀ q, e q = g q.1 + q.2 • n) →
        ∀ᶠ y : E3 in 𝓝 (g a),
          0 ≤ straighteningChart e y 0 ↔ 0 ≤ y 0 := by
    by_cases hx : x ∈ (𝓡∂ 2).boundary S
    · obtain ⟨c,hc,hrow⟩ := native_boundary_coordinate_row hf x hx ((hboundary x).2 hx) (htrans x hx)
      obtain ⟨n,hn,A,hA,_⟩ := boundary_completion L hL hc hrow
      have hs := native_coordinate_extension_boundary_sign hf
        (fun y hy => (hboundary y).2 hy) x hx hg hge hd hc hrow
      refine ⟨n,A,hA,?_⟩
      intro e hea heq
      exact straighteningChart_boundary_halfspace e hea heq hn hs
    · obtain ⟨n,_,_,A,hA⟩ := normal_completion L hL (innerSL ℝ)
        (fun v hv => real_inner_self_pos.mpr hv)
      have ha : 0 < a 0 := by
        have hnn : 0 ≤ a 0 := (chartAt (EuclideanHalfSpace 2) x x).property
        have hne : a 0 ≠ 0 := by
          intro hz
          exact hx ((chart_boundary_coordinate_iff x x (mem_chart_source _ _)).2 hz)
        exact lt_of_le_of_ne hnn (Ne.symm hne)
      have hb : 0 < b 0 := by
        have hnn : 0 ≤ b 0 := (chartAt (EuclideanHalfSpace 3) (f x) (f x)).property
        have hne : b 0 ≠ 0 := by
          intro hz
          exact hx ((hboundary x).1 ((chart_boundary_coordinate_iff (f x) (f x) (mem_chart_source _ _)).2 hz))
        exact lt_of_le_of_ne hnn (Ne.symm hne)
      refine ⟨n,A,hA,?_⟩
      intro e hea heq
      have hgr := straighteningChart_graph e hea heq
      have hct : ContinuousAt (straighteningChart e) (g a) :=
        (straighteningChart e).continuousOn.continuousAt
          ((straighteningChart e).open_source.mem_nhds hgr.1)
      have hβa : 0 < straighteningChart e (g a) 0 := by
        rw [hgr.2.1,standardPlaneEquiv_zero]
        exact ha
      have hβpos : ∀ᶠ y in 𝓝 (g a), 0 < straighteningChart e y 0 :=
        (isOpen_lt continuous_const ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0))).mem_nhds hβa
          |> hct.preimage_mem_nhds
      have hypos : ∀ᶠ y : E3 in 𝓝 (g a), 0 < y 0 := by
        apply (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0)).mem_nhds
        rwa [hga]
      filter_upwards [hβpos,hypos] with y hy hz
      exact ⟨fun _ => le_of_lt hz,fun _ => le_of_lt hy⟩
  obtain ⟨n,A,hA,hhalf⟩ := hdata
  obtain ⟨e,hea,he,hei,heq⟩ := local_normal_extension hg hd n A hA
  have hβ := straighteningChart_smooth e he hei
  have hgr := straighteningChart_graph e hea heq
  obtain ⟨β,hbβ,hβs,hβis,hβim,hβeq⟩ :=
    restrict_halfspace_straightening hgr.1 hβ.1 hβ.2 (hhalf e hea heq)
  have hgraph : ∀ᶠ z : E2 in 𝓝 a,
      g z ∈ β.source ∧ β (g z) = standardPlaneEquiv (z,0) := by
    have hm : ∀ᶠ z : E2 in 𝓝 a, g z ∈ β.source :=
      hg.continuous.continuousAt.preimage_mem_nhds (β.open_source.mem_nhds hbβ)
    filter_upwards [hgr.2.2,hm] with z hz hmz
    exact ⟨hmz,(hβeq (g z)).trans hz.2⟩
  exact native_immersion_of_halfspace_straightening hf x g hg.continuous hge β hβs hβis hβim hgraph

end SeifertSurfaces.OriginalEndpoints.A7Support
