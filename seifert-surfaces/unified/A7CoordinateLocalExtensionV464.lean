import A7HalfSpaceExtensionV464
import EndpointGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (𝓡∂ 2) ∞ M]

theorem coordinate_local_extension {F : M → E3} {W : Set M} (hW : IsOpen W)
    (hF : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,E3) ∞ F W) (x : M) (hx : x ∈ W) :
    ∃ g : E2 → E3, ContDiff ℝ ∞ g ∧
      g =ᶠ[𝓝[range (𝓡∂ 2)] (extChartAt (𝓡∂ 2) x x)] (F ∘ (extChartAt (𝓡∂ 2) x).symm) ∧
      HasFDerivAt g
        ((tangentSpaceCastModel 𝓘(ℝ,E3) (F x)).toContinuousLinearMap.comp
          ((mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x).comp
            (tangentSpaceCastModel (𝓡∂ 2) x).symm.toContinuousLinearMap))
        (extChartAt (𝓡∂ 2) x x) := by
  let I := 𝓡∂ 2
  let c := chartAt (EuclideanHalfSpace 2) x
  let e := extChartAt I x
  let B : Set E2 := I.symm ⁻¹' c.target
  have hB : IsOpen B := c.open_target.preimage I.continuous_symm
  have hcB : ContinuousOn e.symm B := by
    apply c.continuousOn_symm.comp I.continuous_symm.continuousOn
    exact fun _ hz => hz
  let U : Set E2 := B ∩ e.symm ⁻¹' W
  have hU : IsOpen U := hcB.isOpen_inter_preimage hB hW
  have hxU : e x ∈ U := by
    refine ⟨?_,?_⟩
    · change I.symm (I (c x)) ∈ c.target
      rw [I.left_inv]
      exact c.map_source (mem_chart_source (EuclideanHalfSpace 2) x)
    · change e.symm (e x) ∈ W
      rwa [e.left_inv (mem_extChartAt_source x)]
  have hφ : ContDiffOn ℝ ∞ (F ∘ e.symm) (U ∩ range I) := by
    have hes : ContMDiffOn 𝓘(ℝ,E2) I ∞ e.symm (U ∩ range I) := by
      apply (contMDiffOn_extChartAt_symm x).mono
      intro z hz
      rw [extChartAt_target]
      exact ⟨hz.1.1,hz.2⟩
    exact (hF.comp hes (fun _ hz => hz.1.2)).contDiffOn
  obtain ⟨g,hg,hge⟩ := exists_contDiff_extension_halfspace_local hU hφ hxU
  let D : E2 →L[ℝ] E3 :=
    (tangentSpaceCastModel 𝓘(ℝ,E3) (F x)).toContinuousLinearMap.comp
      ((mfderiv I 𝓘(ℝ,E3) F x).comp (tangentSpaceCastModel I x).symm.toContinuousLinearMap)
  have hmd : MDifferentiableAt I 𝓘(ℝ,E3) F x :=
    ((hF x hx).contMDiffAt (hW.mem_nhds hx)).mdifferentiableAt (by simp)
  have hr : e x ∈ range I := mem_range_self _
  have hφD : HasFDerivWithinAt (F ∘ e.symm) D (range I) (e x) := by
    simpa only [writtenInExtChartAt,extChartAt_model_space_eq_id,PartialEquiv.refl_coe,
      Function.id_comp] using hmd.hasMFDerivAt.2
  have hgD : HasFDerivWithinAt g D (range I) (e x) :=
    (hge.hasFDerivWithinAt_iff_of_mem hr).2 hφD
  have hud : UniqueDiffWithinAt ℝ (range I) (e x) := I.uniqueDiffOn _ hr
  have hfd : fderiv ℝ g (e x) = D := by
    rw [←fderivWithin_eq_fderiv hud (hg.differentiable (by simp) _),hgD.fderivWithin hud]
  refine ⟨g,hg,hge,?_⟩
  change HasFDerivAt g D (e x)
  rw [←hfd]
  exact (hg.differentiable (by simp) _).hasFDerivAt

end SeifertSurfaces.OriginalEndpoints.A7Support
