import A7HalfSpaceExtensionV464
import EndpointGeometry
import Section5GeometricDefinitions
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.A7Support
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

theorem boundary3_coordinate_local_extension {F : M → E3} {W : Set M} (hW : IsOpen W)
    (hF : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ,E3) ∞ F W) (x : M) (hx : x ∈ W) :
    ∃ g : E3 → E3, ContDiff ℝ ∞ g ∧
      g =ᶠ[𝓝[range (𝓡∂ 3)] (extChartAt (𝓡∂ 3) x x)] (F ∘ (extChartAt (𝓡∂ 3) x).symm) ∧
      HasFDerivAt g
        ((tangentSpaceCastModel 𝓘(ℝ,E3) (F x)).toContinuousLinearMap.comp
          ((mfderiv (𝓡∂ 3) 𝓘(ℝ,E3) F x).comp
            (tangentSpaceCastModel (𝓡∂ 3) x).symm.toContinuousLinearMap))
        (extChartAt (𝓡∂ 3) x x) := by
  let I := 𝓡∂ 3
  let c := chartAt (EuclideanHalfSpace 3) x
  let e := extChartAt I x
  let B : Set E3 := I.symm ⁻¹' c.target
  have hB : IsOpen B := c.open_target.preimage I.continuous_symm
  have hcB : ContinuousOn e.symm B := by
    apply c.continuousOn_symm.comp I.continuous_symm.continuousOn
    exact fun _ hz => hz
  let U : Set E3 := B ∩ e.symm ⁻¹' W
  have hU : IsOpen U := hcB.isOpen_inter_preimage hB hW
  have hxU : e x ∈ U := by
    refine ⟨?_,?_⟩
    · change I.symm (I (c x)) ∈ c.target
      rw [I.left_inv]
      exact c.map_source (mem_chart_source (EuclideanHalfSpace 3) x)
    · change e.symm (e x) ∈ W
      rwa [e.left_inv (mem_extChartAt_source x)]
  have hφ : ContDiffOn ℝ ∞ (F ∘ e.symm) (U ∩ range I) := by
    have hes : ContMDiffOn 𝓘(ℝ,E3) I ∞ e.symm (U ∩ range I) := by
      apply (contMDiffOn_extChartAt_symm x).mono
      intro z hz
      rw [extChartAt_target]
      exact ⟨hz.1.1,hz.2⟩
    exact (hF.comp hes (fun _ hz => hz.1.2)).contDiffOn
  obtain ⟨g,hg,hge⟩ := exists_contDiff_extension_halfspace_local hU hφ hxU
  let D : E3 →L[ℝ] E3 :=
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

section Source
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixC
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- A smooth extension of the literal warped coordinates of the actual exterior
inclusion, with the exact native derivative and a nonsingular Jacobian. -/
theorem source_boundary_warped_extension
    (H : Section4.SourceGeometry E) (p : E.Carrier)
    (C : WarpedBoundaryCollar H.ambient.extension (range E.toSphere))
    (hp : E.toSphere p ∈ C.coordinates.chart.source) :
    ∃ f : E3 → E3, ContDiff ℝ ∞ f ∧
      f =ᶠ[𝓝[range (𝓡∂ 3)] (extChartAt (𝓡∂ 3) p p)]
        (C.coordinates.chart ∘ E.toSphere ∘ (extChartAt (𝓡∂ 3) p).symm) ∧
      f (extChartAt (𝓡∂ 3) p p) = C.coordinates.chart (E.toSphere p) ∧
      Function.Bijective (fderiv ℝ f (extChartAt (𝓡∂ 3) p p)) := by
  let F : E.Carrier → E3 := C.coordinates.chart ∘ E.toSphere
  let W := E.toSphere ⁻¹' C.coordinates.chart.source
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) 𝓘(ℝ, E3) ∞ E.toSphere := E.inclusion
  have hW : IsOpen W := C.coordinates.chart.open_source.preimage hinc.isEmbedding.continuous
  have hF : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, E3) ∞ F W :=
    C.coordinates.smooth.comp hinc.isImmersion.contMDiff.contMDiffOn (fun _ hz => hz)
  obtain ⟨f, hf, heq, hder⟩ := boundary3_coordinate_local_extension hW hF p hp
  refine ⟨f, hf, heq, ?_, ?_⟩
  · have he := heq.self_of_nhdsWithin (show extChartAt (𝓡∂ 3) p p ∈ range (𝓡∂ 3) from mem_range_self _)
    change f (extChartAt (𝓡∂ 3) p p) =
      C.coordinates.chart (E.toSphere ((extChartAt (𝓡∂ 3) p).symm (extChartAt (𝓡∂ 3) p p))) at he
    rwa [(extChartAt (𝓡∂ 3) p).left_inv (mem_extChartAt_source p)] at he
  · rw [hder.fderiv]
    have hchartMD : C.coordinates.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
      ⟨C.coordinates.smooth.mdifferentiableOn (by simp),
        C.coordinates.inverse_smooth.mdifferentiableOn (by simp)⟩
    have hFi : Injective (mfderiv (𝓡∂ 3) 𝓘(ℝ, E3) F p) := by
      rw [mfderiv_comp p (hchartMD.mdifferentiableAt hp)
        (hinc.isImmersion.contMDiff.mdifferentiableAt (by simp))]
      exact (hchartMD.mfderiv_bijective hp).1.comp
        (hinc.isImmersion.mfderiv_injective (by simp) p)
    have hinj : Injective
        ((tangentSpaceCastModel 𝓘(ℝ, E3) (F p)).toContinuousLinearMap.comp
          ((mfderiv (𝓡∂ 3) 𝓘(ℝ, E3) F p).comp
            (tangentSpaceCastModel (𝓡∂ 3) p).symm.toContinuousLinearMap)) :=
      (tangentSpaceCastModel 𝓘(ℝ, E3) (F p)).injective.comp
        (hFi.comp (tangentSpaceCastModel (𝓡∂ 3) p).symm.injective)
    exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- An actual ambient chart extends the very same native boundary coordinates
along the exterior inclusion on a neighborhood of the supplied point. -/
theorem source_boundary_ambient_chart
    (H : Section4.SourceGeometry E) (p : E.Carrier)
    (C : WarpedBoundaryCollar H.ambient.extension (range E.toSphere))
    (hp : E.toSphere p ∈ C.coordinates.chart.source) :
    ∃ c : SmoothAmbientChart ThreeSphere,
      E.toSphere p ∈ c.chart.source ∧
      c.chart (E.toSphere p) = extChartAt (𝓡∂ 3) p p ∧
      ∀ᶠ q in 𝓝 p,
        E.toSphere q ∈ c.chart.source ∧
        c.chart (E.toSphere q) = extChartAt (𝓡∂ 3) p q := by
  obtain ⟨f, hf, hfeq, hfp, hfb⟩ := source_boundary_warped_extension H p C hp
  let a := extChartAt (𝓡∂ 3) p p
  let A : E3 ≃L[ℝ] E3 := ContinuousLinearEquiv.ofBijective (fderiv ℝ f a)
    (LinearMap.ker_eq_bot.mpr hfb.1) (LinearMap.range_eq_top.mpr hfb.2)
  have hfd : HasFDerivAt f A.toContinuousLinearMap a := by
    change HasFDerivAt f (fderiv ℝ f a) a
    exact (hf.differentiable (by simp) a).hasFDerivAt
  obtain ⟨e, hae, _, he, hei, heq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv
      hf.contDiffOn isOpen_univ (mem_univ a) hfd
  let c : SmoothAmbientChart ThreeSphere := {
    chart := C.coordinates.chart.trans e.symm
    smooth := hei.contMDiffOn.comp
      (C.coordinates.smooth.mono inter_subset_left) (fun _ hz => hz.2)
    inverse_smooth := C.coordinates.inverse_smooth.comp
      (he.contMDiffOn.mono inter_subset_left) (fun _ hz => hz.2) }
  have hepa : e a = C.coordinates.chart (E.toSphere p) := (heq a).trans hfp
  have hpc : E.toSphere p ∈ c.chart.source := by
    refine ⟨hp, ?_⟩
    change C.coordinates.chart (E.toSphere p) ∈ e.target
    rw [← hepa]
    exact e.map_source hae
  have hca : c.chart (E.toSphere p) = a := by
    change e.symm (C.coordinates.chart (E.toSphere p)) = a
    rw [← hepa, e.left_inv hae]
  refine ⟨c, hpc, hca, ?_⟩
  have ht : Tendsto (extChartAt (𝓡∂ 3) p) (𝓝 p) (𝓝[range (𝓡∂ 3)] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨continuousAt_extChartAt p, Filter.Eventually.of_forall (fun q => mem_range_self _)⟩
  have hevent := hfeq.comp_tendsto ht
  have heventSource : ∀ᶠ q in 𝓝 p, extChartAt (𝓡∂ 3) p q ∈ e.source :=
    (continuousAt_extChartAt p).preimage_mem_nhds (e.open_source.mem_nhds hae)
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) 𝓘(ℝ, E3) ∞ E.toSphere := E.inclusion
  have hCevent : ∀ᶠ q in 𝓝 p, E.toSphere q ∈ C.coordinates.chart.source :=
    hinc.isEmbedding.continuous.continuousAt.preimage_mem_nhds
      (C.coordinates.chart.open_source.mem_nhds hp)
  have hnative : ∀ᶠ q in 𝓝 p, q ∈ (extChartAt (𝓡∂ 3) p).source :=
    (isOpen_extChartAt_source (I := 𝓡∂ 3) p).mem_nhds (mem_extChartAt_source p)
  filter_upwards [hevent, heventSource, hCevent, hnative] with q hq hqe hqc hqn
  have heqC : e (extChartAt (𝓡∂ 3) p q) = C.coordinates.chart (E.toSphere q) := by
    rw [heq]
    change f (extChartAt (𝓡∂ 3) p q) =
      C.coordinates.chart (E.toSphere ((extChartAt (𝓡∂ 3) p).symm
        (extChartAt (𝓡∂ 3) p q))) at hq
    rwa [(extChartAt (𝓡∂ 3) p).left_inv hqn] at hq
  refine ⟨⟨hqc, ?_⟩, ?_⟩
  · change C.coordinates.chart (E.toSphere q) ∈ e.target
    rw [← heqC]
    exact e.map_source hqe
  · change e.symm (C.coordinates.chart (E.toSphere q)) = extChartAt (𝓡∂ 3) p q
    rw [← heqC, e.left_inv hqe]

#print axioms source_boundary_warped_extension
#print axioms source_boundary_ambient_chart
end Source
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
