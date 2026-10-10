import Section5BoundaryMetricExtensionV481
import Section5DefiningFunctionHessianV481
import A7NativeChartBoundaryV464

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology BigOperators
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- The actual warped radial function vanishes exactly on the native boundary
and is nonnegative on the inward halfspace, in an actual extending chart. -/
theorem source_boundary_radial_germ
    (H : Section4.SourceGeometry E) (p : E.Carrier)
    (C : WarpedBoundaryCollar H.ambient.extension (range E.toSphere))
    (hp : E.toSphere p ∈ C.coordinates.chart.source)
    (c : SmoothAmbientChart ThreeSphere) (hpc : E.toSphere p ∈ c.chart.source)
    (hcp : c.chart (E.toSphere p) = extChartAt (𝓡∂ 3) p p)
    (hev : ∀ᶠ q in 𝓝 p, E.toSphere q ∈ c.chart.source ∧
      c.chart (E.toSphere q) = extChartAt (𝓡∂ 3) p q) :
    ∀ᶠ z in 𝓝 (extChartAt (𝓡∂ 3) p p),
      (z 0 = 0 → (C.radial ∘ c.chart.symm) z = 0) ∧
      (0 ≤ z 0 → 0 ≤ (C.radial ∘ c.chart.symm) z) := by
  let e := extChartAt (𝓡∂ 3) p
  let a := e p
  have hepa : e.symm a = p := e.left_inv (mem_extChartAt_source p)
  let B : Set E3 := (𝓡∂ 3).symm ⁻¹' (chartAt (EuclideanHalfSpace 3) p).target
  have hBo : IsOpen B := (chartAt (EuclideanHalfSpace 3) p).open_target.preimage (𝓡∂ 3).continuous_symm
  have haB : a ∈ B := by
    change (𝓡∂ 3).symm ((𝓡∂ 3) (chartAt (EuclideanHalfSpace 3) p p)) ∈
      (chartAt (EuclideanHalfSpace 3) p).target
    rw [(𝓡∂ 3).left_inv]
    exact (chartAt (EuclideanHalfSpace 3) p).map_source (mem_chart_source _ p)
  have hes : Tendsto e.symm (𝓝 a) (𝓝 p) := by
    have hh := (continuousAt_extChartAt_symm (I := 𝓡∂ 3) p).tendsto
    change Tendsto e.symm (𝓝 a) (𝓝 (e.symm a)) at hh
    rwa [hepa] at hh
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) 𝓘(ℝ, E3) ∞ E.toSphere := E.inclusion
  have hCnear : ∀ᶠ q in 𝓝 p, E.toSphere q ∈ C.coordinates.chart.source :=
    hinc.isEmbedding.continuous.continuousAt.preimage_mem_nhds
      (C.coordinates.chart.open_source.mem_nhds hp)
  filter_upwards [hBo.mem_nhds haB, hes.eventually hev, hes.eventually hCnear] with z hzB hzE hzC
  have htarget (hz : 0 ≤ z 0) : z ∈ e.target := by
    rw [extChartAt_target]
    refine ⟨hzB, ?_⟩
    simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hz
  have hid (hz : 0 ≤ z 0) : c.chart.symm z = E.toSphere (e.symm z) := by
    have hcoords : c.chart (E.toSphere (e.symm z)) = z := hzE.2.trans (e.right_inv (htarget hz))
    exact (congrArg c.chart.symm hcoords.symm).trans (c.chart.left_inv hzE.1)
  constructor
  · intro hz0
    rw [Function.comp_apply, hid hz0.ge]
    apply (C.boundary_identification _ hzC).mp
    apply (H.ambient.boundary_exact _).mpr
    apply (A7Support.chart_boundary_coordinate_iff p (e.symm z) ?_).mpr
    · rw [e.right_inv (htarget hz0.ge)]
      exact hz0
    · have hh := e.map_target (htarget hz0.ge)
      change e.symm z ∈ (extChartAt (𝓡∂ 3) p).source at hh
      simpa only [extChartAt_source] using hh
  · intro hz0
    rw [Function.comp_apply, hid hz0]
    exact (C.region_identification _ hzC).mp (mem_range_self _)

/-- The actual warped radial covector is nonzero in every overlapping actual
ambient chart, by invertibility of the actual coordinate transition. -/
theorem warped_radial_differential_nonzero
    (H : Section4.SourceGeometry E)
    (C : WarpedBoundaryCollar H.ambient.extension (range E.toSphere))
    (c : SmoothAmbientChart ThreeSphere) (y : E3) (hy : y ∈ c.chart.target)
    (hp : c.chart.symm y ∈ C.coordinates.chart.source) :
    fderiv ℝ (C.radial ∘ c.chart.symm) y ≠ 0 := by
  have hcMD : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
    ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
  have hdMD : C.coordinates.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
    ⟨C.coordinates.smooth.mdifferentiableOn (by simp),
      C.coordinates.inverse_smooth.mdifferentiableOn (by simp)⟩
  let F := C.coordinates.chart ∘ c.chart.symm
  have hF : ContDiffAt ℝ ∞ F y :=
    ((C.coordinates.smooth.contMDiffAt (C.coordinates.chart.open_source.mem_nhds hp)).comp y
      (c.inverse_smooth.contMDiffAt (c.chart.open_target.mem_nhds hy))).contDiffAt
  have hdF : fderiv ℝ F y =
      (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) C.coordinates.chart (c.chart.symm y)).comp
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y) := by
    have hh := mfderiv_comp y (hdMD.mdifferentiableAt hp) (hcMD.mdifferentiableAt_symm hy)
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hFbij : Function.Bijective (fderiv ℝ F y) := by
    rw [hdF]
    exact (hdMD.mfderiv_bijective hp).comp (hcMD.symm.mfderiv_bijective hy)
  have hradF : C.radial ∘ c.chart.symm =ᶠ[𝓝 y] (fun z : E3 => F z 0) := by
    have hn := (c.chart.continuousOn_symm.continuousAt (c.chart.open_target.mem_nhds hy)).preimage_mem_nhds
      (C.coordinates.chart.open_source.mem_nhds hp)
    filter_upwards [hn] with z hz
    exact C.radial_coordinate _ hz
  have hcomp (v : E3) : fderiv ℝ (fun z : E3 => F z 0) y v = (fderiv ℝ F y v) 0 := by
    have hd := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0).hasFDerivAt.comp y
      (hF.differentiableAt (by simp)).hasFDerivAt
    exact congrArg (fun L : E3 →L[ℝ] ℝ => L v) hd.fderiv
  intro hz
  obtain ⟨v, hv⟩ := hFbij.2 (coordinateVector 3 0)
  have he := hcomp v
  rw [← hradF.fderiv_eq, hz, zero_apply, hv] at he
  norm_num [coordinateVector, EuclideanSpace.single, PiLp.single_apply] at he

/-- The full strict boundary convexity consumed by Appendix B follows from the
actual standing warped collar geometry, without adding a convexity premise. -/
theorem source_geometry_strictly_convex (H : Section4.SourceGeometry E) :
    IsStrictlyConvexBoundary H.metric := by
  intro p hpB
  obtain ⟨C, hpC⟩ := H.ambient.collars p hpB
  obtain ⟨c, hpc, hcp, hev, V, hVo, hpV, hVtarget, hmetric, _⟩ :=
    source_boundary_metric_extension H p C hpC
  let a := extChartAt (𝓡∂ 3) p p
  have ha0 : a 0 = 0 :=
    (A7Support.chart_boundary_coordinate_iff p p (mem_chart_source _ p)).mp hpB
  have hcy : a ∈ c.chart.target := hVtarget hpV
  have hpoint : c.chart.symm a = E.toSphere p := by
    exact (congrArg c.chart.symm hcp.symm).trans (c.chart.left_inv hpc)
  have hpC' : c.chart.symm a ∈ C.coordinates.chart.source := hpoint.symm ▸ hpC
  have hR : ContDiffAt ℝ ∞ (C.radial ∘ c.chart.symm) a :=
    ((C.radial_smooth.contMDiffAt (C.coordinates.chart.open_source.mem_nhds hpC')).comp a
      (c.inverse_smooth.contMDiffAt (c.chart.open_target.mem_nhds hcy))).contDiffAt
  have hRa : (C.radial ∘ c.chart.symm) a = 0 := by
    rw [Function.comp_apply, hpoint]
    exact (C.boundary_identification _ hpC).mp ((H.ambient.boundary_exact p).mpr hpB)
  have hgerm := source_boundary_radial_germ H p C hpC c hpc hcp hev
  obtain ⟨k, hk, hdk⟩ := boundary_defining_covector_positive
    (C.radial ∘ c.chart.symm) a ha0 hRa (hR.differentiableAt (by simp))
      (warped_radial_differential_nonzero H C c a hcy hpC') (hgerm.mono fun _ hz => hz.2)
  obtain ⟨hs, hsymm, hpositive⟩ :=
    A4GeometryBridges.actual_chart_tensor_metric_properties H.ambient.extension c
  let G : CoordinateMetric V := {
    tensor := actualChartTensor H.ambient.extension c
    smooth := fun i j => (hs i j).mono hVtarget
    symmetric := fun y hy => hsymm y (hVtarget hy)
    positive := fun y hy => hpositive y (hVtarget hy) }
  refine ⟨V, hVo, G, hpV, hmetric, ?_⟩
  intro w hw hw0
  have hstrict := warped_radial_strict_in_ambient_chart C c a hcy hpC'
    (hpoint.symm ▸ (H.ambient.boundary_exact p).mpr hpB) w hw
      (by rw [hdk w, hw0, mul_zero])
  have hscale := boundary_defining_hessian_scale (actualChartTensor H.ambient.extension c)
    (fun z i j => H.ambient.extension.symm _ _ _) (C.radial ∘ c.chart.symm) a w ha0 hw0
    (hR.of_le (by simp)) (hgerm.mono fun _ hz => hz.1) k hdk
  rw [hscale] at hstrict
  change hessianQuadratic (actualChartTensor H.ambient.extension c) (fun y : E3 => y 0) a w < 0
  nlinarith

#print axioms warped_radial_differential_nonzero
#print axioms source_geometry_strictly_convex
#print axioms source_boundary_radial_germ
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
