import Section5WarpedStrictV481
import NativeWarpedHessian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.PrivateHelpers.C6Native
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]

/-- The actual collar defining function has negative metric Hessian in every
actual ambient chart, on every nonzero vector tangent to its boundary level. -/
theorem warped_radial_strict_in_ambient_chart
    {h : AmbientMetric N} {M : Set N} (C : WarpedBoundaryCollar h M)
    (c : SmoothAmbientChart N) (y : E3) (hy : y ∈ c.chart.target)
    (hp : c.chart.symm y ∈ C.coordinates.chart.source)
    (hb : c.chart.symm y ∈ frontier M)
    (v : E3) (hv : v ≠ 0)
    (ht : fderiv ℝ (C.radial ∘ c.chart.symm) y v = 0) :
    hessianQuadratic (actualChartTensor h c) (C.radial ∘ c.chart.symm) y v < 0 := by
  rw [radial_hessian_chart_transport C.radial C.coordinates c C.radial_coordinate y hy hp v]
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
  have hFy : F y ∈ C.coordinates.chart.target := C.coordinates.chart.map_source hp
  have hrad : C.radial ∘ C.coordinates.chart.symm =ᶠ[𝓝 (F y)] (fun z : E3 => z 0) := by
    filter_upwards [C.coordinates.chart.open_target.mem_nhds hFy] with z hz
    exact (C.radial_coordinate _ (C.coordinates.chart.map_target hz)).trans
      (congrArg (fun w : E3 => w 0) (C.coordinates.chart.right_inv hz))
  have hradF : C.radial ∘ c.chart.symm =ᶠ[𝓝 y] (fun z : E3 => F z 0) := by
    have hn := (c.chart.continuousOn_symm.continuousAt (c.chart.open_target.mem_nhds hy)).preimage_mem_nhds
      (C.coordinates.chart.open_source.mem_nhds hp)
    filter_upwards [hn] with z hz
    exact C.radial_coordinate _ hz
  have hcomp : fderiv ℝ (fun z : E3 => F z 0) y v = (fderiv ℝ F y v) 0 := by
    have hd := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0).hasFDerivAt.comp y
      (hF.differentiableAt (by simp)).hasFDerivAt
    exact congrArg (fun L : E3 →L[ℝ] ℝ => L v) hd.fderiv
  have ht' : (fderiv ℝ F y v) 0 = 0 := by
    rw [← hcomp, ← hradF.fderiv_eq]
    exact ht
  have hn' : fderiv ℝ F y v ≠ 0 := by
    intro he
    exact hv (hFbij.1 (he.trans (map_zero _).symm))
  have hz : F y 0 = 0 := by
    change C.coordinates.chart (c.chart.symm y) 0 = 0
    rw [← C.radial_coordinate _ hp]
    exact (C.boundary_identification _ hp).mp hb
  have heq : hessianQuadratic (actualChartTensor h C.coordinates)
      (C.radial ∘ C.coordinates.chart.symm) (F y) (fderiv ℝ F y v) =
      hessianQuadratic (actualChartTensor h C.coordinates)
        (fun z : E3 => z 0) (F y) (fderiv ℝ F y v) := by
    unfold hessianQuadratic hessianCoefficient partial3
    have hd := hrad.fderiv_eq (𝕜 := ℝ)
    have hpart (b : Fin 3) :
        (fun z => fderiv ℝ (C.radial ∘ C.coordinates.chart.symm) z (coordinateVector 3 b))
          =ᶠ[𝓝 (F y)]
        (fun z => fderiv ℝ (fun w : E3 => w 0) z (coordinateVector 3 b)) :=
      (hrad.fderiv (𝕜 := ℝ)).fun_comp (fun L => L (coordinateVector 3 b))
    have hdd (b : Fin 3) := (hpart b).fderiv_eq (𝕜 := ℝ)
    simp only [hd, hdd]
  change hessianQuadratic (actualChartTensor h C.coordinates)
    (C.radial ∘ C.coordinates.chart.symm) (F y) (fderiv ℝ F y v) < 0
  rw [heq]
  exact warped_coordinate_boundary_strict C (F y) hFy hz _ hn' ht'

theorem radial_hessian_eq_coordinate
    {h : AmbientMetric N} (c : SmoothAmbientChart N) (r : N → ℝ)
    (y : E3) (hrad : r ∘ c.chart.symm =ᶠ[𝓝 y] (fun z : E3 => z 0)) :
    hessianQuadratic (actualChartTensor h c) (r ∘ c.chart.symm) y =
      hessianQuadratic (actualChartTensor h c) (fun z : E3 => z 0) y := by
  unfold hessianQuadratic hessianCoefficient partial3
  have hd := hrad.fderiv_eq (𝕜 := ℝ)
  have hpart (b : Fin 3) :
      (fun z => fderiv ℝ (r ∘ c.chart.symm) z (coordinateVector 3 b)) =ᶠ[𝓝 y]
        (fun z => fderiv ℝ (fun w : E3 => w 0) z (coordinateVector 3 b)) :=
    (hrad.fderiv (𝕜 := ℝ)).fun_comp (fun L => L (coordinateVector 3 b))
  have hdd (b : Fin 3) := (hpart b).fderiv_eq (𝕜 := ℝ)
  simp only [hd, hdd]

#print axioms warped_radial_strict_in_ambient_chart
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
