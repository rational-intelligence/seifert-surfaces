import B1ActualCollarChart_v475
import B1ActualAmbientFlowMinimum_v475
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem native_actual_chart_differential_invertible_v475
    (c : SmoothAmbientChart ThreeSphere) (p : ThreeSphere) (hp : p ∈ c.chart.source) :
    (mfderiv (𝓡 3) 𝓘(ℝ,E3) c.chart p).IsInvertible := by
  have hc : c.chart ∈ IsManifold.maximalAtlas (𝓡 3) 1 ThreeSphere :=
    c.chart.mem_maximalAtlas_of_contMDiffOn (c.smooth.of_le (by simp))
      (c.inverse_smooth.of_le (by simp))
  convert! isInvertible_mfderiv_extend hc hp using 1

/-- Pull back a smooth coordinate field and cut it off inside the actual
exterior. The cutoff is identically one on a neighborhood of the whole
compact region, rather than only at a selected point. -/
theorem native_chart_compact_cutoff_field_v475
    (c : SmoothAmbientChart ThreeSphere) (U A : Set ThreeSphere)
    (hU : IsOpen U) (hUc : U ⊆ c.chart.source)
    (hUE : U ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier)
    (hA : IsCompact A) (hAU : A ⊆ U)
    (W : E3 → E3) (hW : ContDiffOn ℝ ∞ W (c.chart '' U)) :
    ∃ (X : NativeInteriorSmoothVectorField_v475 E) (χ : ThreeSphere → ℝ),
      ContMDiff (𝓡 3) 𝓘(ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      (∀ q, 0 ≤ χ q ∧ χ q ≤ 1) ∧ χ =ᶠ[𝓝ˢ A] 1 ∧
      closure {q | X.field q ≠ 0} ⊆ U ∧
      (∀ q ∈ U, chartDifferential c q (X.field q) = χ q • W (c.chart q)) := by
  classical
  let V := c.chart '' U
  have hV : IsOpen V := c.chart.isOpen_image_of_subset_source hU hUc
  let Z : ∀ z : E3, TangentSpace 𝓘(ℝ,E3) z :=
    fun z => (NormedSpace.fromTangentSpace z).symm (W z)
  let Y := VectorField.mpullback (𝓡 3) 𝓘(ℝ,E3) c.chart Z
  have hZ : ContMDiffOn 𝓘(ℝ,E3) (𝓘(ℝ,E3)).tangent ∞
      (fun z => Bundle.TotalSpace.mk' E3 z (Z z)) V := by
    convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ,E3))).comp_contMDiffOn
      ((contDiffOn_id.prodMk hW).contMDiffOn) using 1
  have hY : ContMDiffOn (𝓡 3) (𝓡 3).tangent ∞
      (fun q => Bundle.TotalSpace.mk' E3 q (Y q)) U := by
    intro q hq
    have hqV : c.chart q ∈ V := mem_image_of_mem c.chart hq
    have hZZ := hZ.contMDiffAt (hV.mem_nhds hqV)
    have hcc := c.smooth.contMDiffAt (c.chart.open_source.mem_nhds (hUc hq))
    exact (hZZ.mpullback_vectorField_preimage hcc
      (native_actual_chart_differential_invertible_v475 c q (hUc hq))
      (by simp)).contMDiffWithinAt
  obtain ⟨χ,hχ,hχc,hχone,hχU,hχrange⟩ :=
    DifferentialGeometry.Analysis.exists_mfd_bump (I := 𝓡 3) hA hU hAU
  let Yχ := fun q => χ q • Y q
  have hYχ : ContMDiff (𝓡 3) (𝓡 3).tangent ∞
      (fun q => Bundle.TotalSpace.mk' E3 q (Yχ q)) :=
    hχ.contMDiffOn.smul_section_of_tsupport hU hχU hY
  have hsu : closure {q | Yχ q ≠ 0} ⊆ tsupport χ := by
    apply closure_mono
    intro q hq
    exact fun h => hq (by simp only [Yχ,h,zero_smul])
  let X : NativeInteriorSmoothVectorField_v475 E := {
    field := Yχ
    smooth := hYχ
    compact_support := hχc.of_isClosed_subset isClosed_closure hsu
    support_interior := hsu.trans (hχU.trans hUE) }
  refine ⟨X,χ,hχ,hχc,(fun q => hχrange (mem_range_self q)),hχone,hsu.trans hχU,?_⟩
  intro q hq
  change chartDifferential c q (χ q • Y q) = _
  rw [map_smul]
  congr 1
  unfold chartDifferential Y VectorField.mpullback
  rw [ContinuousLinearMap.comp_apply,
    (native_actual_chart_differential_invertible_v475 c q (hUc hq)).self_apply_inverse]
  exact (NormedSpace.fromTangentSpace (c.chart q)).apply_symm_apply _

#print axioms native_actual_chart_differential_invertible_v475
#print axioms native_chart_compact_cutoff_field_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
