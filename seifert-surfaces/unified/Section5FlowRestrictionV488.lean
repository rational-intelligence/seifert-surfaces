import Section5FlowConjugationV488
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem restrict_flow_smooth (Φ : Flow ℝ M) (U : TopologicalSpace.Opens M)
    (hU : IsInvariant Φ (U : Set M))
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2)) :
    ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × U => (show Flow ℝ U from Φ.restrict hU) p.1 p.2) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  change ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × U => Φ p.1 p.2.val)
  have hb : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × U => p.2.val) :=
    contMDiff_subtype_val.comp contMDiff_snd
  exact hΦ.comp (contMDiff_fst.prodMk hb)

#print axioms restrict_flow_smooth
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
