import Section5OpenFlowExtensionV488
set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
noncomputable section
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

def conjugateFlow (e : M ≃ₜ N) (Φ : Flow ℝ M) : Flow ℝ N where
  toFun t x := e (Φ t (e.symm x))
  cont' := e.continuous.comp (Φ.continuous continuous_fst (e.symm.continuous.comp continuous_snd))
  map_add' t u x := by simp only [Homeomorph.symm_apply_apply,Flow.map_add]
  map_zero' x := by simp only [Flow.map_zero_apply,Homeomorph.apply_symm_apply]

theorem conjugate_flow_coordinates (e : M ≃ₜ N) (Φ : Flow ℝ M) (t : ℝ) (x : M) :
    conjugateFlow e Φ t (e x) = e (Φ t x) := by
  change e (Φ t (e.symm (e x))) = _
  rw [Homeomorph.symm_apply_apply]

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
variable {I : ModelWithCorners ℝ V H} {I' : ModelWithCorners ℝ W G}
variable [ChartedSpace H M] [ChartedSpace G N]

theorem conjugate_flow_smooth (e : Diffeomorph I I' M N ∞) (Φ : Flow ℝ M)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2)) :
    ContMDiff (𝓘(ℝ).prod I') I' ∞ (fun p : ℝ × N => conjugateFlow e.toHomeomorph Φ p.1 p.2) :=
  e.contMDiff.comp (hΦ.comp (contMDiff_fst.prodMk (e.symm.contMDiff.comp contMDiff_snd)))

#print axioms conjugate_flow_smooth
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
