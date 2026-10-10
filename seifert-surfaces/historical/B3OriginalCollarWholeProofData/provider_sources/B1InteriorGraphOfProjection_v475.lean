import B1ZeroGermDerivativeClosure_v475
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
noncomputable section
open Set Topology Function Filter
open scoped ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A literal rank-two sheet parametrization becomes a smooth scalar graph
over the same base projection once its normal derivative vanishes. -/
theorem native_interior_graph_of_projection_v475
    (O : Set E2) (hO : IsOpen O) (P : E2 → E2 × ℝ)
    (hP : ContDiffOn ℝ ∞ P O) (x : E2) (hx : x ∈ O)
    (hinj : Function.Injective (fderiv ℝ P x))
    (hnormal : fderiv ℝ (fun y => (P y).2) x=0) :
    ∃ e : OpenPartialHomeomorph E2 E2, ∃ u : E2 → ℝ,
      x ∈ e.source ∧ e.source ⊆ O ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ u e.target ∧
      (∀ z ∈ e.target, P (e.symm z)=(z,u z)) ∧
      (∀ y ∈ e.source, P y=(e y,u (e y))) ∧
      P '' e.source=(fun z => (z,u z)) '' e.target := by
  have hPd : DifferentiableAt ℝ P x :=
    (hP.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hn : (ContinuousLinearMap.snd ℝ E2 ℝ).comp (fderiv ℝ P x)=0 := by
    rw [← hPd.hasFDerivAt.snd.fderiv]
    exact hnormal
  have hbInv := native_projected_derivative_invertible_v475 (fderiv ℝ P x) hinj hn
  let B : E2 → E2 := fun y => (P y).1
  have hB : ContDiffOn ℝ ∞ B O := hP.fst
  have hBd : HasFDerivAt B ((ContinuousLinearMap.fst ℝ E2 ℝ).comp (fderiv ℝ P x)) x := hPd.hasFDerivAt.fst
  obtain ⟨L,hL⟩ := hbInv
  obtain ⟨e,heX,heO,heS,heI,heEq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv hB hO hx
      (hL.symm ▸ hBd)
  let u : E2 → ℝ := fun z => (P (e.symm z)).2
  have hu : ContDiffOn ℝ ∞ u e.target :=
    (hP.comp heI (fun z hz => heO (e.map_target hz))).snd
  have hgraph (z : E2) (hz : z ∈ e.target) : P (e.symm z)=(z,u z) := by
    apply Prod.ext
    · change (P (e.symm z)).1 = z
      calc
        (P (e.symm z)).1 = B (e.symm z) := rfl
        _ = e (e.symm z) := (heEq (e.symm z)).symm
        _ = z := e.right_inv hz
    · rfl
  refine ⟨e,u,heX,heO,heS,heI,hu,hgraph,?_,?_⟩
  · intro y hy
    have hh := hgraph (e y) (e.map_source hy)
    change P y=(e y,u (e y))
    rw [← hh,e.left_inv hy]
  · ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨e y,e.map_source hy,?_⟩
      change (e y,u (e y))=P y
      rw [← hgraph (e y) (e.map_source hy),e.left_inv hy]
    · rintro ⟨y,hy,rfl⟩
      exact ⟨e.symm y,e.map_target hy,hgraph y hy⟩

#print axioms native_interior_graph_of_projection_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
