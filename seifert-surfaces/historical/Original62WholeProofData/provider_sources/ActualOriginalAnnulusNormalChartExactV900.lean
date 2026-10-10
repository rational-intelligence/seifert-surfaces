import ActualOriginalAnnulusHalfChartsV858
import ActualAnnularStripAmbientExtensionV851

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped Manifold ContDiff
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
noncomputable section
namespace CompressionActualOriginalAnnulusNormalChartExactV900

/-- Compose the actual original-annulus surface chart with the supplied
    genuine normal neighborhood. Whole-D and boundary avoidance on the zero
    slice are inherited from the actual original-annulus chart proof. -/
theorem original_annulus_normal_chart_exact
    {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} {D : InteriorCompressingDisk f}
    (s : OpenPartialHomeomorph Plane S)
    (hs : s.source = {x : Plane | 1 < ‖x‖ ∧ ‖x‖ < 3})
    (haway : ∀ x,x ∈ s.source →
      f.toFun (s x) ∉ range D.toFun ∧ f.toFun (s x) ∉ (𝓡∂ 3).boundary M)
    (β : OpenPartialHomeomorph (ℝ × S) M)
    (hβs : ∀ x,x ∈ s.target → (0,x) ∈ β.source)
    (hβ0 : ∀ x,x ∈ s.target → β (0,x) = f.toFun x) :
    ∃ e : OpenPartialHomeomorph (Plane × ℝ) M,
      (∀ x : Plane,1 < ‖x‖ → ‖x‖ < 3 → (x,0) ∈ e.source) ∧
      (∀ x : Plane,1 < ‖x‖ → ‖x‖ < 3 → e (x,0) = f.toFun (s x)) ∧
      (∀ y,y ∈ e.target → y ∈ β.target ∧ (β.symm y).2 ∈ s.target) ∧
      (∀ x n,e (x,n) = β (n,s x)) ∧
      ∀ x : Plane,1 < ‖x‖ → ‖x‖ < 3 →
        e (x,0) ∉ range D.toFun ∧ e (x,0) ∉ (𝓡∂ 3).boundary M := by
  let P : OpenPartialHomeomorph (Plane × ℝ) (ℝ × S) :=
    (Homeomorph.prodComm Plane ℝ).toOpenPartialHomeomorph.trans
      ((OpenPartialHomeomorph.refl ℝ).prod s)
  let e : OpenPartialHomeomorph (Plane × ℝ) M := P.trans β
  have hxS (x : Plane) (hlo : 1 < ‖x‖) (hhi : ‖x‖ < 3) : x ∈ s.source := hs.symm ▸ ⟨hlo,hhi⟩
  have hPs (x : Plane) (hlo : 1 < ‖x‖) (hhi : ‖x‖ < 3) : (x,0) ∈ P.source :=
    ⟨mem_univ _,mem_univ _,hxS x hlo hhi⟩
  have hPv (x : Plane) : P (x,0) = (0,s x) := rfl
  have hes (x : Plane) (hlo : 1 < ‖x‖) (hhi : ‖x‖ < 3) : (x,0) ∈ e.source :=
    ⟨hPs x hlo hhi,hβs _ (s.map_source (hxS x hlo hhi))⟩
  have hev (x : Plane) (hlo : 1 < ‖x‖) (hhi : ‖x‖ < 3) : e (x,0) = f.toFun (s x) :=
    hβ0 _ (s.map_source (hxS x hlo hhi))
  have het (y : M) (hy : y ∈ e.target) :
      y ∈ β.target ∧ (β.symm y).2 ∈ s.target := by
    change y ∈ (P.trans β).target at hy
    rw [OpenPartialHomeomorph.trans_target] at hy
    refine ⟨hy.1,?_⟩
    have hp : β.symm y ∈ P.target := hy.2
    change β.symm y ∈ ((Homeomorph.prodComm Plane ℝ).toOpenPartialHomeomorph.trans
      ((OpenPartialHomeomorph.refl ℝ).prod s)).target at hp
    rw [OpenPartialHomeomorph.trans_target] at hp
    exact hp.1.2
  refine ⟨e,hes,hev,het,fun _ _ => rfl,?_⟩
  intro x hlo hhi
  rw [hev x hlo hhi]
  exact haway x (hxS x hlo hhi)

#print axioms original_annulus_normal_chart_exact
end CompressionActualOriginalAnnulusNormalChartExactV900
