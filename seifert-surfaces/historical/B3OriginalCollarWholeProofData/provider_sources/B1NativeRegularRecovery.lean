import OriginalB1

open Set Topology Function
open scoped Manifold ContDiff

namespace SeifertSurfaces.MetricFoundations.B1Bridges
open SeifertSurfaces.Foundations
universe u v
noncomputable section
set_option autoImplicit false

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

theorem proper_smooth_embedding_interior_parameter_smooth
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S M)
    (q : Euc 2 → S) (y : Euc 2)
    (hq : ContinuousAt q y) (hinterior : q y ∉ S.boundary)
    (hcomp : ContMDiffAt 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞ (f.toFun ∘ q) y) :
    ContMDiffAt 𝓘(ℝ, Euc 2) (𝓡∂ 2) ∞ q y := by
  classical
  have local_EuclideanRecoveryProbe (F : Euc 2 → Euc 3) (Q : Euc 2 → Euc 2) (a y : Euc 2)
      (hF : ContDiffAt ℝ ∞ F a) (hFa : Function.Injective (fderiv ℝ F a))
      (hQ : ContinuousAt Q y) (ha : Q y = a) (hcomp : ContDiffAt ℝ ∞ (F ∘ Q) y) :
      ContDiffAt ℝ ∞ Q y := by
    classical
    obtain ⟨L,hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hFa
    let G : Euc 2 → Euc 2 := L ∘ F
    have hG : ContDiffAt ℝ ∞ G a := L.contDiff.contDiffAt.comp a hF
    have hderiv : HasFDerivAt G (ContinuousLinearEquiv.refl ℝ (Euc 2) : Euc 2 →L[ℝ] Euc 2) a := by
      have hc := L.hasFDerivAt.comp a (hF.differentiableAt (by simp)).hasFDerivAt
      have heq : L.comp (fderiv ℝ F a) = ContinuousLinearMap.id ℝ (Euc 2) := by
        apply ContinuousLinearMap.ext
        intro v
        exact hL v
      rw [heq] at hc
      exact hc
    let inv := hG.localInverse hderiv (by simp)
    have hinv : ContDiffAt ℝ ∞ inv (G a) := hG.to_localInverse hderiv (by simp)
    have hinverse : ∀ᶠ z in 𝓝 a, inv (G z) = z :=
      (hG.hasStrictFDerivAt' hderiv (by simp)).eventually_left_inverse
    have hGQ : ContDiffAt ℝ ∞ (G ∘ Q) y := L.contDiff.contDiffAt.comp y hcomp
    have hInvQ : ContDiffAt ℝ ∞ (inv ∘ (G ∘ Q)) y := by
      apply ContDiffAt.comp y ?_ hGQ
      change ContDiffAt ℝ ∞ inv (G (Q y))
      rw [ha]
      exact hinv
    apply hInvQ.congr_of_eventuallyEq
    have hi := hQ.tendsto.eventually (ha.symm ▸ hinverse)
    filter_upwards [hi] with z hz
    exact hz.symm
  have local_NativeGeometryProbe {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S M)
      (q : Euc 2 → S) (y : Euc 2) (hq : ContinuousAt q y)
      (hinterior : q y ∉ S.boundary)
      (hcomp : ContMDiffAt 𝓘(ℝ,Euc 2) (𝓡∂ 3) ∞ (f.toFun ∘ q) y) :
      let p := q y
      let F := writtenInExtChartAt (𝓡∂ 2) (𝓡∂ 3) p f.toFun
      let Q := extChartAt (𝓡∂ 2) p ∘ q
      let a := extChartAt (𝓡∂ 2) p p
      ContDiffAt ℝ ∞ F a ∧ Function.Injective (fderiv ℝ F a) ∧
        ContinuousAt Q y ∧ Q y = a ∧ ContDiffAt ℝ ∞ (F ∘ Q) y := by
    let p := q y
    let e := extChartAt (𝓡∂ 2) p
    let F := writtenInExtChartAt (𝓡∂ 2) (𝓡∂ 3) p f.toFun
    let Q := e ∘ q
    let a := e p
    have hi : (𝓡∂ 2).IsInteriorPoint p :=
      ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint p).2 hinterior
    have hra : range (𝓡∂ 2) ∈ 𝓝 a :=
      mem_interior_iff_mem_nhds.1
        (interior_mono (extChartAt_target_subset_range (I := 𝓡∂ 2) p)
          ((𝓡∂ 2).isInteriorPoint_iff.1 hi))
    have hFs : ContDiffAt ℝ ∞ F a :=
      ((contMDiffAt_iff.1 (f.smooth.contMDiffAt (x := p))).2).contDiffAt hra
    let D : Euc 2 →L[ℝ] Euc 3 :=
      (tangentSpaceCastModel (𝓡∂ 3) (f.toFun p)).toContinuousLinearMap.comp
        ((mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun p).comp
          (tangentSpaceCastModel (𝓡∂ 2) p).symm.toContinuousLinearMap)
    have hD : HasFDerivAt F D a :=
      ((f.smooth.contMDiffAt (x := p)).mdifferentiableAt (by simp)).hasMFDerivAt.2.hasFDerivAt hra
    have hDi : Function.Injective D :=
      ((tangentSpaceCastModel (𝓡∂ 3) (f.toFun p)).injective.comp
        (f.differential_injective p)).comp
        (tangentSpaceCastModel (𝓡∂ 2) p).symm.injective
    have hFi : Function.Injective (fderiv ℝ F a) := by
      have heq : fderiv ℝ F a = D := hD.fderiv
      exact heq ▸ hDi
    have hQ : ContinuousAt Q y := (continuousAt_extChartAt (I := 𝓡∂ 2) p).comp hq
    have hchart : ContDiffAt ℝ ∞
        (extChartAt (𝓡∂ 3) (f.toFun p) ∘ (f.toFun ∘ q)) y :=
      ((contMDiffAt_extChartAt (I := 𝓡∂ 3) (x := f.toFun p) (n := ∞)).comp y hcomp).contDiffAt
    have hEq : (F ∘ Q) =ᶠ[𝓝 y]
        (extChartAt (𝓡∂ 3) (f.toFun p) ∘ (f.toFun ∘ q)) := by
      filter_upwards [hq.tendsto.eventually (extChartAt_source_mem_nhds (I := 𝓡∂ 2) p)] with z hz
      change extChartAt (𝓡∂ 3) (f.toFun p) (f.toFun (e.symm (e (q z)))) = _
      rw [e.left_inv hz]
      rfl
    exact ⟨hFs,hFi,hQ,rfl,hchart.congr_of_eventuallyEq hEq⟩
  obtain ⟨hF,hFi,hQ,ha,hFQ⟩ := local_NativeGeometryProbe f q y hq hinterior hcomp
  have hQs := local_EuclideanRecoveryProbe
    (writtenInExtChartAt (𝓡∂ 2) (𝓡∂ 3) (q y) f.toFun)
    (extChartAt (𝓡∂ 2) (q y) ∘ q) (extChartAt (𝓡∂ 2) (q y) (q y)) y
    hF hFi hQ ha hFQ
  exact (contMDiffAt_iff_target_of_mem_source
    (I := 𝓘(ℝ,Euc 2)) (I' := 𝓡∂ 2) (n := ∞)
    (mem_chart_source (EuclideanHalfSpace 2) (q y))).2
    ⟨hq,hQs.contMDiffAt⟩

end
end SeifertSurfaces.MetricFoundations.B1Bridges
