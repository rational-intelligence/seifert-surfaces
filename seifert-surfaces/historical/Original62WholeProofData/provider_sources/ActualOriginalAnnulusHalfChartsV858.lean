import ActualOriginalAnnulusWidenedHalvesV854
import ActualWideAnnulusSurfaceChartV856

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped Manifold ContDiff
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualPlanarPolarCoordinatesV761
noncomputable section
namespace CompressionActualOriginalAnnulusHalfChartsV858

/-- Construct actual open half-annulus surface charts across the literal
    original attachment edges. Every chart point avoids the full supplied
    disk and the ambient boundary. -/
theorem original_annulus_half_charts
    {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} {D : InteriorCompressingDisk f}
    (A : CompressionAnnulus D) :
    ∃ e : Fin 2 → OpenPartialHomeomorph Plane S,
      (∀ k,(e k).source = {x : Plane | 1 < ‖x‖ ∧ ‖x‖ < 3}) ∧
      (∀ k z,e k ((2:ℝ) • circleVector z) = A.band (z,CompressionAnnulus.sideTime k)) ∧
      (∀ k, (e k).target ⊆ S.boundaryᶜ) ∧
      ∀ k x,x ∈ (e k).source →
        f.toFun (e k x) ∉ range D.toFun ∧ f.toFun (e k x) ∉ (𝓡∂ 3).boundary M := by
  classical
  obtain ⟨w,hw,hcore,hedge,-,-,hbd⟩ :=
    CompressionActualOriginalAnnulusWidenedHalvesV854.original_annulus_widened_halves A
  choose e hes het hel using fun k : Fin 2 =>
    CompressionActualWideAnnulusSurfaceChartV856.wide_annulus_surface_chart S (w k) (hw k)
  have heedge (k : Fin 2) (z : Circle) : e k ((2:ℝ) • circleVector z) =
      A.band (z,CompressionAnnulus.sideTime k) := by
    have h := hel k z middleTime (by norm_num [middleTime]) (by norm_num [middleTime])
    have hr : 1+2*middleTime.val = (2:ℝ) := by norm_num [middleTime]
    rw [hr,hedge] at h
    exact h
  have htarget (k : Fin 2) : (e k).target ⊆ S.boundaryᶜ := by
    rw [het k]
    exact (image_subset_range _ _).trans (hbd k)
  refine ⟨e,hes,heedge,htarget,?_⟩
  intro k x hx
  have hxt : e k x ∈ (e k).target := (e k).map_source hx
  have hxS : e k x ∉ S.boundary := htarget k hxt
  refine ⟨?_,?_⟩
  · intro hd
    have hi : f.toFun (e k x) ∈ range D.toFun ∩ f.image := ⟨hd,mem_range_self _⟩
    have hb : f.toFun (e k x) ∈ D.toFun '' D.disk.boundary := D.intersection ▸ hi
    obtain ⟨p,hp,hpe⟩ := hb
    have hpr : p ∈ range D.boundaryCircle.toFun := D.boundary_covers.symm ▸ hp
    obtain ⟨z,hz⟩ := hpr
    have hfz : f.toFun (e k x) = f.toFun (D.surfaceLoop z) := by
      rw [← D.boundary_matches z,hz,hpe]
    have hs : e k x = D.surfaceLoop z := f.smoothEmbedding.isEmbedding.injective hfz
    have hxtw : e k x ∈ w k '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1} := het k ▸ hxt
    obtain ⟨q,hq,hqe⟩ := hxtw
    have hwe : w k q = w k (z,0) := hqe.trans (hs.trans (hcore k z).symm)
    have hqz := (hw k).injective hwe
    have ht := congrArg (fun p : Circle × Time => p.2.val) hqz
    change q.2.val = 0 at ht
    exact (ne_of_gt hq.1) ht
  · intro hb
    have hs : e k x ∈ S.boundary := by
      rw [← f.boundary_preimage]
      exact hb
    exact hxS hs

#print axioms original_annulus_half_charts
end CompressionActualOriginalAnnulusHalfChartsV858
