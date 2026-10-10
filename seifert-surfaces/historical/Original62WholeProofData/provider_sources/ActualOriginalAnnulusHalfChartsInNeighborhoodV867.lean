import ActualOriginalAnnulusWidenedHalvesInNeighborhoodV859
import ActualWideAnnulusSurfaceChartV856

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped Manifold ContDiff
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualPlanarPolarCoordinatesV761
open CompressionActualAnnulusHalfCoordinatesV772
noncomputable section
namespace CompressionActualOriginalAnnulusHalfChartsInNeighborhoodV867

/-- Construct actual open half-annulus surface charts across the literal
    original attachment edges. Every chart point avoids the full supplied
    disk and the ambient boundary. -/
theorem original_annulus_half_charts_in_neighborhood
    {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} {D : InteriorCompressingDisk f}
    (A : CompressionAnnulus D) (U : Set S) (hU : IsOpen U) (hAU : range A.band ⊆ U) :
    ∃ e : Fin 2 → OpenPartialHomeomorph Plane S,
      (∀ k,(e k).source = {x : Plane | 1 < ‖x‖ ∧ ‖x‖ < 3}) ∧
      (∀ k z,e k ((2:ℝ) • circleVector z) = A.band (z,CompressionAnnulus.sideTime k)) ∧
      (∀ k (z : Circle) (t : Time),0 < t.val →
        e k ((1+t.val) • circleVector z) = A.band (half k (z,t))) ∧
      (∀ k, (e k).target ⊆ S.boundaryᶜ) ∧ (∀ k,(e k).target ⊆ U) ∧
      ∀ k x,x ∈ (e k).source →
        f.toFun (e k x) ∉ range D.toFun ∧ f.toFun (e k x) ∉ (𝓡∂ 3).boundary M := by
  classical
  obtain ⟨w,hw,hcore,hedge,hhalf,-,hbd,hwU⟩ :=
    CompressionActualOriginalAnnulusWidenedHalvesInNeighborhoodV859.original_annulus_widened_halves_in_neighborhood A U hU hAU
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
  have htargetU (k : Fin 2) : (e k).target ⊆ U := by
    rw [het k]
    exact (image_subset_range _ _).trans (hwU k)
  have hehalf (k : Fin 2) (z : Circle) (t : Time) (ht : 0 < t.val) :
      e k ((1+t.val) • circleVector z) = A.band (half k (z,t)) := by
    let u : Time := ⟨t.val/2,div_nonneg t.property.1 (by norm_num),by linarith [t.property.2]⟩
    have hu : 0 < u.val := half_pos ht
    have hu1 : u.val < 1 := by dsimp [u]; linarith [t.property.2]
    have h := hel k z u hu hu1
    have hr : 1+2*u.val = 1+t.val := by dsimp [u]; ring
    rw [hr] at h
    exact h.trans (hhalf k z t)
  refine ⟨e,hes,heedge,hehalf,htarget,htargetU,?_⟩
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

#print axioms original_annulus_half_charts_in_neighborhood
end CompressionActualOriginalAnnulusHalfChartsInNeighborhoodV867
