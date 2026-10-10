import ActualVariableAnnularAmbientSourceV901
import ActualOriginalAnnulusNormalChartExactV900
import ActualOriginalAnnulusDisjointHalfChartsV880
import ActualAnnulusWholeGlobalFamilyV897
import ActualDisjointSupportedAmbientCompositionV881

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped Manifold ContDiff
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualAnnulusHalfCoordinatesV772
open CompressionActualAnnulusHalfPolarModelV768
noncomputable section
namespace CompressionActualOriginalAnnulusCoherentNormalStraighteningV902

/-- One SAME whole annulus family supplies the full product labels and
    simultaneous supported normal straightening of both variable cap collars.
    Normal chart data are actual supplied paid coordinates; surface charts,
    planar families, normal widths and disjoint ambient supports are derived. -/
theorem original_annulus_coherent_normal_straightening
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D)
    (β : C(Circle × Time,Circle × Time)) (hβ : IsEmbedding β)
    (hcore : ∀ z,β (z,middleTime) = (z,middleTime))
    (hside : ∀ k p,side k (β (half k p)))
    (W : Set F.surface) (hW : IsOpen W) (hAW : range A.band ⊆ W)
    (N : OpenPartialHomeomorph (ℝ × F.surface) E.Carrier)
    (hNs : ∀ x,x ∈ W → (0,x) ∈ N.source)
    (hN0 : ∀ x,x ∈ W → N (0,x) = F.embedding.toFun x)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ H : C(Time × (Circle × Time),Circle × Time),
      (∀ s,IsEmbedding (fun p => H (s,p))) ∧
      (∀ p,H (0,p) = β p) ∧ (∀ p,H (1,p) = p) ∧
      (∀ s z,H (s,(z,middleTime)) = (z,middleTime)) ∧
      ∃ ρ : ℝ,0 < ρ ∧ ∀ φ : ℝ → Time,Continuous φ → φ 0 = 1 →
        (∀ m,m ∉ Ioo (-ρ) ρ → φ m = 0) →
        ∃ I : TopologicalAmbientIsotopy E.Carrier,∃ V : Set E.Carrier,
          IsOpen V ∧ IsCompact (closure V) ∧ Disjoint (closure V) (range D.toFun) ∧
          Disjoint (closure V) ((𝓡∂ 3).boundary E.Carrier) ∧
          (∀ k z,F.embedding.toFun (A.band (z,CompressionAnnulus.sideTime k)) ∈ V) ∧
          (∀ t x,x ∉ V → I.stage t x = x) ∧
          (∀ t x,x ∈ (𝓡∂ 3).boundary E.Carrier → I.stage t x = x) ∧
          (∀ (k : Fin 2) (z : Circle) (t : Time),ε ≤ t.val →
            I.stage 1 (F.embedding.toFun (A.band (half k (z,t)))) =
              F.embedding.toFun (A.band (β (half k (z,t))))) ∧
          ∀ (k : Fin 2) (z : Circle) (t : Time),ε ≤ t.val →
            ∀ m,m ∈ Icc (-ρ) ρ →
              I.stage 1 (N (m,A.band (H (φ m,half k (z,t))))) =
                N (m,A.band (β (half k (z,t)))) := by
  classical
  obtain ⟨H,hH,hH0,hH1,hHcore,Γ,G,hG,hGi,hG1,hGfix,hGbound,hΓpolar,hHhalf⟩ :=
    CompressionActualAnnulusWholeGlobalFamilyV897.whole_annulus_relative_global_family β hβ hcore hside
  obtain ⟨s,hss,hse,hspoint,hsbd,hsW,hsdis,hsaway⟩ :=
    CompressionActualOriginalAnnulusDisjointHalfChartsV880.original_annulus_disjoint_half_charts A W hW hAW
  choose e hes hezero het heformula heaway using fun k : Fin 2 =>
    CompressionActualOriginalAnnulusNormalChartExactV900.original_annulus_normal_chart_exact
      (s k) (hss k) (hsaway k) N (fun x hx => hNs x (hsW k hx)) (fun x hx => hN0 x (hsW k hx))
  have hedis : Disjoint (e 0).target (e 1).target := by
    apply disjoint_left.mpr
    intro y hy0 hy1
    exact disjoint_left.mp hsdis (het 0 y hy0).2 (het 1 y hy1).2
  have hDc : IsClosed (range D.toFun) := (isCompact_range D.smoothEmbedding.isEmbedding.continuous).isClosed
  choose r hr hsource hIs using fun k : Fin 2 =>
    CompressionActualVariableAnnularAmbientSourceV901.variable_annular_ambient_source
      (G k) (hG k) (hGi k) (hG1 k) (hGfix k) (hGbound k)
      ε hε hε1 (e k) (hes k) (range D.toFun) hDc (heaway k)
  let ρ : ℝ := min (r 0) (r 1)
  have hρ : 0 < ρ := lt_min (hr 0) (hr 1)
  have hρr (k : Fin 2) : ρ ≤ r k := by fin_cases k; exact min_le_left _ _; exact min_le_right _ _
  have heLabel (k : Fin 2) (u : Time) (z : Circle) (t : Time) (ht : ε ≤ t.val) (m : ℝ) :
      e k (G k u (polar (z,t)),m) = N (m,A.band (H (u,half k (z,t)))) := by
    have htn : 1 < ‖polar (z,t)‖ := by rw [polar_norm]; linarith
    have hgn := CompressionActualBoundaryExactDiskSeparatedIsotopyV845.image_outside_fixed_disk
      (G k u) (hGfix k u) htn
    have hp : 0 < (Γ k (u,(z,t))).2.val := by
      rw [← hΓpolar,polar_norm] at hgn
      linarith
    rw [← hΓpolar,heformula]
    rw [show s k (polar (Γ k (u,(z,t)))) = A.band (half k (Γ k (u,(z,t)))) from
      hspoint k _ _ hp,← hHhalf]
  refine ⟨H,hH,hH0,hH1,hHcore,ρ,hρ,?_⟩
  intro φ hφ hφ0 hφoff
  have hφoffr (k : Fin 2) (m : ℝ) (hm : m ∉ Ioo (-(r k)) (r k)) : φ m = 0 :=
    hφoff m (fun hn => hm ⟨lt_of_le_of_lt (neg_le_neg (hρr k)) hn.1,hn.2.trans_le (hρr k)⟩)
  choose I V hV hVc hVD hVbd hVT hseam hoff hbd hzero hpoint using fun k => hIs k φ hφ hφ0 (hφoffr k)
  have hdis : Disjoint (V 0) (V 1) := hedis.mono (hVT 0) (hVT 1)
  obtain ⟨J,hVo,hVco,hJo,hJbd,hJ0,hJ1⟩ :=
    CompressionActualDisjointSupportedAmbientCompositionV881.disjoint_supported_isotopy_composition
      (I 0) (I 1) (V 0) (V 1) (hV 0) (hV 1) (hVc 0) (hVc 1) hdis
      (hoff 0) (hoff 1) (hbd 0) (hbd 1)
  have hD : Disjoint (closure (V 0 ∪ V 1)) (range D.toFun) := by
    rw [closure_union]
    exact (hVD 0).sup_left (hVD 1)
  have hB : Disjoint (closure (V 0 ∪ V 1)) ((𝓡∂ 3).boundary E.Carrier) := by
    rw [closure_union]
    exact (hVbd 0).sup_left (hVbd 1)
  have hcap (k : Fin 2) (z : Circle) (t : Time) (ht : ε ≤ t.val) (m : ℝ) (hm : m ∈ Icc (-ρ) ρ) :
      J.stage 1 (N (m,A.band (H (φ m,half k (z,t))))) = N (m,A.band (β (half k (z,t)))) := by
    have hm' : m ∈ Icc (-(r k)) (r k) := ⟨(neg_le_neg (hρr k)).trans hm.1,hm.2.trans (hρr k)⟩
    have hp : e k (G k (φ m) (polar (z,t)),m) ∈ (e k).target :=
      (e k).map_source (hsource k (φ m) z t ht m hm')
    rw [← heLabel k (φ m) z t ht m,← hH0,← heLabel k 0 z t ht m]
    fin_cases k
    · rw [hJ0 _ _ (fun hy => disjoint_left.mp hedis hp (hVT 1 hy))]
      exact hpoint 0 z t ht m hm'
    · rw [hJ1 _ _ (fun hy => disjoint_left.mp hedis (hVT 0 hy) hp)]
      exact hpoint 1 z t ht m hm'
  refine ⟨J,V 0 ∪ V 1,hVo,hVco,hD,hB,?_,hJo,hJbd,?_,hcap⟩
  · intro k z
    have heq : e k ((2:ℝ) • circleVector z,0) = F.embedding.toFun (A.band (z,CompressionAnnulus.sideTime k)) := by
      rw [heformula,hse,hN0 _ (hAW (mem_range_self _))]
    fin_cases k
    · exact Or.inl (heq ▸ hseam 0 z)
    · exact Or.inr (heq ▸ hseam 1 z)
  · intro k z t ht
    have hp := hcap k z t ht 0 ⟨by linarith,hρ.le⟩
    rw [hφ0,hH1,hN0 _ (hAW (mem_range_self _)),hN0 _ (hAW (mem_range_self _))] at hp
    exact hp

#print axioms original_annulus_coherent_normal_straightening
end CompressionActualOriginalAnnulusCoherentNormalStraighteningV902
