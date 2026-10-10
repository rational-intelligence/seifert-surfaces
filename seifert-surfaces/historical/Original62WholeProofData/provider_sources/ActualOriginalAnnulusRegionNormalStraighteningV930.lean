import ActualVariableAnnularAmbientRegionsV929
import ActualOriginalAnnulusNormalChartSourceV906
import ActualOriginalAnnulusDisjointHalfChartsV880
import ActualAnnulusWholeGlobalFamilyV897
import ActualDisjointSupportedAmbientCompositionV881
import ActualAnnulusOpenRegionCoordinatesV931

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
namespace CompressionActualOriginalAnnulusRegionNormalStraighteningV930

/-- One SAME whole annulus family supplies the full product labels and
    simultaneous supported normal straightening of both variable cap collars.
    Normal chart data are actual supplied paid coordinates; surface charts,
    planar families, normal widths and disjoint ambient supports are derived. -/
theorem original_annulus_region_normal_straightening
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
    (hNF : ∀ p,p ∈ N.source → (N p ∈ F.image ↔ p.1 = 0))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (Z : Set E.Carrier) (hZ : IsClosed Z) (hZF : Disjoint Z F.image) :
    ∃ H : C(Time × (Circle × Time),Circle × Time),
      (∀ s,IsEmbedding (fun p => H (s,p))) ∧
      (∀ p,H (0,p) = β p) ∧ (∀ p,H (1,p) = p) ∧
      (∀ s z,H (s,(z,middleTime)) = (z,middleTime)) ∧
      ∃ ρ : ℝ,0 < ρ ∧ ∀ φ : ℝ → Time,Continuous φ → φ 0 = 1 →
        (∀ m,m ∉ Ioo (-ρ) ρ → φ m = 0) →
        ∃ I : TopologicalAmbientIsotopy E.Carrier,∃ V : Set E.Carrier,
          IsOpen V ∧ IsCompact (closure V) ∧ Disjoint (closure V) (range D.toFun) ∧
          Disjoint (closure V) ((𝓡∂ 3).boundary E.Carrier) ∧ Disjoint (closure V) Z ∧
          (∀ k z,F.embedding.toFun (A.band (z,CompressionAnnulus.sideTime k)) ∈ V) ∧
          (∀ t x,x ∉ V → I.stage t x = x) ∧
          (∀ t x,x ∈ (𝓡∂ 3).boundary E.Carrier → I.stage t x = x) ∧
          (∀ t m x,(m,x) ∈ N.source → φ m = 0 → I.stage t (N (m,x)) = N (m,x)) ∧
          (∀ t x,I.stage t x ∈ F.image ↔ x ∈ F.image) ∧ (∀ t,I.stage t '' F.image = F.image) ∧
          (I.stage 1 '' (F.embedding.toFun '' A.removed) =
            F.embedding.toFun '' (A.band '' (β '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1}))) ∧
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
  choose e hes hezero het heformula heSource heaway using fun k : Fin 2 =>
    CompressionActualOriginalAnnulusNormalChartSourceV906.original_annulus_normal_chart_source
      (s k) (hss k) (hsaway k) N (fun x hx => hNs x (hsW k hx)) (fun x hx => hN0 x (hsW k hx))
  have hedis : Disjoint (e 0).target (e 1).target := by
    apply disjoint_left.mpr
    intro y hy0 hy1
    exact disjoint_left.mp hsdis (het 0 y hy0).2 (het 1 y hy1).2
  have hDc : IsClosed (range D.toFun) := (isCompact_range D.smoothEmbedding.isEmbedding.continuous).isClosed
  let Z' : Set E.Carrier := range D.toFun ∪ Z
  have hZ' : IsClosed Z' := hDc.union hZ
  have haway' (k : Fin 2) (x : Plane) (hlo : 1 < ‖x‖) (hhi : ‖x‖ < 3) :
      e k (x,0) ∉ Z' ∧ e k (x,0) ∉ (𝓡∂ 3).boundary E.Carrier := by
    refine ⟨?_,(heaway k x hlo hhi).2⟩
    rintro (hd | hz)
    · exact (heaway k x hlo hhi).1 hd
    · rw [hezero k x hlo hhi] at hz
      exact disjoint_left.mp hZF hz (mem_range_self _)
  have heF (k : Fin 2) (p : Plane × ℝ) (hp : p ∈ (e k).source) :
      e k p ∈ F.image ↔ p.2 = 0 := by
    rw [heformula k p.1 p.2]
    exact hNF _ ((heSource k p.1 p.2).mp hp).2
  choose r hr hsource hIs using fun k : Fin 2 =>
    CompressionActualVariableAnnularAmbientRegionsV929.variable_annular_ambient_regions
      (G k) (hG k) (hGi k) (hG1 k) (hGfix k) (hGbound k)
      ε hε hε1 (e k) (hes k) Z' hZ' (haway' k) F.image (heF k)
  let ρ : ℝ := min (r 0) (r 1)
  have hρ : 0 < ρ := lt_min (hr 0) (hr 1)
  have hρr (k : Fin 2) : ρ ≤ r k := by fin_cases k; exact min_le_left _ _; exact min_le_right _ _
  have heLabel (k : Fin 2) (u : Time) (z : Circle) (t : Time) (ht : 0 < t.val) (m : ℝ) :
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
  choose I V hV hVc hVZ hVbd hVT hseam hoff hbd hphase hIS hIimage hregions hzero hpoint using fun k => hIs k φ hφ hφ0 (hφoffr k)
  have hVD (k : Fin 2) : Disjoint (closure (V k)) (range D.toFun) :=
    (hVZ k).mono_right subset_union_left
  have hIZ (k : Fin 2) : Disjoint (closure (V k)) Z := (hVZ k).mono_right subset_union_right
  have hIphase (k : Fin 2) (t : Time) (m : ℝ) (x : F.surface) (hpN : (m,x) ∈ N.source)
      (hpφ : φ m = 0) : (I k).stage t (N (m,x)) = N (m,x) := by
    by_cases hy : N (m,x) ∈ (e k).target
    · let p : Plane × ℝ := (e k).symm (N (m,x))
      have hp : p ∈ (e k).source := (e k).map_target hy
      have hpn : (p.2,s k p.1) ∈ N.source := (heSource k p.1 p.2).mp hp |>.2
      have heq : e k p = N (m,x) := (e k).right_inv hy
      have hn : (p.2,s k p.1) = (m,x) := N.injOn hpn hpN ((heformula k p.1 p.2).symm.trans heq)
      have hnm : p.2 = m := congrArg Prod.fst hn
      rw [← heq]
      exact hphase k t p hp (hnm ▸ hpφ)
    · exact hoff k t _ (fun hv => hy (hVT k hv))
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
  have hZavoid : Disjoint (closure (V 0 ∪ V 1)) Z := by
    rw [closure_union]
    exact (hIZ 0).sup_left (hIZ 1)
  have hJphase (t : Time) (m : ℝ) (x : F.surface) (hpN : (m,x) ∈ N.source) (hpφ : φ m = 0) :
      J.stage t (N (m,x)) = N (m,x) := by
    by_cases hy : N (m,x) ∈ V 1
    · rw [hJ1 t _ (fun hv => disjoint_left.mp hdis hv hy)]
      exact hIphase 1 t m x hpN hpφ
    · rw [hJ0 t _ hy]
      exact hIphase 0 t m x hpN hpφ
  have hJS (t : Time) (x : E.Carrier) : J.stage t x ∈ F.image ↔ x ∈ F.image := by
    by_cases hx : x ∈ V 1
    · rw [hJ1 t _ (fun hv => disjoint_left.mp hdis hv hx)]
      exact hIS 1 t x
    · rw [hJ0 t _ hx]
      exact hIS 0 t x
  have hJimage (t : Time) : J.stage t '' F.image = F.image := by
    apply Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact (hJS t x).mpr hx
    · intro y hy
      exact ⟨(J.stage t).symm y,(hJS t _).mp (by rwa [(J.stage t).apply_symm_apply]),(J.stage t).apply_symm_apply _⟩
  let O : Set (Circle × Time) := {p | 0 < p.2.val ∧ p.2.val < 1}
  let Ann : Set Plane := {x | 1 < ‖x‖ ∧ ‖x‖ < 2}
  have hAnn : polar '' O = Ann := CompressionActualAnnulusOpenRegionCoordinatesV931.polar_open_region
  have hOriginalPoint (k : Fin 2) (p : Circle × Time) (hp : 0 < p.2.val) :
      e k (polar p,0) = F.embedding.toFun (A.band (half k p)) := by
    rw [heformula]
    have hsEq : s k (polar p) = A.band (half k p) := hspoint k p.1 p.2 hp
    rw [hsEq,hN0 _ (hAW (mem_range_self _))]
  have hTargetPoint (k : Fin 2) (p : Circle × Time) (hp : 0 < p.2.val) :
      e k (G k 0 (polar p),0) = F.embedding.toFun (A.band (β (half k p))) := by
    rw [heLabel k 0 p.1 p.2 hp 0,hH0,hN0 _ (hAW (mem_range_self _))]
  have hOriginalImage (k : Fin 2) : e k '' (Ann ×ˢ {0}) =
      (fun p => F.embedding.toFun (A.band (half k p))) '' O := by
    apply Subset.antisymm
    · rintro y ⟨⟨x,n⟩,⟨hx,hn⟩,rfl⟩
      rw [← hAnn] at hx
      obtain ⟨p,hp,rfl⟩ := hx
      have hn0 : n = 0 := mem_singleton_iff.mp hn
      exact ⟨p,hp,(hOriginalPoint k p hp.1).symm.trans (by rw [hn0])⟩
    · rintro y ⟨p,hp,rfl⟩
      exact ⟨(polar p,0),⟨hAnn ▸ ⟨p,hp,rfl⟩,mem_singleton _⟩,hOriginalPoint k p hp.1⟩
  have hTargetImage (k : Fin 2) : e k '' ((G k 0 '' Ann) ×ˢ {0}) =
      (fun p => F.embedding.toFun (A.band (β (half k p)))) '' O := by
    apply Subset.antisymm
    · rintro y ⟨⟨x,n⟩,⟨⟨q,hq,rfl⟩,hn⟩,rfl⟩
      rw [← hAnn] at hq
      obtain ⟨p,hp,rfl⟩ := hq
      have hn0 : n = 0 := mem_singleton_iff.mp hn
      exact ⟨p,hp,(hTargetPoint k p hp.1).symm.trans (by rw [hn0])⟩
    · rintro y ⟨p,hp,rfl⟩
      exact ⟨(G k 0 (polar p),0),⟨⟨polar p,hAnn ▸ ⟨p,hp,rfl⟩,rfl⟩,mem_singleton _⟩,hTargetPoint k p hp.1⟩
  have hJhalf (k : Fin 2) :
      J.stage 1 '' ((fun p => F.embedding.toFun (A.band (half k p))) '' O) =
        (fun p => F.embedding.toFun (A.band (β (half k p)))) '' O := by
    have hEq : J.stage 1 '' ((fun p => F.embedding.toFun (A.band (half k p))) '' O) =
        (I k).stage 1 '' ((fun p => F.embedding.toFun (A.band (half k p))) '' O) := by
      apply image_congr
      rintro y ⟨p,hp,rfl⟩
      have hps : (polar p,0) ∈ (e k).source := hes k (polar p)
        (by rw [polar_norm]; linarith [hp.1])
        (by rw [polar_norm]; linarith [hp.2])
      have hpt : F.embedding.toFun (A.band (half k p)) ∈ (e k).target :=
        hOriginalPoint k p hp.1 ▸ (e k).map_source hps
      fin_cases k
      · exact hJ0 1 _ (fun hy => disjoint_left.mp hedis hpt (hVT 1 hy))
      · exact hJ1 1 _ (fun hy => disjoint_left.mp hedis (hVT 0 hy) hpt)
    rw [hEq,← hOriginalImage,hregions k,hTargetImage]
  have hJcore (z : Circle) : J.stage 1 (F.embedding.toFun (A.band (z,middleTime))) =
      F.embedding.toFun (A.band (z,middleTime)) := by
    apply hJo
    intro hy
    apply disjoint_left.mp hD (subset_closure hy)
    rw [A.center,← D.boundary_matches]
    exact mem_range_self _
  have hremoved : J.stage 1 '' (F.embedding.toFun '' A.removed) =
      F.embedding.toFun '' (A.band '' (β '' O)) := by
    apply Subset.antisymm
    · rintro y ⟨x,⟨a,⟨p,hp,rfl⟩,rfl⟩,rfl⟩
      have hp' : p ∈ range (fun z : Circle => (z,middleTime)) ∪ ⋃ k : Fin 2,half k '' O :=
        CompressionActualAnnulusOpenRegionCoordinatesV931.open_middle_decomposition ▸ hp
      rcases hp' with ⟨z,rfl⟩ | hp'
      · rw [hJcore]
        refine ⟨A.band (z,middleTime),⟨(z,middleTime),⟨(z,middleTime),?_,hcore z⟩,rfl⟩,rfl⟩
        change 0 < (1/2:ℝ) ∧ (1/2:ℝ) < 1
        norm_num
      · obtain ⟨k,q,hq,rfl⟩ := mem_iUnion.mp hp'
        have hy : J.stage 1 (F.embedding.toFun (A.band (half k q))) ∈
            (fun p => F.embedding.toFun (A.band (β (half k p)))) '' O :=
          hJhalf k ▸ ⟨F.embedding.toFun (A.band (half k q)),⟨q,hq,rfl⟩,rfl⟩
        obtain ⟨v,hv,heq⟩ := hy
        exact ⟨A.band (β (half k v)),⟨β (half k v),⟨half k v,
          CompressionActualAnnulusOpenRegionCoordinatesV931.half_open_region k v hv,rfl⟩,rfl⟩,heq⟩
    · rintro y ⟨a,⟨q,⟨p,hp,rfl⟩,rfl⟩,rfl⟩
      have hp' : p ∈ range (fun z : Circle => (z,middleTime)) ∪ ⋃ k : Fin 2,half k '' O :=
        CompressionActualAnnulusOpenRegionCoordinatesV931.open_middle_decomposition ▸ hp
      rcases hp' with ⟨z,rfl⟩ | hp'
      · rw [hcore]
        refine ⟨F.embedding.toFun (A.band (z,middleTime)),⟨A.band (z,middleTime),⟨(z,middleTime),?_,rfl⟩,rfl⟩,hJcore z⟩
        change 0 < (1/2:ℝ) ∧ (1/2:ℝ) < 1
        norm_num
      · obtain ⟨k,q,hq,rfl⟩ := mem_iUnion.mp hp'
        have hy : F.embedding.toFun (A.band (β (half k q))) ∈
            J.stage 1 '' ((fun p => F.embedding.toFun (A.band (half k p))) '' O) :=
          (hJhalf k).symm ▸ ⟨q,hq,rfl⟩
        obtain ⟨x,⟨v,hv,rfl⟩,heq⟩ := hy
        exact ⟨F.embedding.toFun (A.band (half k v)),⟨A.band (half k v),⟨half k v,
          CompressionActualAnnulusOpenRegionCoordinatesV931.half_open_region k v hv,rfl⟩,rfl⟩,heq⟩
  have hcap (k : Fin 2) (z : Circle) (t : Time) (ht : ε ≤ t.val) (m : ℝ) (hm : m ∈ Icc (-ρ) ρ) :
      J.stage 1 (N (m,A.band (H (φ m,half k (z,t))))) = N (m,A.band (β (half k (z,t)))) := by
    have hm' : m ∈ Icc (-(r k)) (r k) := ⟨(neg_le_neg (hρr k)).trans hm.1,hm.2.trans (hρr k)⟩
    have hp : e k (G k (φ m) (polar (z,t)),m) ∈ (e k).target :=
      (e k).map_source (hsource k (φ m) z t ht m hm')
    rw [← heLabel k (φ m) z t (hε.trans_le ht) m,← hH0,← heLabel k 0 z t (hε.trans_le ht) m]
    fin_cases k
    · rw [hJ0 _ _ (fun hy => disjoint_left.mp hedis hp (hVT 1 hy))]
      exact hpoint 0 z t ht m hm'
    · rw [hJ1 _ _ (fun hy => disjoint_left.mp hedis (hVT 0 hy) hp)]
      exact hpoint 1 z t ht m hm'
  refine ⟨J,V 0 ∪ V 1,hVo,hVco,hD,hB,hZavoid,?_,hJo,hJbd,hJphase,hJS,hJimage,hremoved,?_,hcap⟩
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

#print axioms original_annulus_region_normal_straightening
end CompressionActualOriginalAnnulusRegionNormalStraighteningV930
