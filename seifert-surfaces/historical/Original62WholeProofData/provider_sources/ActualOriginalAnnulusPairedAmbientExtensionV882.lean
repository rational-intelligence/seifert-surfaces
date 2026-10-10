import ActualOriginalAnnulusDisjointHalfChartsV880
import ActualOriginalAnnulusNormalChartTargetV879
import ActualDisjointSupportedAmbientCompositionV881
import ActualAnnulusHalfRestrictionV773

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped Manifold ContDiff
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualAnnulusHalfCoordinatesV772
open CompressionActualAnnulusHalfPolarModelV768
noncomputable section
namespace CompressionActualOriginalAnnulusPairedAmbientExtensionV882

/-- The whole prescribed annulus-half embedding extends through the actual
    original surface normal block. The support closure avoids the FULL
    original supplied disk, and every original attachment point is matched. -/
theorem original_annulus_paired_ambient_extension
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D)
    (β : C(Circle × Time,Circle × Time)) (hβ : IsEmbedding β)
    (hcore : ∀ z,β (z,middleTime) = (z,middleTime))
    (hside : ∀ k p,side k (β (half k p)))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ I : TopologicalAmbientIsotopy E.Carrier,∃ V : Set E.Carrier,
      IsOpen V ∧ IsCompact (closure V) ∧ Disjoint (closure V) (range D.toFun) ∧
      Disjoint (closure V) ((𝓡∂ 3).boundary E.Carrier) ∧
      (∀ k z,F.embedding.toFun (A.band (z,CompressionAnnulus.sideTime k)) ∈ V) ∧
      (∀ t x,x ∉ V → I.stage t x = x) ∧
      (∀ t x,x ∈ (𝓡∂ 3).boundary E.Carrier → I.stage t x = x) ∧
      ∀ (k : Fin 2) (z : Circle) (t : Time),ε ≤ t.val →
        I.stage 1 (F.embedding.toFun (A.band (half k (z,t)))) =
          F.embedding.toFun (A.band (β (half k (z,t)))) := by
  classical
  obtain ⟨δ,hδ,W,hW,hAW,hWbd,N,hNs,hN0,hNi⟩ :=
    CompressionArbitraryAnnulusNativeNormalCoordinates.given_arbitrary_annulus_native_surface_normal_coordinates E F D A
  obtain ⟨s,hss,hse,hspoint,hsbd,hsW,hsdis,hsaway⟩ :=
    CompressionActualOriginalAnnulusDisjointHalfChartsV880.original_annulus_disjoint_half_charts A W hW hAW
  have hNs0 (k : Fin 2) (x : F.surface) (hx : x ∈ (s k).target) : (0,x) ∈ N.source := by
    rw [hNs]
    exact ⟨⟨neg_lt_zero.mpr hδ,hδ⟩,hsW k hx⟩
  have hNzero (k : Fin 2) (x : F.surface) (hx : x ∈ (s k).target) : N (0,x) = F.embedding.toFun x :=
    hN0 x (hsW k hx)
  choose e hes hezero het heaway using fun k : Fin 2 =>
    CompressionActualOriginalAnnulusNormalChartTargetV879.original_annulus_normal_chart_target
      (s k) (hss k) (hsaway k) N.toOpenPartialHomeomorph (hNs0 k) (hNzero k)
  have hedis : Disjoint (e 0).target (e 1).target := by
    apply disjoint_left.mpr
    intro y hy0 hy1
    exact disjoint_left.mp hsdis (het 0 y hy0).2 (het 1 y hy1).2
  have halfExtension (k : Fin 2) :
      ∃ I : TopologicalAmbientIsotopy E.Carrier,∃ V : Set E.Carrier,
        IsOpen V ∧ IsCompact (closure V) ∧ Disjoint (closure V) (range D.toFun) ∧
        Disjoint (closure V) ((𝓡∂ 3).boundary E.Carrier) ∧ V ⊆ (e k).target ∧
        (∀ z,F.embedding.toFun (A.band (z,CompressionAnnulus.sideTime k)) ∈ V) ∧
        (∀ t x,x ∉ V → I.stage t x = x) ∧
        (∀ t x,x ∈ (𝓡∂ 3).boundary E.Carrier → I.stage t x = x) ∧
        ∀ (z : Circle) (t : Time),ε ≤ t.val →
          I.stage 1 (F.embedding.toFun (A.band (half k (z,t)))) =
            F.embedding.toFun (A.band (β (half k (z,t)))) := by
    obtain ⟨b,hhalf,hb,hb0,hbpos⟩ :=
      CompressionActualAnnulusHalfRestrictionV773.annulus_half_restriction β hβ hcore k (hside k)
    let q : C(Circle × Time,Plane) := ⟨polar ∘ b,polar_continuous.comp b.continuous⟩
    have hq : IsEmbedding q := polar_embedding.comp hb
    have hq0 (z : Circle) : q (z,0) = circleVector z := by
      change polar (b (z,0)) = circleVector z
      rw [hb0]
      simp [polar]
    have hqout (z : Circle) (t : Time) (ht : t ≠ 0) : 1 < ‖q (z,t)‖ := by
      change 1 < ‖polar (b (z,t))‖
      rw [polar_norm]
      linarith [hbpos z t ht]
    have hqbound (z : Circle) (t : Time) : ‖q (z,t)‖ ≤ 2 := by
      change ‖polar (b (z,t))‖ ≤ 2
      rw [polar_norm]
      linarith [(b (z,t)).2.property.2]
    have hDc : IsClosed (range D.toFun) := (isCompact_range D.smoothEmbedding.isEmbedding.continuous).isClosed
    obtain ⟨I,V,hV,hVc,hVD,hVbd,hVT,hseam,hoff,hbd,hpoint⟩ :=
      CompressionActualAnnularStripAmbientChartSupportV878.annular_strip_ambient_chart_support
        q hq hq0 hqout hqbound ε hε hε1 (e k) (hes k) (range D.toFun) hDc (heaway k)
    have heOriginal (z : Circle) (t : Time) (ht : 0 < t.val) :
        e k (polar (z,t),0) = F.embedding.toFun (A.band (half k (z,t))) := by
      have hn : ‖polar (z,t)‖ = 1+t.val := polar_norm _
      rw [hezero _ _ (by rw [hn]; linarith) (by rw [hn]; linarith [t.property.2])]
      exact congrArg F.embedding.toFun (hspoint k z t ht)
    refine ⟨I,V,hV,hVc,hVD,hVbd,hVT,?_,hoff,hbd,?_⟩
    · intro z
      have ht : half k (z,(1:Time)) = (z,CompressionAnnulus.sideTime k) := by
        refine Prod.ext (by rfl) ?_
        apply Subtype.ext
        fin_cases k <;> norm_num [half,halfTime,CompressionAnnulus.sideTime]
      rw [← ht,← heOriginal z 1 (by norm_num)]
      simpa only [polar,Set.Icc.coe_one,add_self_div_two,show (1:ℝ)+1 = 2 by norm_num] using hseam z
    · intro z t ht
      have htp : 0 < t.val := hε.trans_le ht
      have hbp : 0 < (b (z,t)).2.val := hbpos z t (by intro he; rw [he] at htp; norm_num at htp)
      rw [← heOriginal z t htp]
      have hp := hpoint z t ht
      change I.stage 1 (e k (polar (z,t),0)) = e k (polar (b (z,t)),0) at hp
      rw [heOriginal _ _ hbp,hhalf] at hp
      exact hp
  choose I V hV hVc hVD hVbd hVT hseam hoff hbd hpoint using halfExtension
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
  have hsource (k : Fin 2) (z : Circle) (t : Time) (ht : 0 < t.val) :
      F.embedding.toFun (A.band (half k (z,t))) ∈ (e k).target := by
    have hn : ‖polar (z,t)‖ = 1+t.val := polar_norm _
    have hp : (polar (z,t),0) ∈ (e k).source :=
      hes k _ (by rw [hn]; linarith) (by rw [hn]; linarith [t.property.2])
    have heq : e k (polar (z,t),0) = F.embedding.toFun (A.band (half k (z,t))) :=
      (hezero k _ (by rw [hn]; linarith) (by rw [hn]; linarith [t.property.2])).trans
        (congrArg F.embedding.toFun (hspoint k z t ht))
    exact heq ▸ (e k).map_source hp
  refine ⟨J,V 0 ∪ V 1,hVo,hVco,hD,hB,?_,hJo,hJbd,?_⟩
  · intro k z
    fin_cases k
    · exact Or.inl (hseam 0 z)
    · exact Or.inr (hseam 1 z)
  · intro k z t ht
    have hx := hsource k z t (hε.trans_le ht)
    fin_cases k
    · rw [hJ0 _ _ (fun hy => disjoint_left.mp hedis hx (hVT 1 hy))]
      exact hpoint 0 z t ht
    · rw [hJ1 _ _ (fun hy => disjoint_left.mp hedis (hVT 0 hy) hx)]
      exact hpoint 1 z t ht

#print axioms original_annulus_paired_ambient_extension
end CompressionActualOriginalAnnulusPairedAmbientExtensionV882
