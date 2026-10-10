import ActualOriginalAnnulusHalfChartsInNeighborhoodV867
import ActualOriginalAnnulusNormalChartV866
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
namespace CompressionActualOriginalAnnulusAmbientExtensionV868

/-- The whole prescribed annulus-half embedding extends through the actual
    original surface normal block. The support closure avoids the FULL
    original supplied disk, and every original attachment point is matched. -/
theorem original_annulus_ambient_half_extension
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D)
    (β : C(Circle × Time,Circle × Time)) (hβ : IsEmbedding β)
    (hcore : ∀ z,β (z,middleTime) = (z,middleTime))
    (k : Fin 2) (hside : ∀ p,side k (β (half k p)))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ I : TopologicalAmbientIsotopy E.Carrier,∃ V : Set E.Carrier,
      IsOpen V ∧ IsCompact (closure V) ∧ Disjoint (closure V) (range D.toFun) ∧
      Disjoint (closure V) ((𝓡∂ 3).boundary E.Carrier) ∧
      (∀ z,F.embedding.toFun (A.band (z,CompressionAnnulus.sideTime k)) ∈ V) ∧
      (∀ t x,x ∉ V → I.stage t x = x) ∧
      (∀ t x,x ∈ (𝓡∂ 3).boundary E.Carrier → I.stage t x = x) ∧
      ∀ (z : Circle) (t : Time),ε ≤ t.val →
        I.stage 1 (F.embedding.toFun (A.band (half k (z,t)))) =
          F.embedding.toFun (A.band (β (half k (z,t)))) := by
  classical
  obtain ⟨δ,hδ,W,hW,hAW,hWbd,N,hNs,hN0,hNi⟩ :=
    CompressionArbitraryAnnulusNativeNormalCoordinates.given_arbitrary_annulus_native_surface_normal_coordinates E F D A
  obtain ⟨s,hss,hse,hspoint,hsbd,hsW,hsaway⟩ :=
    CompressionActualOriginalAnnulusHalfChartsInNeighborhoodV867.original_annulus_half_charts_in_neighborhood A W hW hAW
  have hNs0 (x : F.surface) (hx : x ∈ (s k).target) : (0,x) ∈ N.source := by
    rw [hNs]
    exact ⟨⟨neg_lt_zero.mpr hδ,hδ⟩,hsW k hx⟩
  have hNzero (x : F.surface) (hx : x ∈ (s k).target) : N (0,x) = F.embedding.toFun x :=
    hN0 x (hsW k hx)
  obtain ⟨e,hes,hezero,heaway⟩ :=
    CompressionActualOriginalAnnulusNormalChartV866.original_annulus_normal_chart
      (s k) (hss k) (hsaway k) N.toOpenPartialHomeomorph hNs0 hNzero
  obtain ⟨b,hhalf,hb,hb0,hbpos⟩ :=
    CompressionActualAnnulusHalfRestrictionV773.annulus_half_restriction β hβ hcore k hside
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
  obtain ⟨I,V,hV,hVc,hVD,hVbd,hseam,hoff,hbd,hpoint⟩ :=
    CompressionActualAnnularStripAmbientExtensionV851.annular_strip_ambient_extension
      q hq hq0 hqout hqbound ε hε hε1 e hes (range D.toFun) hDc heaway
  -- The surface chart was widened, but its original half retains its labels.
  -- The pointwise chart identities are kept below as explicit derived facts.
  have heOriginal (z : Circle) (t : Time) (ht : 0 < t.val) :
      e (polar (z,t),0) = F.embedding.toFun (A.band (half k (z,t))) := by
    have hn : ‖polar (z,t)‖ = 1+t.val := polar_norm _
    rw [hezero _ (by rw [hn]; linarith) (by rw [hn]; linarith [t.property.2])]
    exact congrArg F.embedding.toFun (hspoint k z t ht)
  refine ⟨I,V,hV,hVc,hVD,hVbd,?_,hoff,hbd,?_⟩
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
    change I.stage 1 (e (polar (z,t),0)) = e (polar (b (z,t)),0) at hp
    rw [heOriginal _ _ hbp,hhalf] at hp
    exact hp

end CompressionActualOriginalAnnulusAmbientExtensionV868
