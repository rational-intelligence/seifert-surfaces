import A5NearbyTrackV472
import A5NearbySourceMapsV472
import A5NearbySurfaceTransportV472
import A5NativeStabilityConsumer

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

theorem reconstructed_smooth_family_all_original_competitors
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {S R : CompactOrientedSurface.{u}} {g : SmoothMetric E.Carrier}
    {F : GeometricPiecewiseSurface S E.Carrier}
    {Fprime : GeometricPiecewiseSurface R E.Carrier}
    (hminimum : FixedBoundaryMinimizer E g F Fprime)
    (Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime)
    (H : ℝ → ProperSmoothEmbedding Q.source E.Carrier)
    (hzero : (H 0).toFun = Q.embedding.toFun)
    (hsmooth : ContMDiff (𝓘(ℝ).prod (𝓡∂ 2)) (𝓡∂ 3) ∞
      (fun p : ℝ × Q.source => (H p.1).toFun p.2))
    (hboundary : ∀ t x, x ∈ Q.source.boundary →
      (H t).toFun x = Q.embedding.toFun x)
    (t : ℝ) :
    ∃ C : GeometricPiecewiseSurface Q.source E.Carrier,
      C.map = (H t).continuousMap ∧ FixedBoundaryImageIsotopic E F C := by
  classical
  obtain ⟨d, stage, hcont, ⟨old⟩, hinitial, hterminal, hfixed⟩ := hminimum.in_class
  choose C hC using fun a : ℝ => smooth_as_piecewise (H a)
  have hCmap (a : ℝ) : (C a).map = (H a).continuousMap := (hC a).1
  let e : S ≃ₜ Q.source := d.homeomorph.trans Q.homeomorph.symm
  have heb : e '' S.boundary = Q.source.boundary :=
    (endpoint_source_homeomorph E F Fprime Q d (H t) (C t) (hCmap t)).boundary_image
  let oldMap : Time × S → E.Carrier := fun p => (stage p.1).map p.2
  let J : Time × Q.source → E.Carrier := fun p => (H (t * (p.1 : ℝ))).toFun p.2
  have hJ : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 2)) (𝓡∂ 3) ∞ J :=
    hsmooth.comp ((contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_fst)).prodMk
      contMDiff_snd)
  have hJr (s : Time) (x : Q.source) :
      Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) (fun x => J (s,x)) x) :=
    (H (t * (s : ℝ))).differential_injective x
  let newMap : Time × S → E.Carrier := fun p => J (p.1,e p.2)
  have hjoin (x : S) : oldMap (1,x) = newMap (0,x) := by
    change (stage 1).map x = (H (t * (0 : ℝ))).toFun (e x)
    rw [hterminal, mul_zero, hzero, Q.pointwise_same_map]
    simp [e]
  have hnewcont : Continuous newMap :=
    hJ.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd))
  let newStage : Time → GeometricPiecewiseSurface S E.Carrier := fun s =>
    if (s : ℝ) ≤ 1 / 2 then stage (leftClock s)
    else SurfaceTransport.pullback_geometric_surface (C (t * (rightClock s : ℝ))) e heb
  have hstage : (fun p : Time × S => (newStage p.1).map p.2) = splice oldMap newMap := by
    funext p
    dsimp [newStage, splice]
    split_ifs
    · rfl
    · simp only [SurfaceTransport.pullback_geometric_surface, hCmap, ContinuousMap.comp_apply]
      rfl
  have hq (i : Fin d.forward.count) :
      ContMDiff CornerModel (𝓡∂ 2) 1 (e ∘ d.forward.parametrization i) ∧
      (∀ x, Function.Injective (mfderiv CornerModel (𝓡∂ 2) (e ∘ d.forward.parametrization i) x)) ∧
      ContMDiffOn CornerModel (𝓡∂ 2) ∞ (e ∘ d.forward.parametrization i)
        (CornerModel.interior (d.forward.domain i)) :=
    geometric_corner_lift_to_smooth_source E F Fprime Q d.homeomorph d.homeomorph.continuous
      d.forward i
  refine ⟨C t, hCmap t,
    endpoint_source_homeomorph E F Fprime Q d (H t) (C t) (hCmap t), newStage, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstage]
    exact splice_continuous oldMap newMap hcont hnewcont hjoin
  · rw [hstage]
    exact geometric_splice_track F Fprime d.forward oldMap old e hq J hJ hJr hjoin
  · have hz : leftClock 0 = 0 := by apply Subtype.ext; norm_num [leftClock, Set.projIcc]
    simpa [newStage, hz] using hinitial
  · have ho : rightClock 1 = 1 := by apply Subtype.ext; norm_num [rightClock, Set.projIcc]
    ext x
    dsimp only [newStage]
    rw [if_neg (by norm_num : ¬ ((1 : Time) : ℝ) ≤ 1 / 2), ho]
    change (C (t * (1 : ℝ))).map (e x) = (C t).map (e x)
    rw [mul_one]
  · intro s x hx
    have hbx : e x ∈ Q.source.boundary := by rw [← heb]; exact ⟨x,hx,rfl⟩
    have hQ : Q.embedding.toFun (e x) = F.map x := by
      have he := hfixed 1 x hx
      rw [hterminal] at he
      simpa [Q.pointwise_same_map, e] using he
    dsimp [newStage]
    split_ifs
    · exact hfixed _ x hx
    · change (C (t * (rightClock s : ℝ))).map (e x) = F.map x
      rw [hCmap]
      exact (hboundary _ _ hbx).trans hQ

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
