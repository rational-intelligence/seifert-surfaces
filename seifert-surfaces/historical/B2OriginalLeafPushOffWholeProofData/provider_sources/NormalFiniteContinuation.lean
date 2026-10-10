import NormalFlowSegmentTracking
import Mathlib.Topology.UnitInterval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- Composition of smooth ambient isotopies retains their exact endpoint maps. -/
def composeAmbientIsotopy (H J : SmoothAmbientIsotopy M) : SmoothAmbientIsotopy M :=
  { stage := fun t => (H.stage t).trans (J.stage t)
    smooth_family := J.smooth_family.comp (contMDiff_fst.prodMk H.smooth_family)
    initial := by intro x; change J.stage 0 (H.stage 0 x) = x; rw [H.initial,J.initial]
    boundary_setwise := by
      intro t
      change (fun x => J.stage t (H.stage t x)) '' _ = _
      rw [← image_image,H.boundary_setwise,J.boundary_setwise] }

variable {S : CompactOrientedSurface.{u}} [T2Space M] {f g : NeatEmbedding S M}

/-- Uniform compact-support continuation is realized by finitely many actual
flow segments of the same field. Their endpoint composition transports the
original normal isotopy across the entire closed time interval. -/
theorem normal_integrate_compact_spatial_field
    (F : SmoothNormalIsotopy S M f g)
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (htrace : ∀ p, Y (normalTrace F p) = traceVelocity F p)
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    {K : Set M} (hK : IsCompact K) (hsupp : ∀ q, q.2 ∉ K → Y q = 0) :
    ∃ H : SmoothAmbientIsotopy M, ∀ x,
      H.stage 1 ((F.stage 0).toFun x) = (F.stage 1).toFun x := by
  obtain ⟨ε,hε,hshort⟩ := exists_uniform_short_spatial_flow Y hY hYb hK hsupp
  let d : ℝ := ε / 2
  have hd : 0 < d := half_pos hε
  have hdε : d < ε := half_lt_self hε
  let c : ℕ → Time := Set.Icc.addNSMul (by norm_num : (0 : ℝ) ≤ 1) d
  have hcmono : Monotone c := Set.Icc.monotone_addNSMul (by norm_num) hd.le
  have hc0 : c 0 = 0 := by
    apply Subtype.ext
    exact Set.Icc.addNSMul_zero (by norm_num)
  obtain ⟨N,hN⟩ := Set.Icc.addNSMul_eq_right (by norm_num : (0 : ℝ) ≤ 1) hd
  have hfinite (n : ℕ) : ∃ H : SmoothAmbientIsotopy M, ∀ x,
      H.stage 1 ((F.stage 0).toFun x) = (F.stage (c n)).toFun x := by
    induction n with
    | zero =>
      refine ⟨{
        stage := fun _ => Diffeomorph.refl (𝓡∂ 3) M ∞
        smooth_family := contMDiff_snd
        initial := fun _ => rfl
        boundary_setwise := fun _ => image_id _ },?_⟩
      intro x
      rw [hc0]
      rfl
    | succ n ih =>
      obtain ⟨H,hH⟩ := ih
      have hab : c n ≤ c (n+1) := hcmono (Nat.le_succ n)
      have hdist : dist ((c n : Time) : ℝ) ((c (n+1) : Time) : ℝ) < ε := by
        have hh := Set.Icc.abs_sub_addNSMul_le (by norm_num : (0 : ℝ) ≤ 1) hd.le n
          (t := c (n+1)) ⟨hab,le_rfl⟩
        rw [Real.dist_eq,abs_sub_comm]
        exact hh.trans_lt hdε
      obtain ⟨Φ,hΦ⟩ := hshort (c n) (c (n+1)) hab (c n).property (c (n+1)).property hdist
      obtain ⟨J,hJ⟩ := spatial_flow_segment_tracks_normal F Y hY hYb htrace hab hΦ
      refine ⟨composeAmbientIsotopy H J,?_⟩
      intro x
      change J.stage 1 (H.stage 1 ((F.stage 0).toFun x)) = (F.stage (c (n+1))).toFun x
      rw [hH,hJ]
  obtain ⟨H,hH⟩ := hfinite N
  refine ⟨H,?_⟩
  intro x
  have hcN : c N = 1 := by
    apply Subtype.ext
    exact hN N le_rfl
  simpa only [hcN] using hH x

variable [SecondCountableTopology M]

/-- The compact moving-family field and its finite-time integration are both
produced from the original normal isotopy, with no extra premises. -/
theorem normal_isotopy_ambient_endpoint (F : SmoothNormalIsotopy S M f g) :
    ∃ H : SmoothAmbientIsotopy M, ∀ x,
      H.stage 1 ((F.stage 0).toFun x) = (F.stage 1).toFun x := by
  obtain ⟨K,hK,Y,hY,htrace,hYb,hsupp⟩ := normal_exists_compact_spatial_velocity F
  exact normal_integrate_compact_spatial_field F Y hY htrace hYb hK hsupp

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
