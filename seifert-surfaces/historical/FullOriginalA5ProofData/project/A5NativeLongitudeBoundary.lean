import A5MinimizerConsequences
import A5NativeAmbientLift

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- Every actual longitude is a smooth regular curve in the two-sided sphere,
including at the boundary of the exterior. -/
theorem longitude_leaf_sphere_smooth_regular
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (J : LongitudeFoliation.{u} E) (a : Circle) :
    ContMDiff (𝓡 1) (𝓡 3) ∞ (fun z => E.toSphere (J.torus (a,z))) ∧
    ∀ z, Function.Injective
      (mfderiv (𝓡 1) (𝓡 3) (fun z => E.toSphere (J.torus (a,z))) z) := by
  let k : Circle → Circle × Circle := fun z => (a,z)
  have hk : ContMDiff (𝓡 1) ((𝓡 1).prod (𝓡 1)) ∞ k :=
    contMDiff_const.prodMk contMDiff_id
  have hinc : Manifold.IsImmersion (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := by
    let : ChartedSpace (EuclideanHalfSpace 3) T.Carrier := E.charted
    let : IsManifold (𝓡∂ 3) ∞ T.Carrier := E.smooth
    exact E.inclusion.isImmersion
  have htorus := J.smoothEmbedding.contMDiff.comp hk
  refine ⟨hinc.contMDiff.comp htorus, ?_⟩
  intro z
  have hkd := hk.mdifferentiable (by simp) z
  have hkinj : Function.Injective (mfderiv (𝓡 1) ((𝓡 1).prod (𝓡 1)) k z) := by
    have hcomp := mfderiv_comp z
      (mdifferentiableAt_snd (I := 𝓡 1) (I' := 𝓡 1)) hkd
    have he : Prod.snd ∘ k = id := rfl
    rw [he, mfderiv_id] at hcomp
    intro v w hvw
    have hv := congrArg (fun L => L v) hcomp
    have hw := congrArg (fun L => L w) hcomp
    exact hv.trans ((congrArg _ hvw).trans hw.symm)
  change Function.Injective (mfderiv (𝓡 1) (𝓡 3) (E.toSphere ∘ J.torus ∘ k) z)
  rw [mfderiv_comp z (hinc.contMDiff.mdifferentiable (by simp) _)
    (htorus.mdifferentiable (by simp) z),
    mfderiv_comp z (J.smoothEmbedding.contMDiff.mdifferentiable (by simp) _) hkd]
  exact (hinc.mfderiv_injective (by simp) _).comp
    ((J.smoothEmbedding.isImmersion.mfderiv_injective (by simp) _).comp hkinj)

/-- The original leaf-labelled boundary has its actual continuous circle
parametrization in the rough native source. Ambient regularity is inherited
from the literal longitude, without assuming the rough source map smooth. -/
theorem native_longitude_boundary_circle
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (J : LongitudeFoliation.{u} E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) (hF : J.BoundaryIn F.map) :
    ∃ (a : Circle) (b : C(Circle,S)),
      IsEmbedding b ∧ range b = S.boundary ∧
      (∀ z, F.map (b z) = J.torus (a,z)) ∧
      ContMDiff (𝓡 1) (𝓡 3) ∞ (E.toSphere ∘ F.map ∘ b) ∧
      ∀ z, Function.Injective (mfderiv (𝓡 1) (𝓡 3) (E.toSphere ∘ F.map ∘ b) z) := by
  obtain ⟨a,ha⟩ := hF
  let e := F.embedding.toHomeomorph
  have hm (z : Circle) : J.torus (a,z) ∈ range F.map := by
    have h : J.torus (a,z) ∈ F.map '' S.boundary := by
      rw [ha]; exact mem_range_self z
    exact image_subset_range _ _ h
  let q : Circle → range F.map := fun z => ⟨J.torus (a,z),hm z⟩
  have hq : Continuous q :=
    (J.smoothEmbedding.isEmbedding.continuous.comp
      (continuous_const.prodMk continuous_id)).subtype_mk hm
  let b : C(Circle,S) := ⟨e.symm ∘ q,e.symm.continuous.comp hq⟩
  have heq (z : Circle) : F.map (b z) = J.torus (a,z) := by
    have hh := congrArg Subtype.val (e.apply_symm_apply (q z))
    exact hh
  have hbi : IsEmbedding b := by
    apply F.embedding.of_comp_iff.mp
    have hb : F.map ∘ b = fun z => J.torus (a,z) := funext heq
    rw [hb]
    exact J.smoothEmbedding.isEmbedding.comp (isEmbedding_prodMkRight a)
  have hbr : range b = S.boundary := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      rw [← F.boundary_preimage]
      change F.map (b z) ∈ (𝓡∂ 3).boundary E.Carrier
      rw [heq]
      exact J.torus_lands_boundary _
    · intro hx
      have hm : F.map x ∈ J.leaf a := by rw [← ha]; exact mem_image_of_mem _ hx
      obtain ⟨z,hz⟩ := hm
      exact ⟨z,F.embedding.injective ((heq z).trans hz)⟩
  have hs : E.toSphere ∘ F.map ∘ b = fun z => E.toSphere (J.torus (a,z)) :=
    funext fun z => congrArg E.toSphere (heq z)
  refine ⟨a,b,hbi,hbr,heq,?_,?_⟩
  · rw [hs]; exact (longitude_leaf_sphere_smooth_regular E J a).1
  · rw [hs]; exact (longitude_leaf_sphere_smooth_regular E J a).2

/-- The actual minimizer has the same smooth regular labelled boundary circle
as the initial original competitor. -/
theorem original_minimizer_native_boundary_circle
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (J : LongitudeFoliation.{u} E) {S R : CompactOrientedSurface.{u}}
    {g : SmoothMetric E.Carrier}
    (F : GeometricPiecewiseSurface S E.Carrier) (hF : J.BoundaryIn F.map)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E g F Fprime) :
    ∃ (a : Circle) (b : C(Circle,R)),
      IsEmbedding b ∧ range b = R.boundary ∧
      (∀ z, Fprime.map (b z) = J.torus (a,z)) ∧
      ContMDiff (𝓡 1) (𝓡 3) ∞ (E.toSphere ∘ Fprime.map ∘ b) ∧
      ∀ z, Function.Injective (mfderiv (𝓡 1) (𝓡 3) (E.toSphere ∘ Fprime.map ∘ b) z) := by
  apply native_longitude_boundary_circle E J Fprime
  obtain ⟨a,ha⟩ := hF
  exact ⟨a,hminimum.in_class.boundary_image_eq.trans ha⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
