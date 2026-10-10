import Section5SurfaceLocalInverseOnV489
import Section5SurfaceProjectionRankV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates
noncomputable section
universe u
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]

/-- Full-rank projection of a neat surface to the actual cylinder is a local
smooth coordinate system at its boundary. -/
theorem cylinder_projection_local_inverse {f : S → Circle × Time} {U : Set S}
    (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) ∞ f U)
    (hboundary : ∀ y ∈ U, y ∈ (𝓡∂ 2).boundary S → (f y).2 = 0)
    {x : S} (hxU : x ∈ U) (hx : x ∈ (𝓡∂ 2).boundary S)
    (hinj : Injective (mfderiv (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) f x)) :
    IsLocalDiffeomorphAt (𝓡∂ 2) ((𝓡 1).prod (𝓡∂ 1)) ∞ f x := by
  obtain ⟨d,hdz,hdr⟩ := cylinder_boundary_halfspace_chart (f x).1
  have hdx : f x ∈ d.source := by
    have h := hboundary x hxU hx
    have he : f x = ((f x).1,0) := Prod.ext rfl h
    rwa [he]
  let V := U ∩ f ⁻¹' d.source
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU d.open_source
  have hxV : x ∈ V := ⟨hxU,hdx⟩
  have hdf : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (d ∘ f) V :=
    d.contMDiffOn.comp (hf.mono inter_subset_left) (fun _ hy => hy.2)
  have hb : ∀ y ∈ V, y ∈ (𝓡∂ 2).boundary S → d (f y) ∈ (𝓡∂ 2).boundary (EuclideanHalfSpace 2) := by
    intro y hy hby
    have hz := hdr (f y) hy.2
    rw [hboundary y hy.1 hby,Set.Icc.coe_zero] at hz
    change (𝓡∂ 2).IsBoundaryPoint (d (f y))
    rw [ModelWithCorners.isBoundaryPoint_iff,extChartAt_self_eq,
      frontier_range_modelWithCornersEuclideanHalfSpace]
    exact hz.symm
  have hdD := d.isLocalDiffeomorphAt ((𝓡 1).prod (𝓡∂ 1)) (𝓡∂ 2) ∞ hdx
  have hdi : Injective (mfderiv ((𝓡 1).prod (𝓡∂ 1)) (𝓡∂ 2) d (f x)) := by
    simpa only [IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv] using!
      (hdD.mfderivToContinuousLinearEquiv (by simp)).injective
  have hdfi : Injective (mfderiv (𝓡∂ 2) (𝓡∂ 2) (d ∘ f) x) := by
    rw [mfderiv_comp x (hdD.mdifferentiableAt (by simp))
      (((hf x hxU).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp))]
    exact hdi.comp hinj
  obtain ⟨p,hpx,heqp⟩ := surface_boundary_local_inverse_on hV hdf hb hxV hx hdfi
  let R := p.toOpenPartialHomeomorph.restrOpen V hV
  let q : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) S (EuclideanHalfSpace 2) ∞ := {
    toPartialEquiv := R.toPartialEquiv
    open_source := R.open_source
    open_target := R.open_target
    contMDiffOn_toFun := p.contMDiffOn.mono inter_subset_left
    contMDiffOn_invFun := p.symm.contMDiffOn.mono inter_subset_left }
  refine ⟨q.trans d.symm,?_,?_⟩
  · refine ⟨⟨hpx,hxV⟩,?_⟩
    change p x ∈ d.target
    rw [← heqp hpx]
    exact d.map_source hdx
  · intro y hy
    change (y ∈ p.source ∧ y ∈ V) ∧ p y ∈ d.target at hy
    have he := heqp hy.1.1
    change d (f y) = p y at he
    change f y = d.symm (p y)
    have hfy : f y ∈ d.source := hy.1.2.2
    rw [← he]
    exact (d.left_inv hfy).symm

#print axioms cylinder_projection_local_inverse
end
end SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
