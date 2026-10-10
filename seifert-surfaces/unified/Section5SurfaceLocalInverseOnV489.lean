import Section5CylinderHalfspaceChartV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
noncomputable section
universe u v
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]
  {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (𝓡∂ 2) ∞ M]

theorem surface_open_inclusion (U : TopologicalSpace.Opens S) (hne : Nonempty U) :
    ∃ e : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) U S ∞,
      (∀ x, e x = x.val) ∧ e.source = univ ∧ e.target = (U:Set S) := by
  let e := U.openPartialHomeomorphSubtypeCoe hne
  have hi : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ e.symm e.target := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target x).mp
    have heq : EqOn (Subtype.val ∘ e.symm) id e.target := fun y hy => e.right_inv hy
    exact (contMDiffOn_id.congr (fun y hy => heq hy)) x hx
  exact ⟨{ toPartialEquiv := e.toPartialEquiv
           open_source := e.open_source
           open_target := e.open_target
           contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
           contMDiffOn_invFun := hi },fun _ => rfl,rfl,
    U.openPartialHomeomorphSubtypeCoe_target hne⟩

/-- The boundary inverse theorem uses only the actual open neighborhood of the
point, so coordinate projections need no artificial global smooth extension. -/
theorem surface_boundary_local_inverse_on {f : S → M} {U : Set S}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ f U)
    (hboundary : ∀ y ∈ U, y ∈ (𝓡∂ 2).boundary S → f y ∈ (𝓡∂ 2).boundary M)
    {x : S} (hxU : x ∈ U) (hx : x ∈ (𝓡∂ 2).boundary S)
    (hinj : Injective (mfderiv (𝓡∂ 2) (𝓡∂ 2) f x)) :
    IsLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ f x := by
  let V : TopologicalSpace.Opens S := ⟨U,hU⟩
  let xx : V := ⟨x,hxU⟩
  obtain ⟨inc,hinc,hincs,hinct⟩ := surface_open_inclusion V ⟨xx⟩
  have hfV : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (f ∘ Subtype.val : V → M) :=
    hf.comp_contMDiff contMDiff_subtype_val (fun y => y.property)
  have hbV : ∀ y : V, y ∈ (𝓡∂ 2).boundary V → f y.val ∈ (𝓡∂ 2).boundary M := by
    intro y hy
    exact hboundary y.val y.property ((𝓡∂ 2).isBoundaryPoint_iff_isBoundaryPoint_val.mp hy)
  have hxx : xx ∈ (𝓡∂ 2).boundary V :=
    (𝓡∂ 2).isBoundaryPoint_iff_isBoundaryPoint_val.mpr hx
  have hix : Injective (mfderiv (𝓡∂ 2) (𝓡∂ 2) (Subtype.val : V → S) xx) := by
    let hh := (inc.isLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ (hincs ▸ mem_univ xx)).mfderivToContinuousLinearEquiv (by simp)
    have hi : Injective (mfderiv (𝓡∂ 2) (𝓡∂ 2) inc xx) := by
      simpa only [hh,IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv] using! hh.injective
    have heq : (inc : V → S) = Subtype.val := funext hinc
    rwa [heq] at hi
  have hinjV : Injective (mfderiv (𝓡∂ 2) (𝓡∂ 2) (f ∘ Subtype.val : V → M) xx) := by
    have hdf : MDifferentiableAt (𝓡∂ 2) (𝓡∂ 2) f x :=
      ((hf x hxU).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
    have hdi : MDifferentiableAt (𝓡∂ 2) (𝓡∂ 2) (Subtype.val : V → S) xx :=
      contMDiff_subtype_val.mdifferentiableAt (n:=∞) (by simp)
    rw [mfderiv_comp xx hdf hdi]
    exact hinj.comp hix
  obtain ⟨p,hp,heqp⟩ := surface_boundary_local_inverse hfV hbV hxx hinjV
  refine ⟨inc.symm.trans p,?_,?_⟩
  · have hi : x ∈ inc.target := hinct ▸ hxU
    refine ⟨hi,?_⟩
    have he : inc.symm x = xx := by
      apply (inc.toPartialEquiv.injOn (inc.symm.map_source hi) (hincs ▸ mem_univ xx))
      exact (inc.right_inv hi).trans (hinc xx).symm
    change inc.symm x ∈ p.source
    rwa [he]
  · intro y hy
    change y ∈ inc.target ∧ inc.symm y ∈ p.source at hy
    change f y = p (inc.symm y)
    exact (congrArg f ((hinc (inc.symm y)).symm.trans (inc.right_inv hy.1))).symm.trans
      (heqp hy.2)

#print axioms surface_open_inclusion
#print axioms surface_boundary_local_inverse_on
end
end SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
