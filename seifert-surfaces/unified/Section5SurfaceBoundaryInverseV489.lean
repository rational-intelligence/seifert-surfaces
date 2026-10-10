import A7HalfSpaceRestrictionV464
import Section5SurfaceBoundarySignV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter Manifold
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
open SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates
universe u v
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]
  {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (𝓡∂ 2) ∞ M]

/-- A full-rank map preserving the boundary has an actual smooth local inverse
at a boundary point of a surface. -/
theorem surface_boundary_local_inverse {f : S → M}
    (hf : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ f)
    (hboundary : ∀ y, y ∈ (𝓡∂ 2).boundary S → f y ∈ (𝓡∂ 2).boundary M)
    {x : S} (hx : x ∈ (𝓡∂ 2).boundary S)
    (hinj : Injective (mfderiv (𝓡∂ 2) (𝓡∂ 2) f x)) :
    IsLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ f x := by
  let L := surfaceCoordinateDifferential f x
  have hL : Injective L :=
    (tangentSpaceCastModel (𝓡∂ 2) (f x)).injective.comp
      (hinj.comp (tangentSpaceCastModel (𝓡∂ 2) x).symm.injective)
  let eL : E2 ≃ₗ[ℝ] E2 := L.toLinearMap.linearEquivOfInjective hL rfl
  let A : E2 ≃L[ℝ] E2 := {
    toLinearEquiv := eL
    continuous_toFun := L.continuous
    continuous_invFun := eL.symm.toLinearMap.continuous_of_finiteDimensional }
  have htrans : ∃ w : TangentSpace (𝓡∂ 2) x,
      inwardCoordinate (f x) (mfderiv (𝓡∂ 2) (𝓡∂ 2) f x w) ≠ 0 := by
    obtain ⟨w,hw⟩ := A.surjective (EuclideanSpace.single 0 1)
    refine ⟨w,?_⟩
    rw [inwardCoordinate_eq_coordinate]
    change L w 0 ≠ 0
    have h := congrArg (fun z : E2 => z 0) hw
    change L w 0 = _ at h
    have hone : (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0 = 1 := by simp [EuclideanSpace.single]
    rw [hone] at h
    exact h ▸ (one_ne_zero : (1 : ℝ) ≠ 0)
  obtain ⟨g,hg,hge,hd⟩ := surface_target_coordinate_extension hf x
  obtain ⟨c,hc,hrow⟩ := surface_boundary_coordinate_row hf x hx (hboundary x hx) htrans
  have hsign := surface_coordinate_extension_boundary_sign hf hboundary x hx hg hge hd hc hrow
  obtain ⟨e,hea,_,hes,hei,heq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv
      hg.contDiffOn isOpen_univ (mem_univ _) (by simpa only [A,eL] using hd : HasFDerivAt g A (extChartAt (𝓡∂ 2) x x))
  obtain ⟨W,hW,hWo,haW⟩ := mem_nhds_iff.mp hsign
  let gamma := e.restrOpen W hWo
  have hgamma : gamma.IsImage (range (𝓡∂ 2)) (range (𝓡∂ 2)) := by
    intro y hy
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ e y 0 ↔ 0 ≤ y 0
    rw [heq]
    exact hW hy.2
  let eta : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) (EuclideanHalfSpace 2) (EuclideanHalfSpace 2) ∞ := {
    toPartialEquiv := (halfSpaceRestriction gamma hgamma).toPartialEquiv
    open_source := (halfSpaceRestriction gamma hgamma).open_source
    open_target := (halfSpaceRestriction gamma hgamma).open_target
    contMDiffOn_toFun := halfSpaceRestriction_smooth gamma hgamma (hes.mono inter_subset_left)
    contMDiffOn_invFun := halfSpaceRestriction_inverse_smooth gamma hgamma (hei.mono inter_subset_left) }
  let cs : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) S (EuclideanHalfSpace 2) ∞ := {
    toPartialEquiv := (chartAt (EuclideanHalfSpace 2) x).toPartialEquiv
    open_source := (chartAt (EuclideanHalfSpace 2) x).open_source
    open_target := (chartAt (EuclideanHalfSpace 2) x).open_target
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }
  let ds : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) M (EuclideanHalfSpace 2) ∞ := {
    toPartialEquiv := (chartAt (EuclideanHalfSpace 2) (f x)).toPartialEquiv
    open_source := (chartAt (EuclideanHalfSpace 2) (f x)).open_source
    open_target := (chartAt (EuclideanHalfSpace 2) (f x)).open_target
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }
  let Phi := (cs.trans eta).trans ds.symm
  let ex := extChartAt (𝓡∂ 2) x
  have heT : Tendsto ex (𝓝 x) (𝓝[range (𝓡∂ 2)] (ex x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨(contMDiffAt_extChartAt (I := 𝓡∂ 2) (n := ∞) (x := x)).continuousAt.tendsto,
      Eventually.of_forall (fun y => mem_range_self _)⟩
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ Phi.source ∧ Phi y = f y := by
    have hsrc : ∀ᶠ y in 𝓝 x, ex y ∈ gamma.source :=
      (contMDiffAt_extChartAt (I := 𝓡∂ 2) (n := ∞) (x := x)).continuousAt.preimage_mem_nhds
        (gamma.open_source.mem_nhds ⟨hea,haW⟩)
    have hdf : ∀ᶠ y in 𝓝 x, f y ∈ ds.source :=
      hf.continuous.continuousAt.preimage_mem_nhds (ds.open_source.mem_nhds (mem_chart_source _ _))
    filter_upwards [cs.open_source.mem_nhds (mem_chart_source _ _),hsrc,hdf,heT.eventually hge]
      with y hy hys hdy hey
    have hecy : ex.symm (ex y) = y := ex.left_inv (by simpa only [ex,extChartAt_source] using hy)
    change g (ex y) = (extChartAt (𝓡∂ 2) (f x)) (f (ex.symm (ex y))) at hey
    rw [hecy] at hey
    have hEta : eta (cs y) = ds (f y) := by
      change (𝓡∂ 2).symm (e (ex y)) = ds (f y)
      rw [heq,hey]
      exact (𝓡∂ 2).left_inv _
    refine ⟨⟨⟨hy,hys⟩,?_⟩,?_⟩
    · change eta (cs y) ∈ ds.target
      rw [hEta]
      exact ds.toPartialEquiv.map_source hdy
    · change ds.symm (eta (cs y)) = f y
      rw [hEta]
      exact ds.toPartialEquiv.left_inv hdy
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hnear
  let R := Phi.toOpenPartialHomeomorph.restrOpen V hVo
  refine ⟨{ toPartialEquiv := R.toPartialEquiv
            open_source := R.open_source
            open_target := R.open_target
            contMDiffOn_toFun := Phi.contMDiffOn.mono inter_subset_left
            contMDiffOn_invFun := Phi.symm.contMDiffOn.mono inter_subset_left },
    ⟨(hV hxV).1,hxV⟩,?_⟩
  intro y hy
  exact (hV hy.2).2.symm

#print axioms surface_boundary_local_inverse
end SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
