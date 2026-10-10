import LinkingHomology
open scoped Manifold ContDiff
open Set Topology TopologicalSpace
open SeifertSurfaces.Foundations
namespace SeifertSurfaces.GenusLinking.CompressionSupport

noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma inclusion_derivative (S : CompactOrientedSurface.{0}) (U : Opens S) (x : U) :
    mfderiv (𝓡∂ 2) (𝓡∂ 2) (Subtype.val : U → S) x = ContinuousLinearMap.id ℝ (Euc 2) := by
  apply HasMFDerivAt.mfderiv
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  change HasFDerivWithinAt (writtenInExtChartAt (𝓡∂ 2) (𝓡∂ 2) x Subtype.val)
    (ContinuousLinearMap.id ℝ (Euc 2)) (range (𝓡∂ 2)) ((extChartAt (𝓡∂ 2) x) x)
  have heq : writtenInExtChartAt (𝓡∂ 2) (𝓡∂ 2) x Subtype.val =ᶠ[𝓝[range (𝓡∂ 2)] ((extChartAt (𝓡∂ 2) x) x)] id := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := 𝓡∂ 2) x] with y hy
    change (extChartAt (𝓡∂ 2) x.val) ((extChartAt (𝓡∂ 2) x).symm y).val = y
    change (extChartAt (𝓡∂ 2) x) ((extChartAt (𝓡∂ 2) x).symm y) = y
    exact (extChartAt (𝓡∂ 2) x).right_inv hy
  exact (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq heq (by
    change (extChartAt (𝓡∂ 2) x) ((extChartAt (𝓡∂ 2) x).symm ((extChartAt (𝓡∂ 2) x) x)) = _
    exact (extChartAt (𝓡∂ 2) x).right_inv ((extChartAt (𝓡∂ 2) x).map_source (mem_extChartAt_source x)))

lemma chart_inverse_agrees (S : CompactOrientedSurface.{0}) (U : Opens S) (p : U)
    {y : Euc 2} (hy : y ∈ (extChartAt (𝓡∂ 2) p).target) :
    ((extChartAt (𝓡∂ 2) p).symm y).val = (extChartAt (𝓡∂ 2) p.val).symm y := by
  rw [extChartAt, OpenPartialHomeomorph.extend_target] at hy
  exact ((chartAt (EuclideanHalfSpace 2) p.val).subtypeRestr_symm_eqOn ⟨p⟩ hy.1).symm

lemma chart_target_subset (S : CompactOrientedSurface.{0}) (U : Opens S) (p : U) :
    (extChartAt (𝓡∂ 2) p).target ⊆ (extChartAt (𝓡∂ 2) p.val).target := by
  intro y hy
  rw [extChartAt, OpenPartialHomeomorph.extend_target] at hy ⊢
  exact ⟨(chartAt (EuclideanHalfSpace 2) p.val).subtypeRestr_target_subset ⟨p⟩ hy.1,hy.2⟩

lemma chart_targets_eventually_agree (S : CompactOrientedSurface.{0}) (U : Opens S) (p : U)
    {y : Euc 2} (hy : y ∈ (extChartAt (𝓡∂ 2) p).target) :
    (extChartAt (𝓡∂ 2) p).target =ᶠ[𝓝 y] (extChartAt (𝓡∂ 2) p.val).target := by
  have hyold := chart_target_subset S U p hy
  have hval : (extChartAt (𝓡∂ 2) p.val).symm y ∈ U := by
    rw [← chart_inverse_agrees S U p hy]
    exact ((extChartAt (𝓡∂ 2) p).symm y).property
  have hn := (continuousAt_extChartAt_symm'' hyold).preimage_mem_nhds (U.isOpen.mem_nhds hval)
  filter_upwards [hn] with z hz
  change (z ∈ (extChartAt (𝓡∂ 2) p).target) = (z ∈ (extChartAt (𝓡∂ 2) p.val).target)
  apply propext
  constructor
  · exact fun h => chart_target_subset S U p h
  · intro h
    rw [extChartAt, OpenPartialHomeomorph.extend_target] at h ⊢
    refine ⟨?_,h.2⟩
    change (𝓡∂ 2).symm z ∈ ((chartAt (EuclideanHalfSpace 2) p.val).subtypeRestr ⟨p⟩).target
    refine ⟨h.1, ?_⟩
    simpa only [Opens.openPartialHomeomorphSubtypeCoe_target, extChartAt, OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply, mem_preimage] using hz

lemma chart_inverse_derivative_agrees (S : CompactOrientedSurface.{0}) (U : Opens S) (p : U)
    {y : Euc 2} (hy : y ∈ (extChartAt (𝓡∂ 2) p).target) :
    mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) (extChartAt (𝓡∂ 2) p).symm
      (extChartAt (𝓡∂ 2) p).target y =
    mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) (extChartAt (𝓡∂ 2) p.val).symm
      (extChartAt (𝓡∂ 2) p.val).target y := by
  have hcomp := mfderiv_comp_mfderivWithin y
    ((contMDiff_subtype_val (I := 𝓡∂ 2) (U := U) (n := ∞)).mdifferentiableAt (by simp))
    ((contMDiffOn_extChartAt_symm (n := ∞) p y hy).mdifferentiableWithinAt (by simp))
    ((uniqueDiffOn_extChartAt_target p y hy).uniqueMDiffWithinAt)
  rw [inclusion_derivative S U] at hcomp
  change mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
    (Subtype.val ∘ (extChartAt (𝓡∂ 2) p).symm) (extChartAt (𝓡∂ 2) p).target y =
    mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) (extChartAt (𝓡∂ 2) p).symm
      (extChartAt (𝓡∂ 2) p).target y at hcomp
  rw [← hcomp]
  change mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
    (Subtype.val ∘ (extChartAt (𝓡∂ 2) p).symm) (extChartAt (𝓡∂ 2) p).target y = _
  exact (mfderivWithin_congr_of_mem (fun z hz => chart_inverse_agrees S U p hz) hy).trans
    (mfderivWithin_congr_set (chart_targets_eventually_agree S U p hy))

noncomputable def restrictedOrientation (S : CompactOrientedSurface.{0}) (U : Opens S) :
    SmoothVolumeOrientation (𝓡∂ 2) U where
  form x := S.orientation.form x.val
  nowhere_zero x := S.orientation.nowhere_zero x.val
  smooth_coefficients p := by
    apply (S.orientation.smooth_coefficients p.val).mono (chart_target_subset S U p) |>.congr
    intro y hy
    change S.orientation.form (((extChartAt (𝓡∂ 2) p).symm y).val)
      (fun i => mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) (extChartAt (𝓡∂ 2) p).symm
        (extChartAt (𝓡∂ 2) p).target y (EuclideanSpace.single i 1)) =
      S.orientation.form ((extChartAt (𝓡∂ 2) p.val).symm y)
      (fun i => mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) (extChartAt (𝓡∂ 2) p.val).symm
        (extChartAt (𝓡∂ 2) p.val).target y (EuclideanSpace.single i 1))
    have hf := chart_inverse_agrees S U p hy
    have hd := chart_inverse_derivative_agrees S U p hy
    exact congrArg₂ (fun (x : S) (v : Fin 2 → Euc 2) => S.orientation.form x v) hf
      (funext fun i => congrArg (fun L : Euc 2 →L[ℝ] Euc 2 => L (EuclideanSpace.single i 1)) hd)

noncomputable def componentSurface (S : CompactOrientedSurface.{0}) (x : S) :
    CompactOrientedSurface.{0} := by
  letI : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace (H := EuclideanHalfSpace 2) S
  let U : Opens S := ⟨connectedComponent x,isOpen_connectedComponent⟩
  letI : CompactSpace U := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  exact {carrier := U, orientation := restrictedOrientation S U}

lemma componentSurface_boundary (S : CompactOrientedSurface.{0}) (x : S) :
    ∀ y : componentSurface S x, y ∈ (componentSurface S x).boundary ↔ y.val ∈ S.boundary := by
  letI : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace (H := EuclideanHalfSpace 2) S
  let U : Opens S := ⟨connectedComponent x,isOpen_connectedComponent⟩
  intro y
  change y ∈ (𝓡∂ 2).boundary U ↔ y.val ∈ (𝓡∂ 2).boundary S
  rw [ModelWithCorners.boundary_open]
  rfl

end
end SeifertSurfaces.GenusLinking.CompressionSupport
