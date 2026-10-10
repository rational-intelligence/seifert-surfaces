import ChartFlowParameters

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

theorem chartRealFlow_hasMFDerivAt
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, z 0 = 0 → V (t,z) 0 = 0)
    (hlocal : halfspaceSpatialSupport V ⊆ e.target) (s t : ℝ) {x : M} (hx : x ∈ e.source)
    (w : TangentSpace (𝓡∂ 3) (chartRealFlow e hV hs hb s t x))
    (hw : V (t,(e.extend (𝓡∂ 3)) (chartRealFlow e hV hs hb s t x)) =
      (show Euc 3 from mfderiv (𝓡∂ 3) 𝓘(ℝ,Euc 3) (e.extend (𝓡∂ 3))
        (chartRealFlow e hV hs hb s t x) w)) :
    HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 3) (fun u => chartRealFlow e hV hs hb s u x) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight w) := by
  let γ : ℝ → M := fun u => chartRealFlow e hV hs hb s u x
  have hγ : ContMDiff 𝓘(ℝ,ℝ) (𝓡∂ 3) ∞ γ :=
    (chartRealFlow_contMDiff e he hV hs hb hlocal).comp
      ((contMDiff_const.prodMk contMDiff_id).prodMk contMDiff_const)
  have hγd : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡∂ 3) γ t := hγ.mdifferentiableAt (by simp)
  have hγsrc : γ t ∈ e.source := chartRealFlow_mapsTo e hV hs hb hlocal s t hx
  have hed := (e.contMDiffOn_extend he).mdifferentiableOn (by simp)
    |>.mdifferentiableAt (e.open_source.mem_nhds hγsrc)
  have hchain := mfderiv_comp t hed hγd
  have hcoord := chartRealFlow_coordinate_derivative e hV hs hb hlocal s t hx
  change HasDerivAt ((e.extend (𝓡∂ 3)) ∘ γ)
    (V (t,(e.extend (𝓡∂ 3)) (γ t))) t at hcoord
  rw [mfderiv_eq_fderiv,hcoord.hasFDerivAt.fderiv] at hchain
  have hone := congrArg (fun L =>
    NormedSpace.fromTangentSpace ((e.extend (𝓡∂ 3)) (γ t)) (L 1)) hchain
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.toSpanSingleton_apply] at hone
  have hcast : NormedSpace.fromTangentSpace (𝕜 := ℝ) t 1 = (1 : ℝ) := rfl
  rw [hcast,one_smul] at hone
  have hone' : (show Euc 3 from mfderiv (𝓡∂ 3) 𝓘(ℝ,Euc 3) (e.extend (𝓡∂ 3)) (γ t)
      (mfderiv 𝓘(ℝ,ℝ) (𝓡∂ 3) γ t 1)) = V (t,(e.extend (𝓡∂ 3)) (γ t)) := hone.symm
  have hwone : mfderiv 𝓘(ℝ,ℝ) (𝓡∂ 3) γ t 1 = w :=
    (isInvertible_mfderiv_extend
      (IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞) he) hγsrc).injective
        (hone'.trans hw)
  apply hγd.hasMFDerivAt.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  let ar : ℝ := a
  change mfderiv 𝓘(ℝ,ℝ) (𝓡∂ 3) γ t ar = ar • w
  calc
    mfderiv 𝓘(ℝ,ℝ) (𝓡∂ 3) γ t ar =
        mfderiv 𝓘(ℝ,ℝ) (𝓡∂ 3) γ t (ar • (1 : TangentSpace 𝓘(ℝ,ℝ) t)) := by
          congr 1
          change ar = ar * 1
          rw [mul_one]
    _ = ar • w := by rw [map_smul,hwone]

set_option backward.isDefEq.respectTransparency false in
theorem chart_coordinate_hasDerivWithinAt
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {γ : ℝ → M} {A : Set ℝ} {t : ℝ} (ht : γ t ∈ e.source)
    (w : TangentSpace (𝓡∂ 3) (γ t))
    (hγ : HasMFDerivWithinAt 𝓘(ℝ,ℝ) (𝓡∂ 3) γ A t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight w)) :
    HasDerivWithinAt (fun u => (e.extend (𝓡∂ 3)) (γ u))
      (show Euc 3 from mfderiv (𝓡∂ 3) 𝓘(ℝ,Euc 3) (e.extend (𝓡∂ 3)) (γ t) w) A t := by
  have hed := (e.contMDiffOn_extend he).mdifferentiableOn (by simp)
    |>.mdifferentiableAt (e.open_source.mem_nhds ht)
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt,← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (hed.hasMFDerivAt.comp_hasMFDerivWithinAt t hγ).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  let ar : ℝ := a
  change (mfderiv (𝓡∂ 3) 𝓘(ℝ,Euc 3) (e.extend (𝓡∂ 3)) (γ t)) (ar • w) =
    ar • ((mfderiv (𝓡∂ 3) 𝓘(ℝ,Euc 3) (e.extend (𝓡∂ 3)) (γ t)) w)
  exact map_smul _ _ _

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
