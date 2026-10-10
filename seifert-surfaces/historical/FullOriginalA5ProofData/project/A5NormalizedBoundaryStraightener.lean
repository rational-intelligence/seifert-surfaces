import A5SmoothBoundaryStraightener

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- After tangent normalization, the actual smooth boundary straightener
fixes the inward differential. Thus its positive half-space sign is a
proved consequence of the original C1 jet. -/
theorem smooth_boundary_straightener_preserves_inward_jet
    (γ : ℝ → E2) (I : Set ℝ) (hI : IsOpen I) (hzero : (0 : ℝ) ∈ I)
    (hγ : ContDiffOn ℝ ∞ γ I) (a : ℝ) (ha : a ≠ 0)
    (hdγ : HasDerivAt γ (a • coordinateVector 2 1) 0) :
    ∃ d : OpenPartialHomeomorph E2 E2,
      γ 0 ∈ d.source ∧ d (γ 0) = 0 ∧
      (∀ z, d.symm z = γ (z 1) + z 0 • coordinateVector 2 0) ∧
      (∀ z ∈ d.target, z 1 ∈ I) ∧
      ContDiffOn ℝ ∞ d d.source ∧ ContDiffOn ℝ ∞ d.symm d.target ∧
      (∀ z ∈ d.source, Function.Bijective (fderiv ℝ d z)) ∧
      (∀ z ∈ d.target, Function.Bijective (fderiv ℝ d.symm z)) ∧
      fderiv ℝ d (γ 0) (coordinateVector 2 0) = coordinateVector 2 0 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (-ε) ε,
        γ t ∈ d.source ∧ d (γ t) = t • coordinateVector 2 1 := by
  let D := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).smulRight
      (a • coordinateVector 2 1) +
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight (coordinateVector 2 0)
  have hDi : Function.Injective D := by
    apply (injective_iff_map_eq_zero D).mpr
    intro z hz
    have hz0 := congrArg (fun w : E2 => w 0) hz
    have hz1 := congrArg (fun w : E2 => w 1) hz
    simp [D,coordinateVector,EuclideanSpace.single] at hz0 hz1
    have hh : z 1 = 0 := hz1.resolve_right ha
    ext i
    fin_cases i <;> simp [hz0,hh]
  have hDb : Function.Bijective D := ⟨hDi,LinearMap.injective_iff_surjective.mp hDi⟩
  obtain ⟨d,hds,hd0,hdinv,hI',hd,hdi,hdr,hdir,hclock⟩ :=
    smooth_boundary_straightener_with_transverse_vector γ I hI hzero hγ
      (a • coordinateVector 2 1) (coordinateVector 2 0) hdγ hDb
  refine ⟨d,hds,hd0,hdinv,hI',hd,hdi,hdr,hdir,?_,hclock⟩
  let α : ℝ → E2 := fun t => γ 0 + t • coordinateVector 2 0
  have hα : HasDerivAt α (coordinateVector 2 0) 0 := by
    simpa only [α,id_eq,one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector 2 0)).const_add (γ 0)
  have hα0 : α 0 = γ 0 := by simp [α]
  have hdd := ((hd.contDiffAt (d.open_source.mem_nhds hds)).differentiableAt (by simp)).hasFDerivAt
  have hcomp : HasDerivAt (d ∘ α) (fderiv ℝ d (γ 0) (coordinateVector 2 0)) 0 := by
    apply HasFDerivAt.comp_hasDerivAt 0 _ hα
    rwa [hα0]
  let line : ℝ → E2 := fun t => t • coordinateVector 2 0
  have hl : HasDerivAt line (coordinateVector 2 0) 0 := by
    simpa only [line,id_eq,one_smul] using
      (hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector 2 0)
  have hzdt : (0 : E2) ∈ d.target := hd0 ▸ d.map_source hds
  have heq : d ∘ α =ᶠ[𝓝 0] line := by
    have hline : Continuous line := by dsimp [line]; fun_prop
    filter_upwards [hline.continuousAt.preimage_mem_nhds
      (show d.target ∈ 𝓝 (line 0) by simpa [line] using d.open_target.mem_nhds hzdt)] with t ht
    have hi : d.symm (line t) = α t := by
      rw [hdinv]
      simp [line,α,coordinateVector,EuclideanSpace.single]
    change d (α t) = line t
    rw [← hi,d.right_inv ht]
  exact (hcomp.congr_of_eventuallyEq heq.symm).unique hl

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
