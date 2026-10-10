import CollarRemainingE
import CollarRemainingI
import Foundations
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option maxSynthPendingDepth 3
open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers.CollarCutHelpers
open Foundations
universe u v w
noncomputable section

/-! G-CHART. Source: sealed blueprint §4, H01–H03. These are obligations,
not admitted external facts. The halfspace normal is coordinate zero. -/

theorem compact_circle_halfspace_extension (a : ℝ) (ha : 0 < a)
    (h : Circle × ℝ → ℝ)
    (hh : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h
      {p | 0 ≤ p.2 ∧ p.2 < a}) :
    ∃ a' : ℝ, 0 < a' ∧ a' < a ∧ ∃ h_ext : Circle × ℝ → ℝ,
      ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h_ext
        {p | |p.2| < a'} ∧
      EqOn h_ext h {p | 0 ≤ p.2 ∧ p.2 < a'} ∧
      ∀ z, h_ext (z, 0) = h (z, 0) ∧
        deriv (fun s => h_ext (z, s)) 0 =
          derivWithin (fun s => h (z, s)) (Ici 0) 0 := by
  obtain ⟨D⟩ := Remaining.E4_circle_extension_data a ha h hh
  obtain ⟨hs, heq, hj⟩ := Remaining.E5_circle_weighted_extension hh D
  exact ⟨D.a', D.a'_pos, D.a'_lt, Remaining.circleWeightedExtension D, hs, heq, hj⟩

theorem inward_coordinate_change_positive {n : ℕ} [NeZero n]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] (x : M) (hx : x ∈ (𝓡∂ n).boundary M)
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M) (hxe : x ∈ e.source) :
    ∃ a : ℝ, 0 < a ∧ ∀ w : TangentSpace (𝓡∂ n) x,
      (tangentSpaceCastModel 𝓘(ℝ, Euc n) ((e.extend (𝓡∂ n)) x)
        (mfderiv (𝓡∂ n) 𝓘(ℝ, Euc n) (e.extend (𝓡∂ n)) x w)) 0 =
          a * inwardCoordinate x w := by
  let f : M → ℝ := fun y => ((e.extend (𝓡∂ n)) y) 0
  have hfs : ContMDiffOn (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ f e.source :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).contMDiff.comp_contMDiffOn
      (e.contMDiffOn_extend he)
  have hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f x :=
    (hfs.contMDiffAt (e.open_source.mem_nhds hxe)).mdifferentiableAt (by simp)
  have he1 : e ∈ IsManifold.maximalAtlas (𝓡∂ n) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hfx : f x = 0 := by
    let e' : PartialDiffeomorph (𝓡∂ n) (𝓡∂ n) M (EuclideanHalfSpace n) ∞ :=
      { __ := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
        contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
    have hd : IsLocalDiffeomorphAt (𝓡∂ n) (𝓡∂ n) ∞ e x :=
      ⟨e', hxe, fun _ _ => rfl⟩
    have hb := (hd.isBoundaryPoint_iff (by simp)).mp hx
    simpa [f, ModelWithCorners.IsBoundaryPoint, extChartAt,
      frontier_range_modelWithCornersEuclideanHalfSpace, eq_comm] using hb
  have hcomp : mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f x =
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).comp
        (mfderiv (𝓡∂ n) 𝓘(ℝ, Euc n) (e.extend (𝓡∂ n)) x) := by
    have hh := mfderiv_comp x
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).differentiableAt.mdifferentiableAt)
      ((e.contMDiffAt_extend he hxe).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hh
    change mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f x =
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).comp
        (mfderiv (𝓡∂ n) 𝓘(ℝ, Euc n) (e.extend (𝓡∂ n)) x) at hh
    exact hh
  let L : Euc n →L[ℝ] ℝ := mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f x
  let u : Euc n := EuclideanSpace.single 0 1
  have hu : u 0 = 1 := by simp [u]
  have hnonneg (v : Euc n) (hv : 0 ≤ v 0) : 0 ≤ L v := by
    let z := extChartAt (𝓡∂ n) x x
    have hz : z 0 = 0 := by
      have hh := hx
      change (𝓡∂ n).IsBoundaryPoint x at hh
      rw [ModelWithCorners.isBoundaryPoint_iff,
        frontier_range_modelWithCornersEuclideanHalfSpace] at hh
      exact hh.symm
    have hmin : IsLocalMinOn (writtenInExtChartAt (𝓡∂ n) 𝓘(ℝ, ℝ) x f)
        (range (𝓡∂ n)) z := by
      have hpos : ∀ᶠ y in 𝓝 x, 0 ≤ f y :=
        Filter.Eventually.of_forall (fun y => (e y).property)
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (extChartAt_preimage_mem_nhds (I := 𝓡∂ n) hpos)] with w hw
      change f ((extChartAt (𝓡∂ n) x).symm z) ≤ f ((extChartAt (𝓡∂ n) x).symm w)
      rw [extChartAt_to_inv, hfx]
      exact hw
    change @LE.le ℝ inferInstance 0 (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f x v)
    rw [hf.mfderiv]
    apply hmin.fderivWithin_nonneg
    apply mem_posTangentConeAt_of_segment_subset
    apply (𝓡∂ n).convex_range.segment_subset
    · exact mem_range_self _
    · rw [range_modelWithCornersEuclideanHalfSpace]
      change 0 ≤ (z + v) 0
      simpa only [PiLp.add_apply, hz, zero_add] using hv
  have hker (v : Euc n) (hv : v 0 = 0) : L v = 0 := by
    apply le_antisymm
    · have hh := hnonneg (-v) (by simp only [PiLp.neg_apply, hv, neg_zero, le_refl])
      simpa only [map_neg, neg_nonneg] using hh
    · exact hnonneg v (le_of_eq hv.symm)
  have hL : L = (L u) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n) := by
    ext v
    have hh := hker (v - (v 0) • u) (by simp only [PiLp.sub_apply, PiLp.smul_apply,
      hu, smul_eq_mul, mul_one, sub_self])
    change L v = L u * v 0
    simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero, mul_comm] using hh
  have hreg : L ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := (isInvertible_mfderiv_extend he1 hxe).surjective u
    have hh := congrArg (fun A : Euc n →L[ℝ] ℝ => A v) hzero
    change mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f x v = 0 at hh
    rw [hcomp] at hh
    change (show Euc n from
      mfderiv (𝓡∂ n) 𝓘(ℝ, Euc n) (e.extend (𝓡∂ n)) x v) 0 = 0 at hh
    rw [hv, hu] at hh
    norm_num at hh
  have ha : 0 < L u := by
    refine lt_of_le_of_ne (hnonneg u (by rw [hu]; exact zero_le_one)) ?_
    intro hh
    apply hreg
    rw [hL, ← hh, zero_smul]
  refine ⟨L u, ha, ?_⟩
  intro w
  have hw := congrArg (fun A : Euc n →L[ℝ] ℝ => A w) hL
  change mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) f x w = L u * (show Euc n from w) 0 at hw
  rw [hcomp] at hw
  change (show Euc n from
    mfderiv (𝓡∂ n) 𝓘(ℝ, Euc n) (e.extend (𝓡∂ n)) x w) 0 = L u *
      inwardCoordinate x w
  have hI : inwardCoordinate x w = (show Euc n from w) 0 := by
    unfold inwardCoordinate
    rw [mfderiv_extChartAt_self]
    rfl
  rw [hI]
  exact hw


theorem halfspace_atlas_boundary_interior {n : ℕ} [NeZero n]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M) (x : M) (hx : x ∈ e.source) :
    (x ∈ (𝓡∂ n).boundary M ↔ ((𝓡∂ n) (e x)) 0 = 0) ∧
    (x ∈ (𝓡∂ n).interior M ↔ 0 < ((𝓡∂ n) (e x)) 0) := by
  let e' : PartialDiffeomorph (𝓡∂ n) (𝓡∂ n) M (EuclideanHalfSpace n) ∞ :=
    { __ := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  have hd : IsLocalDiffeomorphAt (𝓡∂ n) (𝓡∂ n) ∞ e x :=
    ⟨e', hx, fun _ _ => rfl⟩
  have hb := hd.isBoundaryPoint_iff (by simp)
  have hi := hd.isInteriorPoint_iff (by simp)
  constructor
  · simpa [ModelWithCorners.boundary, ModelWithCorners.IsBoundaryPoint,
      extChartAt, frontier_range_modelWithCornersEuclideanHalfSpace, eq_comm, e'] using hb
  · simpa [ModelWithCorners.interior, ModelWithCorners.IsInteriorPoint,
      extChartAt, interior_range_modelWithCornersEuclideanHalfSpace, e'] using hi


theorem inward_diffeomorph_positive {n : ℕ} [NeZero n]
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace n) M] [ChartedSpace (EuclideanHalfSpace n) N]
    [IsManifold (𝓡∂ n) ∞ M] [IsManifold (𝓡∂ n) ∞ N]
    (d : Diffeomorph (𝓡∂ n) (𝓡∂ n) M N ∞)
    (x : M) (hx : x ∈ (𝓡∂ n).boundary M) :
    ∃ a : ℝ, 0 < a ∧ ∀ w : TangentSpace (𝓡∂ n) x,
      inwardCoordinate (d x) (mfderiv (𝓡∂ n) (𝓡∂ n) d x w) =
        a * inwardCoordinate x w := by
  let e : OpenPartialHomeomorph M (EuclideanHalfSpace n) :=
    d.toHomeomorph.toOpenPartialHomeomorph.trans
      (chartAt (EuclideanHalfSpace n) (d x))
  have hxe : x ∈ e.source := by simp [e, mem_chart_source]
  have he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M := by
    apply e.mem_maximalAtlas_of_contMDiffOn
    · exact contMDiffOn_chart.comp d.contMDiff.contMDiffOn
        (by intro y hy; exact hy.2)
    · have hs := d.symm.contMDiff.comp_contMDiffOn
        (contMDiffOn_chart_symm (I := 𝓡∂ n) (n := ∞) (x := d x))
      simpa only [e, OpenPartialHomeomorph.coe_trans_symm,
        Homeomorph.toOpenPartialHomeomorph_symm_apply, Diffeomorph.coe_toHomeomorph_symm,
        OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
        preimage_univ, inter_univ] using hs
  obtain ⟨a, ha, hw⟩ := inward_coordinate_change_positive x hx e he hxe
  refine ⟨a, ha, ?_⟩
  intro w
  have hh := mfderiv_comp x
    (mdifferentiableAt_extChartAt (I := 𝓡∂ n) (mem_chart_source _ (d x)))
    (d.contMDiff.mdifferentiable (by simp) x)
  have heq : (e.extend (𝓡∂ n) : M → Euc n) =
      (extChartAt (𝓡∂ n) (d x)) ∘ d := rfl
  rw [heq, hh] at hw
  exact hw w


end
end SeifertSurfaces.LongitudeProducers.CollarCutHelpers
