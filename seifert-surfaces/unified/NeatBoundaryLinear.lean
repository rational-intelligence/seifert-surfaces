import TraceVelocity
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.ContinuousInverse

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v

theorem inwardCoordinate_eq {n : ℕ} [NeZero n] {N : Type*}
    [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace n) N]
    [IsManifold (𝓡∂ n) ∞ N] (x : N) (w : TangentSpace (𝓡∂ n) x) :
    inwardCoordinate x w = (show Euc n from w) 0 := by
  unfold inwardCoordinate
  rw [mfderiv_extChartAt_self]
  rfl

/-- Neat transversality determines a positive normal factor for the actual
embedding differential. -/
theorem neat_inward_differential_positive {S : CompactOrientedSurface.{u}} {M : Type v}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] (f : NeatEmbedding S M) (x : S) (hx : x ∈ S.boundary) :
    ∃ a : ℝ, 0 < a ∧ ∀ w : TangentSpace (𝓡∂ 2) x,
      inwardCoordinate (f.toFun x) (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun x w) =
        a * inwardCoordinate x w := by
  let c := extChartAt (𝓡∂ 3) (f.toFun x)
  let q : S → ℝ := fun y => c (f.toFun y) 0
  have hfd : MDifferentiableAt (𝓡∂ 2) (𝓡∂ 3) f.toFun x :=
    f.smoothEmbedding.contMDiff.mdifferentiableAt (by simp)
  have hcd := mdifferentiableAt_extChartAt (I := 𝓡∂ 3) (mem_chart_source _ (f.toFun x))
  have hqd : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ, ℝ) q x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).differentiableAt.mdifferentiableAt.comp x
      (hcd.comp x hfd)
  have hchain : mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) q x =
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).comp
        ((mfderiv (𝓡∂ 3) 𝓘(ℝ, Euc 3) c (f.toFun x)).comp
          (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun x)) := by
    have h := mfderiv_comp x
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).differentiableAt.mdifferentiableAt)
      (hcd.comp x hfd)
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv, mfderiv_comp x hcd hfd] at h
    exact h
  have hxb : f.toFun x ∈ (𝓡∂ 3).boundary M := by
    change x ∈ f.toFun ⁻¹' (𝓡∂ 3).boundary M
    rw [f.boundary_preimage]
    exact hx
  have hqx : q x = 0 := by
    change (𝓡∂ 3).IsBoundaryPoint (f.toFun x) at hxb
    rw [ModelWithCorners.isBoundaryPoint_iff,
      frontier_range_modelWithCornersEuclideanHalfSpace] at hxb
    exact hxb.symm
  let L : Euc 2 →L[ℝ] ℝ := mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) q x
  let u : Euc 2 := EuclideanSpace.single 0 1
  have hu : u 0 = 1 := by simp [u]
  have hnonneg (w : Euc 2) (hw : 0 ≤ w 0) : 0 ≤ L w := by
    let z := extChartAt (𝓡∂ 2) x x
    have hz : z 0 = 0 := by
      have hh := hx
      change (𝓡∂ 2).IsBoundaryPoint x at hh
      rw [ModelWithCorners.isBoundaryPoint_iff,
        frontier_range_modelWithCornersEuclideanHalfSpace] at hh
      exact hh.symm
    have hmin : IsLocalMinOn (writtenInExtChartAt (𝓡∂ 2) 𝓘(ℝ, ℝ) x q)
        (range (𝓡∂ 2)) z := by
      have hpos : ∀ᶠ y in 𝓝 x, 0 ≤ q y :=
        Filter.Eventually.of_forall (fun y => (chartAt (EuclideanHalfSpace 3)
          (f.toFun x) (f.toFun y)).property)
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (extChartAt_preimage_mem_nhds (I := 𝓡∂ 2) hpos)] with w hw
      change q ((extChartAt (𝓡∂ 2) x).symm z) ≤ q ((extChartAt (𝓡∂ 2) x).symm w)
      rw [extChartAt_to_inv, hqx]
      exact hw
    change @LE.le ℝ inferInstance 0 (mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) q x w)
    rw [hqd.mfderiv]
    apply hmin.fderivWithin_nonneg
    apply mem_posTangentConeAt_of_segment_subset
    apply (𝓡∂ 2).convex_range.segment_subset
    · exact mem_range_self _
    · rw [range_modelWithCornersEuclideanHalfSpace]
      change 0 ≤ (z + w) 0
      simpa only [PiLp.add_apply, hz, zero_add] using hw
  have hker (w : Euc 2) (hw : w 0 = 0) : L w = 0 := by
    apply le_antisymm
    · have h := hnonneg (-w) (by simp only [PiLp.neg_apply, hw, neg_zero, le_refl])
      simpa only [map_neg, neg_nonneg] using h
    · exact hnonneg w (le_of_eq hw.symm)
  have hL : ∀ w : Euc 2, L w = L u * w 0 := by
    intro w
    have h := hker (w - (w 0) • u) (by simp only [PiLp.sub_apply, PiLp.smul_apply,
      hu, smul_eq_mul, mul_one, sub_self])
    simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero, mul_comm] using h
  have hread (w : TangentSpace (𝓡∂ 2) x) :
      L (show Euc 2 from w) =
        inwardCoordinate (f.toFun x) (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun x w) := by
    change mfderiv (𝓡∂ 2) 𝓘(ℝ, ℝ) q x w = _
    rw [hchain]
    rfl
  have hne : L u ≠ 0 := by
    obtain ⟨w, hw⟩ := f.boundary_transverse x hx
    intro hzero
    apply hw
    rw [← hread]
    rw [hL, hzero, zero_mul]
  refine ⟨L u, lt_of_le_of_ne (hnonneg u (by rw [hu]; exact zero_le_one)) hne.symm, ?_⟩
  intro w
  rw [← hread, inwardCoordinate_eq]
  exact hL w

/-- Correct an arbitrary linear left inverse to respect both boundary normal
coordinates. This gives the pointwise boundary-compatible retraction needed
before extending the prescribed velocity. -/
theorem exists_boundary_compatible_leftInverse
    (A : Euc 2 →L[ℝ] Euc 3) (hA : Function.Injective A)
    (a : ℝ) (ha : a ≠ 0) (hfactor : ∀ w, A w 0 = a * w 0) :
    ∃ R : Euc 3 →L[ℝ] Euc 2,
      Function.LeftInverse R A ∧ ∀ z, R z 0 = z 0 / a := by
  obtain ⟨B,hB⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hA
  let u : Euc 2 := EuclideanSpace.single 0 1
  let δ : Euc 3 →L[ℝ] ℝ :=
    a⁻¹ • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3) -
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp B
  let R : Euc 3 →L[ℝ] Euc 2 := B + δ.smulRight u
  refine ⟨R, ?_, ?_⟩
  · intro w
    have hz : δ (A w) = 0 := by
      change a⁻¹ * A w 0 - B (A w) 0 = 0
      rw [hfactor, hB]
      field_simp
      ring
    change B (A w) + δ (A w) • u = w
    rw [hB, hz, zero_smul, add_zero]
  · intro z
    change B z 0 + δ z * u 0 = z 0 / a
    simp only [u, PiLp.single_apply, ↓reduceIte, mul_one]
    change B z 0 + (a⁻¹ * z 0 - B z 0) = z 0 / a
    rw [add_sub_cancel, div_eq_mul_inv, mul_comm]

theorem neat_boundary_leftInverse {S : CompactOrientedSurface.{u}} {M : Type v}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] (f : NeatEmbedding S M) (x : S) (hx : x ∈ S.boundary) :
    ∃ (a : ℝ) (R : Euc 3 →L[ℝ] Euc 2), 0 < a ∧
      Function.LeftInverse R (mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun x) ∧
      ∀ z, R z 0 = z 0 / a := by
  obtain ⟨a,ha,hfactor⟩ := neat_inward_differential_positive f x hx
  let A : Euc 2 →L[ℝ] Euc 3 := mfderiv (𝓡∂ 2) (𝓡∂ 3) f.toFun x
  have hA : Function.Injective A := f.smoothEmbedding.isImmersion.mfderiv_injective (by simp) x
  have hf : ∀ w : Euc 2, A w 0 = a * w 0 := by
    intro w
    have h := hfactor (show TangentSpace (𝓡∂ 2) x from w)
    rw [inwardCoordinate_eq (f.toFun x),
      inwardCoordinate_eq x (show TangentSpace (𝓡∂ 2) x from w)] at h
    exact h
  obtain ⟨R,hR,hRnormal⟩ := exists_boundary_compatible_leftInverse A hA a ha.ne' hf
  exact ⟨a,R,ha,hR,hRnormal⟩

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
