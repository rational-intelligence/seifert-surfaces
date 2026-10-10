import A7CoordinateLocalExtensionV464
import A7NativeChartBoundaryV464
import A7NativeBoundaryCovectorV464
import A7HalfSpaceSignV464
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates
universe u v
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]
  {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

def nativeCoordinateDifferential (f : S → M) (x : S) : E2 →L[ℝ] E3 :=
  (tangentSpaceCastModel (𝓡∂ 3) (f x)).toContinuousLinearMap.comp
    ((mfderiv (𝓡∂ 2) (𝓡∂ 3) f x).comp
      (tangentSpaceCastModel (𝓡∂ 2) x).symm.toContinuousLinearMap)

theorem native_target_coordinate_extension {f : S → M}
    (hf : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ f) (x : S) :
    ∃ g : E2 → E3, ContDiff ℝ ∞ g ∧
      g =ᶠ[𝓝[range (𝓡∂ 2)] (extChartAt (𝓡∂ 2) x x)]
        ((extChartAt (𝓡∂ 3) (f x)) ∘ f ∘ (extChartAt (𝓡∂ 2) x).symm) ∧
      HasFDerivAt g (nativeCoordinateDifferential f x) (extChartAt (𝓡∂ 2) x x) := by
  let d := extChartAt (𝓡∂ 3) (f x)
  let W := f ⁻¹' d.source
  have hW : IsOpen W := (isOpen_extChartAt_source (f x)).preimage hf.continuous
  have hfx : x ∈ W := mem_extChartAt_source (f x)
  have hF : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,E3) ∞ (d ∘ f) W :=
    (contMDiffOn_extChartAt (I := 𝓡∂ 3) (n := ∞) (x := f x)).comp hf.contMDiffOn
      (fun _ hy => by simpa only [W,d,extChartAt_source] using hy)
  obtain ⟨g,hg,hge,hgD⟩ := coordinate_local_extension hW hF x hfx
  have hd : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ,E3) d (f x) :=
    (contMDiffAt_extChartAt (I := 𝓡∂ 3) (n := ∞)).mdifferentiableAt (by simp)
  have hD : (tangentSpaceCastModel 𝓘(ℝ,E3) ((d ∘ f) x)).toContinuousLinearMap.comp
      ((mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) (d ∘ f) x).comp
        (tangentSpaceCastModel (𝓡∂ 2) x).symm.toContinuousLinearMap) =
      nativeCoordinateDifferential f x := by
    apply ContinuousLinearMap.ext
    intro z
    change (show E3 from mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) (d ∘ f) x z) =
      (show E3 from mfderiv (𝓡∂ 2) (𝓡∂ 3) f x z)
    rw [mfderiv_comp x hd (hf.mdifferentiableAt (by simp))]
    change (mfderiv (𝓡∂ 3) 𝓘(ℝ,E3) (extChartAt (𝓡∂ 3) (f x)) (f x)) _ = _
    rw [mfderiv_extChartAt_self]
    rfl
  refine ⟨g,hg,?_,?_⟩
  · exact hge
  · rwa [hD] at hgD

theorem native_boundary_coordinate_row {f : S → M}
    (hf : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ f) (x : S)
    (hx : x ∈ (𝓡∂ 2).boundary S) (hfx : f x ∈ (𝓡∂ 3).boundary M)
    (htrans : ∃ w : TangentSpace (𝓡∂ 2) x,
      inwardCoordinate (f x) (mfderiv (𝓡∂ 2) (𝓡∂ 3) f x w) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : E2, nativeCoordinateDifferential f x z 0 = c * z 0 := by
  let F := (extChartAt (𝓡∂ 3) (f x)) ∘ f
  let p : E3 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let q : S → ℝ := p ∘ F
  have hd : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ,E3) (extChartAt (𝓡∂ 3) (f x)) (f x) :=
    (contMDiffAt_extChartAt (I := 𝓡∂ 3) (n := ∞)).mdifferentiableAt (by simp)
  have hF : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ,E3) F x :=
    hd.comp x (hf.mdifferentiableAt (by simp))
  have hp : MDifferentiableAt 𝓘(ℝ,E3) 𝓘(ℝ) p (F x) :=
    (p.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp)
  have hq : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ) q x := hp.comp x hF
  have hqx : q x = 0 := (chart_boundary_coordinate_iff (f x) (f x) (mem_chart_source _ _)).1 hfx
  have hmin : ∀ᶠ y in 𝓝 x, 0 ≤ q y := by
    apply Eventually.of_forall
    intro y
    exact (chartAt (EuclideanHalfSpace 3) (f x) (f y)).property
  have hqd (z : E2) : (show ℝ from mfderiv (𝓡∂ 2) 𝓘(ℝ) q x z) =
      nativeCoordinateDifferential f x z 0 := by
    rw [mfderiv_comp x hp hF]
    rw [mfderiv_eq_fderiv,p.hasFDerivAt.fderiv]
    change (show E3 from mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) F x z) 0 =
      (show E3 from mfderiv (𝓡∂ 2) (𝓡∂ 3) f x z) 0
    rw [mfderiv_comp x hd (hf.mdifferentiableAt (by simp)),mfderiv_extChartAt_self]
    rfl
  let e0 : E2 := EuclideanSpace.single 0 1
  let c : ℝ := nativeCoordinateDifferential f x e0 0
  have hrow (z : E2) : nativeCoordinateDifferential f x z 0 = c * z 0 := by
    have hpz : inwardCoordinate x (show TangentSpace (𝓡∂ 2) x from boundaryProjection z) = 0 := by
      rw [inwardCoordinate_eq_coordinate]
      exact boundaryProjection_zero z
    have hz := boundary_minimum_covector hq hx hqx hmin (boundaryProjection z) hpz
    change (show ℝ from mfderiv (𝓡∂ 2) 𝓘(ℝ) q x (boundaryProjection z)) = 0 at hz
    rw [hqd] at hz
    have he : z = boundaryProjection z + z 0 • e0 := by
      have h := boundaryProjection_difference z
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    conv_lhs => rw [he]
    simp only [map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,hz,zero_add,smul_eq_mul]
    exact mul_comm _ _
  have hc : 0 ≤ c := by
    have h := boundary_minimum_covector_nonneg hq hx hqx hmin e0 (by simp [e0,EuclideanSpace.single])
    change 0 ≤ nativeCoordinateDifferential f x e0 0
    rw [←hqd e0]
    exact h
  have hcn : c ≠ 0 := by
    intro hc0
    obtain ⟨w,hw⟩ := htrans
    apply hw
    rw [inwardCoordinate_eq_coordinate]
    change nativeCoordinateDifferential f x (show E2 from w) 0 = 0
    rw [hrow,hc0,zero_mul]
  exact ⟨c,lt_of_le_of_ne hc (Ne.symm hcn),hrow⟩

end SeifertSurfaces.OriginalEndpoints.A7Support
