import A5TopologicalSignsOnNewAtlasV466
import A5HalfballDomainsV466
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
universe u

theorem a5_surface_interior_dense (S : A5CompactSmoothCarrier.{u}) (x : S) :
    x ∈ closure ((𝓡∂ 2).interior S) := by
  let c := extChartAt (𝓡∂ 2) x
  have hy : c x ∈ closure (interior c.target) :=
    extChartAt_target_subset_closure_interior (mem_extChartAt_target (I := 𝓡∂ 2) x)
  have hcl := mem_closure_image (continuousAt_extChartAt_symm (I := 𝓡∂ 2) x) hy
  rw [c.left_inv (mem_extChartAt_source x)] at hcl
  apply closure_mono (t := (𝓡∂ 2).interior S) ?_ hcl
  rintro z ⟨y,hy,rfl⟩
  change (𝓡∂ 2).IsInteriorPoint (c.symm y)
  apply ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
    (chart_mem_atlas (EuclideanHalfSpace 2) x)
    (by simpa only [c,extChartAt_source] using c.map_target (interior_subset hy))).mpr
  change c (c.symm y) ∈ interior c.target
  rwa [c.right_inv (interior_subset hy)]

theorem a5_transitionJacobian_continuousAt (S : A5CompactSmoothCarrier.{u}) (p q x : S)
    (hp : x ∈ (extChartAt (𝓡∂ 2) p).source)
    (hq : x ∈ (extChartAt (𝓡∂ 2) q).source) :
    ContinuousAt (fun z => (a5TransitionJacobian S p q z).det) x := by
  let e := extChartAt (𝓡∂ 2) p
  have hy := e.map_source hp
  have he : e.symm (e x) = x := e.left_inv hp
  have hys : e x ∈ (e.symm ≫ extChartAt (𝓡∂ 2) q).source := by
    refine ⟨hy,?_⟩
    change e.symm (e x) ∈ (extChartAt (𝓡∂ 2) q).source
    rw [he]
    exact hq
  have ht : ContDiffWithinAt ℝ ∞ ((extChartAt (𝓡∂ 2) q) ∘ e.symm) e.target (e x) :=
    (contDiffWithinAt_ext_coord_change q p hys).mono (extChartAt_target_subset_range p)
  have hder := ht.fderivWithin_right (uniqueDiffOn_extChartAt_target p)
    (m := (∞ : ℕ∞ω)) (by simp) hy
  have hcoeff : ∀ a b : Fin 2, ContDiffWithinAt ℝ ∞
      (fun z => (fderivWithin ℝ ((extChartAt (𝓡∂ 2) q) ∘ e.symm)
        e.target z (EuclideanSpace.single b 1)) a) e.target (e x) := by
    intro a b
    have hdv := hder.clm_apply (contDiffWithinAt_const (c := EuclideanSpace.single b (1 : ℝ)))
    exact (EuclideanSpace.proj a).contDiff.contDiffAt.comp_contDiffWithinAt (e x) hdv
  have hdet : ContinuousWithinAt
      (fun z => Matrix.det (fun a b : Fin 2 => fderivWithin ℝ
        ((extChartAt (𝓡∂ 2) q) ∘ e.symm) e.target z (EuclideanSpace.single b 1) a))
      e.target (e x) := by
    simp only [Matrix.det_fin_two]
    exact (((hcoeff 0 0).mul (hcoeff 1 1)).sub ((hcoeff 0 1).mul (hcoeff 1 0))).continuousWithinAt
  have hcomp := hdet.comp ((continuousOn_extChartAt p) x hp) e.mapsTo
  exact hcomp.continuousAt ((isOpen_extChartAt_source (I := 𝓡∂ 2) p).mem_nhds hp)

/-- A nonzero continuous signed transition determinant remains positive at boundary points. -/
theorem a5_positive_transition_boundary_extension (S : A5CompactSmoothCarrier.{u})
    (p q : S) (U V : Set S) (hU : IsOpen U) (hV : IsOpen V)
    (hUs : U ⊆ (extChartAt (𝓡∂ 2) p).source)
    (hVs : V ⊆ (extChartAt (𝓡∂ 2) q).source)
    (s t : ℝ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (hpos : ∀ x, x ∈ U → x ∈ V → (𝓡∂ 2).IsInteriorPoint x →
      0 < t * s * (a5TransitionJacobian S p q x).det) :
    ∀ x, x ∈ U → x ∈ V → 0 < t * s * (a5TransitionJacobian S p q x).det := by
  intro x hxU hxV
  have hd := a5_transitionJacobian_det_ne_zero S p q x (hUs hxU) (hVs hxV)
  have hne : t * s * (a5TransitionJacobian S p q x).det ≠ 0 := by
    rcases hs with rfl|rfl <;> rcases ht with rfl|rfl <;> simpa using hd
  have hc : ContinuousAt (fun z => t * s * (a5TransitionJacobian S p q z).det) x :=
    continuousAt_const.mul (a5_transitionJacobian_continuousAt S p q x (hUs hxU) (hVs hxV))
  let W := (U ∩ V) ∩ (𝓡∂ 2).interior S
  have hxcl : x ∈ closure W := by
    rw [mem_closure_iff]
    intro O hO hxO
    obtain ⟨z,hz,hzi⟩ := mem_closure_iff.mp (a5_surface_interior_dense S x)
      (O ∩ (U ∩ V)) (hO.inter (hU.inter hV)) ⟨hxO,hxU,hxV⟩
    exact ⟨z,hz.1,hz.2,hzi⟩
  have hge : 0 ≤ t * s * (a5TransitionJacobian S p q x).det :=
    ContinuousWithinAt.closure_le hxcl continuousWithinAt_const hc.continuousWithinAt
      (fun z hz => (hpos z hz.1.1 hz.1.2 hz.2).le)
  exact lt_of_le_of_ne hge hne.symm

#print axioms a5_positive_transition_boundary_extension
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
