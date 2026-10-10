import A5PuncturedPlane
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Metric Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations

/-- A half-ball punctured at its flat boundary center is connected. Its
star center lies strictly inside the positive half-space. -/
theorem punctured_planar_halfball_preconnected
    (c : Euc 2) (hc : c 0 = 0) (r : ℝ) (hr : 0 < r) :
    IsPreconnected ((ball c r ∩ {z : Euc 2 | 0 ≤ z 0}) \ {c}) := by
  let d : Euc 2 := c + EuclideanSpace.single 0 (r / 2)
  have hd0 : d 0 = r / 2 := by simp [d,hc,EuclideanSpace.single]
  have hdb : d ∈ ball c r := by
    rw [mem_ball,dist_eq_norm]
    simp only [d,add_sub_cancel_left]
    rw [EuclideanSpace.single,PiLp.norm_single,Real.norm_eq_abs,abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  have hd : d ∈ (ball c r ∩ {z : Euc 2 | 0 ≤ z 0}) \ {c} := by
    refine ⟨⟨hdb,by change 0 ≤ d 0; rw [hd0]; positivity⟩,?_⟩
    intro he
    have hh := congrArg (fun z : Euc 2 => z 0) he
    rw [hd0,hc] at hh
    linarith
  have hstar : StarConvex ℝ d ((ball c r ∩ {z : Euc 2 | 0 ≤ z 0}) \ {c}) := by
    intro y hy a b ha hb hab
    refine ⟨⟨(convex_ball c r) hdb hy.1.1 ha hb hab,?_⟩,?_⟩
    · change 0 ≤ a * d 0 + b * y 0
      exact add_nonneg (mul_nonneg ha (by rw [hd0]; positivity)) (mul_nonneg hb hy.1.2)
    · intro he
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simp only [ha0,hb1,zero_smul,one_smul,zero_add] at he
        exact hy.2 he
      · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hh := congrArg (fun z : Euc 2 => z 0) he
        change a * d 0 + b * y 0 = c 0 at hh
        rw [hd0,hc] at hh
        have hm : 0 ≤ b * y 0 := mul_nonneg hb hy.1.2
        have hp : 0 < a * (r / 2) := mul_pos hapos (half_pos hr)
        linarith
  exact (hstar.isPathConnected hd).isConnected.isPreconnected

/-- Half-space charts supply connected punctures even at boundary points. -/
theorem boundary_halfspace_punctured_chart_neighborhoods
    {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (EuclideanHalfSpace 2)) (x : X)
    (hx : x ∈ e.source) (hx0 : ((𝓡∂ 2) (e x)) 0 = 0) :
    ∀ V : Set X, IsOpen V → x ∈ V →
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ IsPreconnected (W \ {x}) := by
  intro V hV hxV
  let c : Euc 2 := (𝓡∂ 2) (e x)
  let O : Set (EuclideanHalfSpace 2) := e.target ∩ e.symm ⁻¹' V
  have hO : O ∈ 𝓝 (e x) := inter_mem (e.open_target.mem_nhds (e.map_source hx))
    ((e.symm.continuousAt (e.map_source hx)).preimage_mem_nhds
      (by simpa only [e.left_inv hx] using hV.mem_nhds hxV))
  have hpre : (𝓡∂ 2).symm ⁻¹' O ∈ 𝓝 c :=
    (𝓡∂ 2).continuous_symm.continuousAt.preimage_mem_nhds (by
      simpa only [c,ModelWithCorners.left_inv] using hO)
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hpre
  let W := e.source ∩ (fun y => (𝓡∂ 2) (e y)) ⁻¹' ball c r
  have hWo : IsOpen W := e.isOpen_inter_preimage
    (Metric.isOpen_ball.preimage (𝓡∂ 2).continuous)
  have hxW : x ∈ W := ⟨hx,mem_ball_self hr⟩
  have hWV : W ⊆ V := by
    intro y hy
    have ht := (hrsub hy.2).2
    change e.symm ((𝓡∂ 2).symm ((𝓡∂ 2) (e y))) ∈ V at ht
    rwa [ModelWithCorners.left_inv,e.left_inv hy.1] at ht
  let B := (ball c r ∩ {z : Euc 2 | 0 ≤ z 0}) \ {c}
  have hB : IsPreconnected B := punctured_planar_halfball_preconnected c hx0 r hr
  have htarget (y : Euc 2) (hy : y ∈ B) : (𝓡∂ 2).symm y ∈ e.target :=
    (hrsub hy.1.1).1
  have hyRange (y : Euc 2) (hy : y ∈ B) : y ∈ range (𝓡∂ 2) := by
    exact ⟨⟨y,hy.1.2⟩,rfl⟩
  have himage : (e.symm ∘ (𝓡∂ 2).symm) '' B = W \ {x} := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hzt := htarget z hz
      refine ⟨⟨e.map_target hzt,?_⟩,?_⟩
      · change (𝓡∂ 2) (e (e.symm ((𝓡∂ 2).symm z))) ∈ ball c r
        rw [e.right_inv hzt,(𝓡∂ 2).right_inv (hyRange z hz)]
        exact hz.1.1
      · intro he
        apply hz.2
        change z = c
        rw [← (𝓡∂ 2).right_inv (hyRange z hz),← e.right_inv hzt]
        exact congrArg (fun y => (𝓡∂ 2) (e y)) he
    · intro hy
      refine ⟨(𝓡∂ 2) (e y),⟨⟨hy.1.2,?_⟩,?_⟩,?_⟩
      · exact (e y).property
      · intro he
        exact hy.2 (e.injOn hy.1.1 hx ((𝓡∂ 2).injective he))
      · change e.symm ((𝓡∂ 2).symm ((𝓡∂ 2) (e y))) = y
        rw [ModelWithCorners.left_inv,e.left_inv hy.1.1]
  refine ⟨W,hWo,hxW,hWV,?_⟩
  rw [← himage]
  exact hB.image _ (e.symm.continuousOn.comp (𝓡∂ 2).continuous_symm.continuousOn htarget)

/-- Every actual boundary point of the auxiliary native source has
arbitrarily small connected punctured neighborhoods. -/
theorem native_boundary_punctured_neighborhoods
    (S : CompactOrientedSurface) (x : S) (hx : x ∈ S.boundary) :
    ∀ V : Set S, IsOpen V → x ∈ V →
      ∃ W : Set S, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ IsPreconnected (W \ {x}) := by
  apply boundary_halfspace_punctured_chart_neighborhoods
    (chartAt (EuclideanHalfSpace 2) x) x (mem_chart_source _ x)
  have hz := (ModelWithCorners.isBoundaryPoint_iff (I := 𝓡∂ 2)).mp hx
  rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hz
  change 0 = ((𝓡∂ 2) (chartAt (EuclideanHalfSpace 2) x x)) 0 at hz
  exact hz.symm

/-- Both interior and boundary source points have the punctured connectivity
needed for finite incident tangent limits. -/
theorem native_surface_punctured_neighborhoods
    (S : CompactOrientedSurface) (x : S) :
    ∀ V : Set S, IsOpen V → x ∈ V →
      ∃ W : Set S, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ IsPreconnected (W \ {x}) := by
  by_cases hx : x ∈ S.boundary
  · exact native_boundary_punctured_neighborhoods S x hx
  · exact native_interior_punctured_neighborhoods S x
      (((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mpr hx)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
