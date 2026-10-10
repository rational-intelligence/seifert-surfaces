import SectorPieces
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Metric Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations

theorem punctured_planar_ball_preconnected (c : Euc 2) (r : ℝ) (hr : 0 < r) :
    IsPreconnected (ball c r \ {c}) := by
  let H : OpenPartialHomeomorph (Euc 2) (Euc 2) := OpenPartialHomeomorph.univBall c r
  have hsource : H.source = univ := OpenPartialHomeomorph.univBall_source c r
  have htarget : H.target = ball c r := OpenPartialHomeomorph.univBall_target c hr
  have hH0 : H 0 = c := OpenPartialHomeomorph.univBall_apply_zero c r
  have hHc : Continuous H := OpenPartialHomeomorph.continuous_univBall c r
  have hdim : 1 < Module.rank ℝ (Euc 2) := by
    rw [← Module.finrank_eq_rank]
    norm_num [Euc]
  have hpre := (isPathConnected_compl_singleton_of_one_lt_rank hdim (0 : Euc 2)).isConnected.isPreconnected
  have he : H '' ({0}ᶜ : Set (Euc 2)) = ball c r \ {c} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨htarget ▸ H.map_source (hsource.symm ▸ mem_univ z), ?_⟩
      intro he
      have heq : H z = H 0 := he.trans hH0.symm
      exact hz (H.injOn (hsource.symm ▸ mem_univ z) (hsource.symm ▸ mem_univ 0) heq)
    · intro hy
      have hyt : y ∈ H.target := htarget.symm ▸ hy.1
      refine ⟨H.symm y, ?_, H.right_inv hyt⟩
      intro he
      apply hy.2
      change y = c
      rw [← H.right_inv hyt, he, hH0]
  rw [← he]
  exact hpre.image H hHc.continuousOn

theorem center_mem_closure_punctured_planar_ball (c : Euc 2) (r : ℝ) (hr : 0 < r) :
    c ∈ closure (ball c r \ {c}) := by
  apply mem_closure_iff_nhds.mpr
  intro V hV
  have hmeet : V ∩ ball c r ∈ 𝓝 c := inter_mem hV (ball_mem_nhds c hr)
  obtain ⟨y, hy, hyc⟩ := mem_closure_iff_nhds.mp (dense_compl_singleton c c) _ hmeet
  exact ⟨y, hy.1, hy.2, hyc⟩

/-- A plane chart supplies arbitrarily small connected punctured source
neighborhoods. This is purely topological and uses no smooth source map. -/
theorem punctured_chart_neighborhoods
    {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (Euc 2)) (x : X) (hx : x ∈ e.source) :
    ∀ V : Set X, IsOpen V → x ∈ V →
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ IsPreconnected (W \ {x}) := by
  intro V hV hxV
  have htarget := e.map_source hx
  have hgood : e.target ∩ e.symm ⁻¹' V ∈ 𝓝 (e x) :=
    inter_mem (e.open_target.mem_nhds htarget)
      ((e.symm.continuousAt htarget).preimage_mem_nhds
        (by simpa only [e.left_inv hx] using hV.mem_nhds hxV))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hgood
  let W := e.source ∩ e ⁻¹' ball (e x) r
  have hWo : IsOpen W := e.isOpen_inter_preimage Metric.isOpen_ball
  have hxW : x ∈ W := ⟨hx, mem_ball_self hr⟩
  have hWV : W ⊆ V := by
    intro y hy
    have he := (hsub hy.2).2
    change e.symm (e y) ∈ V at he
    rwa [e.left_inv hy.1] at he
  have he : e.symm '' (ball (e x) r \ {e x}) = W \ {x} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzt : z ∈ e.target := (hsub hz.1).1
      refine ⟨⟨e.map_target hzt, ?_⟩, ?_⟩
      · change e (e.symm z) ∈ ball (e x) r
        simpa only [e.right_inv hzt] using hz.1
      · intro heq
        apply hz.2
        change z = e x
        rw [← e.right_inv hzt, heq]
    · intro hy
      refine ⟨e y, ⟨hy.1.2, ?_⟩, e.left_inv hy.1.1⟩
      intro heq
      exact hy.2 (e.injOn hy.1.1 hx heq)
  refine ⟨W, hWo, hxW, hWV, ?_⟩
  rw [← he]
  exact (punctured_planar_ball_preconnected (e x) r hr).image e.symm
    (e.symm.continuousOn.mono (fun z hz => (hsub hz.1).1))

/-- The auxiliary smooth surface is used here only for its native topology:
every interior point has arbitrarily small connected punctured neighborhoods. -/
theorem native_interior_punctured_neighborhoods
    (S : CompactOrientedSurface) (x : S) (hx : x ∈ (𝓡∂ 2).interior S) :
    ∀ V : Set S, IsOpen V → x ∈ V →
      ∃ W : Set S, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ IsPreconnected (W \ {x}) := by
  let c := extChartAt (𝓡∂ 2) x
  let e : OpenPartialHomeomorph S (Euc 2) := {
    toFun := c
    invFun := c.symm
    source := c.source ∩ c ⁻¹' interior c.target
    target := interior c.target
    map_source' := fun _ h => h.2
    map_target' := by
      intro y hy
      refine ⟨c.map_target (interior_subset hy), ?_⟩
      change c (c.symm y) ∈ interior c.target
      rw [c.right_inv (interior_subset hy)]
      exact hy
    left_inv' := fun _ h => c.left_inv h.1
    right_inv' := fun _ h => c.right_inv (interior_subset h)
    open_source := isOpen_extChartAt_preimage' x isOpen_interior
    open_target := isOpen_interior
    continuousOn_toFun := (continuousOn_extChartAt x).mono inter_subset_left
    continuousOn_invFun := (continuousOn_extChartAt_symm x).mono interior_subset }
  apply punctured_chart_neighborhoods e x
  exact ⟨mem_extChartAt_source x, (ModelWithCorners.isInteriorPoint_iff).mp hx⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
