import CurveComplexGenusTwo.CWHurewicz.CWBasic
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.TietzeExtension

namespace CurveComplexGenusTwo.CWHurewicz
open Topology Metric Set
open scoped ContDiff unitInterval

/-- Genuine point avoidance: smooth approximation followed by a small
translation outside its lower-dimensional range. -/
theorem exists_ne_zero_approx
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (f : C(E,F)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : C(E,F), (∀ x, g x ≠ 0) ∧ ∀ x, dist (g x) (f x) < ε := by
  obtain ⟨g,hg,hgf,_⟩ := f.continuous.exists_contDiff_approx 1
    (continuous_const : Continuous (fun _ : E => ε/2)) (fun _ => half_pos hε)
  have hd := (hg.differentiable (by norm_num)).dense_compl_range_of_finrank_lt_finrank hdim
  obtain ⟨y,hy,hyn⟩ := Metric.mem_closure_iff.mp (hd (0 : F)) (ε/2) (half_pos hε)
  refine ⟨⟨fun x => g x - y, hg.continuous.sub continuous_const⟩, ?_, ?_⟩
  · intro x he
    have hxy : g x = y := sub_eq_zero.mp he
    exact hy ⟨x,hxy⟩
  · intro x
    calc
      dist (g x - y) (f x) ≤ dist (g x - y) (g x) + dist (g x) (f x) := dist_triangle _ _ _
      _ < ε/2 + ε/2 := add_lt_add (by simpa [dist_eq_norm] using hyn) (hgf x)
      _ = ε := by ring

private def centerCutoff (r : ℝ) : ℝ := max 0 (min 1 (2 - 4*r))

private theorem centerCutoff_bounds (r : ℝ) :
    0 ≤ centerCutoff r ∧ centerCutoff r ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

private theorem centerCutoff_one {r : ℝ} (hr : r ≤ 1/4) : centerCutoff r = 1 := by
  simp only [centerCutoff]
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

private theorem centerCutoff_zero {r : ℝ} (hr : 1/2 ≤ r) : centerCutoff r = 0 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

/-- Localized center avoidance. It fixes the original map wherever its norm
is at least one half, so it is suited to gluing inside an open cell. -/
theorem exists_ne_zero_approx_fixed_outside_half
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F) (f : C(E,F)) :
    ∃ g : C(E,F), (∀ x, g x ≠ 0) ∧
      (∀ x, dist (g x) (f x) < 1/8) ∧
      (∀ x, 1/2 ≤ ‖f x‖ → g x = f x) := by
  obtain ⟨u,hu,huf⟩ := exists_ne_zero_approx hdim f (1/8) (by norm_num)
  let g : C(E,F) := ⟨fun x => f x + centerCutoff ‖f x‖ • (u x - f x), by
    unfold centerCutoff
    fun_prop⟩
  have hdist (x : E) : dist (g x) (f x) < 1/8 := by
    rw [dist_eq_norm]
    change ‖f x + centerCutoff ‖f x‖ • (u x-f x) - f x‖ < 1/8
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (centerCutoff_bounds _).1]
    have hn : ‖u x-f x‖ < 1/8 := by simpa only [dist_eq_norm] using huf x
    exact (mul_le_of_le_one_left (norm_nonneg _) (centerCutoff_bounds _).2).trans_lt hn
  refine ⟨g, ?_, hdist, ?_⟩
  · intro x hx
    by_cases hfx : ‖f x‖ ≤ 1/4
    · have hg : g x = u x := by
        change f x + centerCutoff ‖f x‖ • (u x-f x) = u x
        rw [centerCutoff_one hfx, one_smul]
        abel
      exact hu x (hg.symm.trans hx)
    · have hh := hdist x
      rw [hx, dist_zero_left] at hh
      linarith
  · intro x hx
    change f x + centerCutoff ‖f x‖ • (u x-f x) = f x
    rw [centerCutoff_zero hx, zero_smul, add_zero]

/-- Point avoidance on an arbitrary closed subset of a lower-dimensional
coordinate space. Tietze extension is constructed before smooth approximation. -/
theorem closedSubset_centerAvoidance {k n : ℕ} (hkn : k < n)
    (S : Set (Fin k → ℝ)) (hS : IsClosed S) (f : C(S, Fin n → ℝ)) :
    ∃ g : C(S, Fin n → ℝ), (∀ x, g x ≠ 0) ∧
      (∀ x, dist (g x) (f x) < 1/8) ∧
      (∀ x, 1/2 ≤ ‖f x‖ → g x = f x) := by
  obtain ⟨e,he⟩ := f.exists_restrict_eq hS
  have hev (x : S) : e x.val = f x := congrArg (fun q : C(S, Fin n → ℝ) => q x) he
  obtain ⟨g,hg,hgf,hfix⟩ := exists_ne_zero_approx_fixed_outside_half
    (by simpa only [Module.finrank_fin_fun] using hkn) e
  refine ⟨g.restrict S, fun x => hg x.val, ?_, ?_⟩
  · intro x
    simpa only [ContinuousMap.restrict_apply, hev x] using hgf x.val
  · intro x hx
    have h := hfix x.val (by rwa [hev x])
    simpa only [ContinuousMap.restrict_apply, hev x] using h

/-- A closed characteristic disk admits center avoidance in larger target
dimension, relative to the full inverse image of the outer half-annulus. -/
theorem cellDisk_centerAvoidance {k n : ℕ} (hkn : k < n)
    (f : C(CellDisk k, CellDisk n)) :
    ∃ g : C(CellDisk k, CellDisk n), (∀ z, (g z).val ≠ 0) ∧
      Nonempty (ContinuousMap.HomotopyRel f g {z | 1/2 ≤ ‖(f z).val‖}) := by
  let fv : C(CellDisk k, Fin n → ℝ) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(CellDisk n, Fin n → ℝ)).comp f
  obtain ⟨v,hv,hvf,hfix⟩ := closedSubset_centerAvoidance hkn
    (closedBall (0 : Fin k → ℝ) 1) isClosed_closedBall fv
  have hvball (z : CellDisk k) : v z ∈ closedBall (0 : Fin n → ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hz : 1/2 ≤ ‖fv z‖
    · rw [hfix z hz]
      exact (mem_closedBall_zero_iff).mp (f z).property
    · have hdist : ‖v z - fv z‖ < 1/8 := by simpa only [dist_eq_norm] using hvf z
      have hn := norm_add_le (v z - fv z) (fv z)
      rw [sub_add_cancel] at hn
      have hlt : ‖fv z‖ < 1/2 := lt_of_not_ge hz
      linarith
  let g : C(CellDisk k, CellDisk n) := ⟨fun z => ⟨v z,hvball z⟩, v.continuous.subtype_mk _⟩
  refine ⟨g, hv, ⟨{
    toFun := fun p => ⟨(1-(p.1 : ℝ)) • (f p.2).val + (p.1 : ℝ) • (g p.2).val,
      (convex_closedBall (0 : Fin n → ℝ) (1 : ℝ)) (f p.2).property (g p.2).property
        (sub_nonneg.mpr p.1.property.2) p.1.property.1 (by ring)⟩
    continuous_toFun := by fun_prop
    map_zero_left := fun z => by apply Subtype.ext; simp
    map_one_left := fun z => by apply Subtype.ext; simp
    prop' := fun t z hz => by
      apply Subtype.ext
      change (1-(t : ℝ)) • (f z).val + (t : ℝ) • v z = (f z).val
      rw [hfix z hz]
      change (1-(t : ℝ)) • (f z).val + (t : ℝ) • (f z).val = (f z).val
      rw [← add_smul]
      simp }⟩⟩

/-- The same actual approximation for any closed-embedded domain, allowing
a closed chart preimage inside a disk to be used without flattening subtypes. -/
theorem closedEmbedding_centerAvoidance {k n : ℕ} (hkn : k < n)
    {S : Type*} [TopologicalSpace S] (e : S → (Fin k → ℝ))
    (he : IsClosedEmbedding e) (f : C(S, Fin n → ℝ)) :
    ∃ g : C(S, Fin n → ℝ), (∀ x, g x ≠ 0) ∧
      (∀ x, dist (g x) (f x) < 1/8) ∧
      (∀ x, 1/2 ≤ ‖f x‖ → g x = f x) := by
  obtain ⟨v,hv⟩ := f.exists_extension he
  have hve (x : S) : v (e x) = f x := congrArg (fun q : C(S, Fin n → ℝ) => q x) hv
  obtain ⟨g,hg,hgf,hfix⟩ := exists_ne_zero_approx_fixed_outside_half
    (by simpa only [Module.finrank_fin_fun] using hkn) v
  refine ⟨g.comp ⟨e,he.continuous⟩, fun x => hg (e x), ?_, ?_⟩
  · intro x
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hve x] using hgf (e x)
  · intro x hx
    have h := hfix (e x) (by rwa [hve x])
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hve x] using h

end CurveComplexGenusTwo.CWHurewicz
