import CurveComplexGenusTwo.SphereGapFinish.ExteriorInversion
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import ClassificationJordanCurve.Arcs
import ClassificationJordanCurve.Main
import ClassificationJordanCurve.Brouwer
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Order.Iterate
namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
open CurveComplex Set Filter Metric _root_.Topology
open Schoenflies CurveComplex.SphereGapFinish

theorem proper_line_inversion_isJordanCurve (F : C(ℝ, Schoenflies.Plane)) (hF : IsProperMap F)
    (hinj : Function.Injective F) (a : Schoenflies.Plane)
    (ha : a ∉ Set.range F) :
    Schoenflies.IsJordanCurve (insert a (Schoenflies.invert a '' Set.range F)) := by
  let q : OnePoint ℝ → Schoenflies.Plane :=
    invertAtInfinity a ∘ OnePoint.map F
  have hmap : Continuous (OnePoint.map F) := by
    apply OnePoint.continuous_map F.continuous
    simpa only [coclosedCompact_eq_cocompact] using
      (isProperMap_iff_tendsto_cocompact.mp hF).2
  have hq : Continuous q := by
    apply continuous_iff_continuousAt.mpr
    intro z
    cases z with
    | infty =>
      exact (invertAtInfinity_continuousAt_infty a).comp hmap.continuousAt
    | coe x =>
      apply OnePoint.continuousAt_coe.mpr
      change ContinuousAt (fun x : ℝ => Schoenflies.invert a (F x)) x
      exact (Schoenflies.continuousAt_invert (by
        intro h; exact ha ⟨x, h⟩)).comp F.continuous.continuousAt
  have hqi : Function.Injective q := by
    intro x y hxy
    cases x with
    | infty =>
      cases y with
      | infty => rfl
      | coe y =>
        change a = Schoenflies.invert a (F y) at hxy
        exact False.elim (ha ⟨y, Schoenflies.invert_eq_center_iff.mp hxy.symm⟩)
    | coe x =>
      cases y with
      | infty =>
        change Schoenflies.invert a (F x) = a at hxy
        exact False.elim (ha ⟨x, Schoenflies.invert_eq_center_iff.mp hxy⟩)
      | coe y =>
        change Schoenflies.invert a (F x) = Schoenflies.invert a (F y) at hxy
        exact congrArg OnePoint.some (hinj (Schoenflies.invert_injective a hxy))
  let e : OnePoint ℝ ≃ₜ Circle :=
    (onePointEquivSphereOfFinrankEq (V := ℝ) (ι := Fin 2) (by simp)).trans
      ClassificationJordanCurve.Arcs.circleHomeoSphere.symm
  let r : C(Circle, Schoenflies.Plane) := ⟨q ∘ e.symm, hq.comp e.symm.continuous⟩
  have hr : IsEmbedding r := (r.continuous.isClosedEmbedding (hqi.comp e.symm.injective)).isEmbedding
  have hrange : Set.range r = insert a (Schoenflies.invert a '' Set.range F) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      change q (e.symm x) ∈ _
      generalize e.symm x = y
      cases y with
      | infty => exact Set.mem_insert a _
      | coe t => exact Set.mem_insert_of_mem _ ⟨F t, ⟨t, rfl⟩, rfl⟩
    · intro hz
      rcases hz with hz | ⟨w, ⟨t, rfl⟩, rfl⟩
      · subst z
        exact ⟨e OnePoint.infty, by simp [r, q, invertAtInfinity]⟩
      · exact ⟨e (OnePoint.some t), by simp [r, q, invertAtInfinity]⟩
  rw [← hrange]
  exact CurveComplex.isJordanCurve_range_of_isEmbedding_circle r hr

theorem proper_line_sides_of_inversion_jordan (L : Set Plane) (a : Plane) (ha : a ∉ L)
    (hJ : IsJordanCurve (insert a (invert a '' L))) :
    ∃ U V : Set Plane, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = Lᶜ ∧ frontier U = L ∧ frontier V = L := by
  let C := insert a (invert a '' L)
  have hsep : IsSeparating C := jordan_curve_theorem hJ
  have haC : a ∈ C := Set.mem_insert a _
  have hain : a ∉ inside C := fun h => h.1 haC
  have haout : a ∉ outside C := fun h => h.1 haC
  let U := invert a '' inside C
  let V := invert a '' outside C ∪ {a}
  have hUopen : IsOpen U := isOpen_invert_image hsep.isOpen_inside hain
  have houtc : outside C ⊆ ({a}ᶜ : Set Plane) := by
    intro z hz
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (show z ≠ a from fun h => haout (h ▸ hz))
  have hinc : inside C ⊆ ({a}ᶜ : Set Plane) := by
    intro z hz
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (show z ≠ a from fun h => hain (h ▸ hz))
  have hUconn : IsConnected U :=
    hsep.isConnected_inside.image _ ((continuousOn_invert a).mono hinc)
  obtain ⟨R, hR, hRout⟩ := exists_radius_compl_closedBall_subset_outside hsep a
  have hTopen : IsOpen (invert a '' outside C) :=
    isOpen_invert_image hsep.isOpen_outside haout
  have hVball : ball a R⁻¹ ⊆ V := by
    intro z hz
    rcases eq_or_ne z a with rfl | hza
    · exact Or.inr rfl
    · refine Or.inl ⟨invert a z, hRout ?_, invert_invert a z⟩
      have hpos : 0 < dist z a := dist_pos.2 hza
      rw [mem_compl_iff, mem_closedBall, dist_invert_center]
      exact not_le.2 (lt_inv_of_lt_inv₀ hpos (mem_ball.1 hz))
  have hVopen : IsOpen V := by
    have hrw : V = invert a '' outside C ∪ ball a R⁻¹ := by
      refine Subset.antisymm (union_subset subset_union_left ?_)
        (union_subset subset_union_left hVball)
      rintro z rfl
      exact Or.inr (mem_ball_self (by positivity))
    rw [hrw]
    exact hTopen.union isOpen_ball
  have hacl : a ∈ closure (invert a '' outside C) := by
    rw [Metric.mem_closure_iff]
    intro e he
    obtain ⟨z, hzout, hzfar⟩ : ∃ z ∈ outside C, e⁻¹ < dist z a := by
      by_contra hcon
      push Not at hcon
      exact hsep.not_isBounded_outside
        ((isBounded_iff_subset_closedBall a).2 ⟨e⁻¹, fun z hz => hcon z hz⟩)
    refine ⟨invert a z, ⟨z, hzout, rfl⟩, ?_⟩
    rw [dist_comm, dist_invert_center]
    exact inv_lt_of_inv_lt₀ he hzfar
  have hVconn : IsConnected V := by
    refine ⟨⟨a, Or.inr rfl⟩, ?_⟩
    exact (hsep.isConnected_outside.image _
      ((continuousOn_invert a).mono houtc)).isPreconnected.subset_closure subset_union_left
      (union_subset subset_closure (by rintro z rfl; exact hacl))
  have hdis : Disjoint U V := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ (⟨y, hy, he⟩ | he)
    · have he' := invert_injective a he
      exact Set.disjoint_left.mp disjoint_inside_outside hx (he' ▸ hy)
    · exact hain ((invert_eq_center_iff.mp he) ▸ hx)
  have hinv (z : Plane) : invert a z ∈ C ↔ z = a ∨ z ∈ L := by
    dsimp [C]
    simp only [mem_insert_iff, invert_eq_center_iff]
    rw [Set.mem_image]
    constructor
    · rintro (h | ⟨x, hx, he⟩)
      · exact Or.inl h
      · exact Or.inr ((invert_injective a he) ▸ hx)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨z, h, rfl⟩
  have hpart : U ∪ V = Lᶜ := by
    ext z
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | rfl)
      · intro hz
        have := (hinv (invert a x)).mpr (Or.inr hz)
        rw [invert_invert] at this
        exact hx.1 this
      · intro hz
        have := (hinv (invert a x)).mpr (Or.inr hz)
        rw [invert_invert] at this
        exact hx.1 this
      · exact ha
    · intro hz
      by_cases hza : z = a
      · exact Or.inr (Or.inr hza)
      · have hzC : invert a z ∉ C := by simpa [hinv, hza] using hz
        have hzside : invert a z ∈ inside C ∪ outside C := by
          rwa [inside_union_outside]
        rcases hzside with hu | hv
        · exact Or.inl ⟨invert a z, hu, invert_invert a z⟩
        · exact Or.inr (Or.inl ⟨invert a z, hv, invert_invert a z⟩)
  have hUL : Disjoint U L := by
    apply Set.disjoint_left.mpr
    intro x hx hL
    exact (show x ∈ Lᶜ from hpart ▸ Or.inl hx) hL
  have hVL : Disjoint V L := by
    apply Set.disjoint_left.mpr
    intro x hx hL
    exact (show x ∈ Lᶜ from hpart ▸ Or.inr hx) hL
  have hfrontU : frontier U = L := by
    apply Subset.antisymm
    · intro x hx
      by_contra hxL
      have hside : x ∈ U ∪ V := hpart.symm ▸ hxL
      rcases hside with hu | hv
      · exact (hUopen.frontier_eq ▸ hx).2 hu
      · exact Set.disjoint_right.mp (hdis.closure_left hVopen) hv (frontier_subset_closure hx)
    · intro x hx
      have hxa : x ≠ a := fun h => ha (h ▸ hx)
      have hixC : invert a x ∈ C := (hinv x).mpr (Or.inr hx)
      have hixcl : invert a x ∈ closure (inside C) := by
        rw [← hsep.frontier_inside] at hixC
        exact frontier_subset_closure hixC
      rw [hUopen.frontier_eq]
      refine ⟨?_, fun h => Set.disjoint_left.mp hUL h hx⟩
      simpa only [invert_invert] using
        mem_closure_image (continuousAt_invert (invert_ne_center hxa)) hixcl
  have hfrontV : frontier V = L := by
    apply Subset.antisymm
    · intro x hx
      by_contra hxL
      have hside : x ∈ U ∪ V := hpart.symm ▸ hxL
      rcases hside with hu | hv
      · exact Set.disjoint_left.mp (hdis.closure_right hUopen) hu (frontier_subset_closure hx)
      · exact (hVopen.frontier_eq ▸ hx).2 hv
    · intro x hx
      have hxa : x ≠ a := fun h => ha (h ▸ hx)
      have hixC : invert a x ∈ C := (hinv x).mpr (Or.inr hx)
      have hixcl : invert a x ∈ closure (outside C) := by
        rw [← hsep.frontier_outside] at hixC
        exact frontier_subset_closure hixC
      rw [hVopen.frontier_eq]
      refine ⟨?_, fun h => Set.disjoint_left.mp hVL h hx⟩
      apply closure_mono (show invert a '' outside C ⊆ V from subset_union_left)
      simpa only [invert_invert] using
        mem_closure_image (continuousAt_invert (invert_ne_center hxa)) hixcl
  exact ⟨U, V, hUopen, hVopen, hUconn, hVconn, hdis, hpart, hfrontU, hfrontV⟩

end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
