import CurveComplexGenusTwo.Topology.CrosscutIsotopy
import CurveComplexGenusTwo.Topology.ChartLift
import Schoenflies.ModelCurve
import Schoenflies.Topology
namespace CurveComplex
open Schoenflies
/-- Actual square-relative support, including points INSIDE the chart but
outside the selected repair disk; these are part of the unchanged remainder. -/
theorem position_crosscut_surface_square_support
    (S : Type*) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (U : Set S) (V : Set Plane) (hU : IsOpen U)
    (e : U ≃ₜ V) (hSquare : Plane.closedSquare 0 1 ⊆ V)
    (A B : Set Plane) (a b : Plane)
    (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
    (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
    (hAi : A \ {a, b} ⊆ Plane.openSquare 0 1)
    (hBi : B \ {a, b} ⊆ Plane.openSquare 0 1) :
    ∃ G : AmbientIsotopy S,
      G.finalMap '' {x : S | ∃ u : U, u.val = x ∧ (e u : Plane) ∈ A} =
        {x : S | ∃ u : U, u.val = x ∧ (e u : Plane) ∈ B} ∧
      ∀ t x, x ∉ {x : S | ∃ u : U, u.val = x ∧
        (e u : Plane) ∈ Plane.openSquare 0 1} → G.map (t, x) = x := by
  obtain ⟨R, H, hR, hHA, hHball, hHsq⟩ :=
    position_crosscut_supported_isotopy A B a b hA hB ha hb hAi hBi
  have hC : IsCompact (Plane.closedSquare 0 1) := isCompact_closedSquare 0 1
  have hfix : ∀ t x, x ∉ Plane.closedSquare 0 1 → H.map (t, x) = x := by
    intro t x hx
    apply hHsq
    intro hxs
    exact hx (mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hxs).le)
  obtain ⟨K, G, hcoord, hGU, hGfix⟩ :=
    position_surface_chart_lift S U V hU e (Plane.closedSquare 0 1) hC hSquare H hfix
  have hfixSquare : ∀ t x, x ∉ {x : S | ∃ u : U, u.val = x ∧
      (e u : Plane) ∈ Plane.openSquare 0 1} → G.map (t, x) = x := by
    intro t x hx
    by_cases hxU : x ∈ U
    · let u : U := ⟨x, hxU⟩
      have huSq : (e u : Plane) ∉ Plane.openSquare 0 1 := by
        intro hu
        exact hx ⟨u, rfl, hu⟩
      have hKu : K.map (t, u) = u := by
        apply e.injective
        apply Subtype.ext
        exact (hcoord t u).trans (hHsq t (e u) huSq)
      rw [hGU t u, hKu]
    · exact hGfix t x hxU
  refine ⟨G, ?_, hfixSquare⟩
  ext y
  constructor
  · rintro ⟨x, ⟨u, rfl, huA⟩, hy⟩
    refine ⟨K.finalMap u, ?_, ?_⟩
    · exact (hGU (⟨1, by norm_num⟩ : Interval) u).symm.trans hy
    · have h := hcoord (⟨1, by norm_num⟩ : Interval) u
      change (e (K.finalMap u) : Plane) = H.finalMap (e u : Plane) at h
      rw [h]
      exact hHA ▸ ⟨(e u : Plane), huA, rfl⟩
  · rintro ⟨v, hv, hvB⟩
    have hzB : (e v : Plane) ∈ H.finalMap '' A := hHA.symm ▸ hvB
    obtain ⟨z, hzA, hz⟩ := hzB
    have hzV : z ∈ V := hSquare (crosscut_subset_closedSquare ha hb hAi hzA)
    let u : U := e.symm ⟨z, hzV⟩
    have heu : (e u : Plane) = z := congrArg Subtype.val (e.apply_symm_apply ⟨z, hzV⟩)
    have hKu : K.finalMap u = v := by
      apply e.injective
      apply Subtype.ext
      have h := hcoord (⟨1, by norm_num⟩ : Interval) u
      change (e (K.finalMap u) : Plane) = H.finalMap (e u : Plane) at h
      rw [heu, hz] at h
      exact h
    refine ⟨u.val, ⟨u, rfl, ?_⟩, ?_⟩
    · rw [heu]
      exact hzA
    · change G.map ((⟨1, by norm_num⟩ : Interval), u.val) = y
      rw [hGU (⟨1, by norm_num⟩ : Interval) u]
      change (K.finalMap u : S) = y
      rw [hKu]
      exact hv


end CurveComplex
