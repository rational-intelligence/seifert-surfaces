import Schoenflies.JordanClosed
import Mathlib

open Set Bornology Schoenflies

theorem jordan_inside_contained_in_proper_line_side {C L U V : Set Plane} (hC : IsJordanCurve C)
    (hU : IsOpen U) (hV : IsOpen V) (hVconn : IsConnected V)
    (hd : Disjoint U V) (hpart : U ∪ V = Lᶜ)
    (hfront : frontier V = L) (hVunbounded : ¬ IsBounded V)
    (hCside : C ⊆ U ∪ L) :
    inside C ⊆ U := by
  have hsep := jordan_curve_theorem hC
  have hVL : Disjoint V L := by
    apply disjoint_left.mpr
    intro x hx hxl
    exact (show x ∈ Lᶜ from hpart ▸ Or.inr hx) hxl
  have hVC : V ⊆ Cᶜ := by
    intro x hx hxc
    rcases hCside hxc with hxU | hxL
    · exact disjoint_left.mp hd hxU hx
    · exact disjoint_left.mp hVL hx hxL
  have hout : V ⊆ outside C := by
    have hregions : V ⊆ inside C ∪ outside C := by
      rw [inside_union_outside]
      exact hVC
    rcases hVconn.isPreconnected.subset_or_subset hsep.isOpen_inside hsep.isOpen_outside
        disjoint_inside_outside hregions with h | h
    · exact False.elim (hVunbounded (hsep.isBounded_inside.subset h))
    · exact h
  intro x hx
  have hxV : x ∉ V := fun hv => disjoint_left.mp disjoint_inside_outside hx (hout hv)
  have hxL : x ∉ L := by
    intro hxl
    have hxcl : x ∈ closure V := frontier_subset_closure (hfront.symm ▸ hxl)
    obtain ⟨y, hyin, hyV⟩ :=
      Set.Nonempty.of_closure ⟨x, hsep.isOpen_inside.inter_closure ⟨hx, hxcl⟩⟩
    exact disjoint_left.mp disjoint_inside_outside hyin (hout hyV)
  have hxside : x ∈ U ∪ V := hpart.symm ▸ hxL
  exact hxside.resolve_right hxV


#print axioms jordan_inside_contained_in_proper_line_side
