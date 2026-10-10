import Schoenflies.JordanClosed
import Mathlib
open Set Schoenflies Bornology

theorem vertical_translate_inside_pairwise (C U V : Set Plane) (T : ℝ) (hd : Disjoint U V)
    (hnest : (Homeomorph.addRight (Plane.mk 0 T)) '' U ⊆ U)
    (hinside : inside C ⊆ U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V)
    (hWperiod : ∀ n : ℤ, (fun z : Plane => z+Plane.mk ((n:ℝ)*T) 0) ''
      (U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V)=
      U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V)
    (hrow : Pairwise (fun i j : ℤ => Disjoint
      (inside ((fun z : Plane => z+Plane.mk ((i:ℝ)*T) 0) '' C))
      (inside ((fun z : Plane => z+Plane.mk ((j:ℝ)*T) 0) '' C)))) :
    Pairwise (fun i j : ℤ × ℤ => Disjoint
      (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' C))
      (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) '' C))) := by
  have transport (e : Plane ≃ₜ Plane) (C : Set Plane) :
      e '' inside C = inside (e '' C) ∧
        e '' closure (inside C) = closure (inside (e '' C)) := by
    have boundedImage (f : Plane ≃ₜ Plane) {S : Set Plane} (hS : IsBounded S) :
        IsBounded (f '' S) :=
      (hS.isCompact_closure.image f.continuous).isBounded.subset (image_mono subset_closure)
    have boundedIff (S : Set Plane) : IsBounded (e '' S) ↔ IsBounded S := by
      constructor
      · intro h
        have hh := boundedImage e.symm h
        simpa only [← image_comp,e.symm_comp_self,image_id] using hh
      · exact boundedImage e
    have memIff (x : Plane) : e x ∈ inside (e '' C) ↔ x ∈ inside C := by
      by_cases hx : x ∈ C
      · have hex : e x ∈ e '' C := mem_image_of_mem e hx
        simp only [mem_inside_iff]
        exact ⟨fun h => False.elim (h.1 hex),fun h => False.elim (h.1 hx)⟩
      · have hex : e x ∉ e '' C := by
          rintro ⟨y,hy,he⟩
          exact hx (e.injective he ▸ hy)
        have hc := e.image_connectedComponentIn (s := Cᶜ) (x := x) hx
        rw [e.image_compl] at hc
        simp only [mem_inside_iff,hx,hex,not_false_eq_true,true_and]
        rw [← hc]
        exact boundedIff _
    have him : e '' inside C = inside (e '' C) := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact (memIff x).mpr hx
      · intro hz
        refine ⟨e.symm z,?_,e.apply_symm_apply z⟩
        exact (memIff _).mp (by simpa only [e.apply_symm_apply] using hz)
    exact ⟨him,by rw [e.image_closure,him]⟩
  have bandDisjoint (U V : Set Plane) (T : ℝ) (hd : Disjoint U V)
      (hnest : (Homeomorph.addRight (Plane.mk 0 T)) '' U ⊆ U) :
      let H : ℤ → Plane ≃ₜ Plane := fun n => Homeomorph.addRight (Plane.mk 0 ((n:ℝ)*T))
      let W := U ∩ H 1 '' V
      Pairwise (fun i j : ℤ => Disjoint (H i '' W) (H j '' W)) := by
    dsimp only
    let H : ℤ → Plane ≃ₜ Plane := fun n => Homeomorph.addRight (Plane.mk 0 ((n:ℝ)*T))
    let W := U ∩ H 1 '' V
    have comp (i j : ℤ) (S : Set Plane) : H (i+j) '' S=H i '' (H j '' S) := by
      rw [← image_comp]
      congr 1
      funext z
      ext k
      fin_cases k <;> simp [H,Plane.mk,Int.cast_add] <;> ring
    have zero (S : Set Plane) : H 0 '' S=S := by
      have he : (H 0 : Plane → Plane)=id := by
        funext z
        ext k
        fin_cases k <;> simp [H,Plane.mk]
      rw [he,image_id]
    have downNat (n : ℕ) : H (n:ℤ) '' U ⊆ U := by
      induction n with
      | zero => rw [Nat.cast_zero,zero]
      | succ n ih =>
        rw [Nat.cast_succ,comp]
        exact (image_mono (show H 1 '' U ⊆ U by simpa [H] using hnest)).trans ih
    have down (n : ℤ) (hn : 0 ≤ n) : H n '' U ⊆ U := by
      have hh := downNat n.toNat
      simpa only [Int.toNat_of_nonneg hn] using hh
    have mono (i j : ℤ) (hij : i ≤ j) : H j '' U ⊆ H i '' U := by
      have hj : j=i+(j-i) := by omega
      rw [hj,comp]
      exact image_mono (down (j-i) (by omega))
    have ordered (i j : ℤ) (hij : i < j) : Disjoint (H i '' W) (H j '' W) := by
      apply disjoint_left.mpr
      intro z hi hj
      have hiV : z ∈ H (i+1) '' V := by
        rw [comp]
        exact image_mono inter_subset_right hi
      have hjU : z ∈ H j '' U := image_mono inter_subset_left hj
      have hiU : z ∈ H (i+1) '' U := mono (i+1) j (by omega) hjU
      obtain ⟨u,hu,he⟩ := hiU
      obtain ⟨v,hv,hvEq⟩ := hiV
      have huv : v=u := (H (i+1)).injective (hvEq.trans he.symm)
      exact disjoint_left.1 hd hu (huv ▸ hv)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact ordered i j h
    · exact (ordered j i h).symm
  let X : ℤ → Plane ≃ₜ Plane := fun n => Homeomorph.addRight (Plane.mk ((n:ℝ)*T) 0)
  let Y : ℤ → Plane ≃ₜ Plane := fun n => Homeomorph.addRight (Plane.mk 0 ((n:ℝ)*T))
  let Z : ℤ × ℤ → Plane ≃ₜ Plane := fun i => Homeomorph.addRight (Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))
  let W := U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V
  have form (i : ℤ × ℤ) : inside (Z i '' C)=Y i.2 '' inside (X i.1 '' C) := by
    rw [← (transport (Z i) C).1,← (transport (X i.1) C).1,← image_comp]
    congr 1
    funext z
    ext k
    fin_cases k <;> simp [Z,Y,X,Plane.mk]
  have rowIn (n : ℤ) : inside (X n '' C) ⊆ W := by
    rw [← (transport (X n) C).1]
    have hh := image_mono hinside (f := X n)
    change X n '' inside C ⊆ X n '' W at hh
    rw [show X n '' W=W from hWperiod n] at hh
    exact hh
  have bands : Pairwise (fun i j : ℤ => Disjoint (Y i '' W) (Y j '' W)) := by
    simpa [Y,W] using bandDisjoint U V T hd hnest
  intro i j hij
  change Disjoint (inside (Z i '' C)) (inside (Z j '' C))
  rw [form,form]
  by_cases hm : i.2=j.2
  · have hn : i.1 ≠ j.1 := by
      intro hh
      exact hij (Prod.ext hh hm)
    have hr : Disjoint (inside (X i.1 '' C)) (inside (X j.1 '' C)) := hrow hn
    rw [hm]
    apply disjoint_left.mpr
    rintro z ⟨a,ha,he⟩ ⟨b,hb,hbe⟩
    have hbEq : b=a := (Y j.2).injective (hbe.trans he.symm)
    exact disjoint_left.1 hr ha (hbEq ▸ hb)
  · exact (bands hm).mono (image_mono (rowIn i.1)) (image_mono (rowIn j.1))

#print axioms vertical_translate_inside_pairwise
