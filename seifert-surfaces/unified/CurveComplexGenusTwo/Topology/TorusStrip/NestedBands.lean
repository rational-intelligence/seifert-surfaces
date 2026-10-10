import CurveComplexGenusTwo.Topology.TorusStrip.ProperLineSeparationCore
import ClassificationJordanCurve.Main
import ClassificationJordanCurve.Brouwer
import CurveComplexGenusTwo.Topology.TorusStrip.VerticalTranslateInsidePairwise
import CurveComplexGenusTwo.Topology.TorusStrip.JordanSideContainment
import Mathlib

open Set Metric Schoenflies Bornology _root_.Topology
open CurveComplexGenusTwo.Topology.PuncturedTorusCandidate

theorem normalized_line_ordered_sides (G : C(ℝ, Plane)) (hG : IsClosedEmbedding G)
    (T : ℝ) (hT : 0 < T)
    (hp : ∀ (n : ℤ) x, G (x + (n : ℝ) * T) = G x + Plane.mk ((n : ℝ) * T) 0)
    (hdis : Disjoint (range G) ((Homeomorph.addRight (Plane.mk 0 T)) '' range G)) :
    ∃ U V : Set Plane, ∃ B : ℝ,
      0 < B ∧ IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (range G)ᶜ ∧
      frontier U = range G ∧ frontier V = range G ∧
      {z : Plane | B < z 1} ⊆ U ∧ {z : Plane | z 1 < -B} ⊆ V ∧
      let e := Homeomorph.addRight (Plane.mk 0 T)
      e '' U ⊂ U ∧ e '' range G ⊆ U ∧ range G ⊆ e '' V := by
  have sides (F : C(ℝ, Plane)) (hF : IsProperMap F) (hinj : Function.Injective F)
      (B : ℝ) (hB : 0 < B) (hbound : ∀ x : ℝ, |F x 1| < B)
      (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0) :
      ∃ U V : Set Plane,
        IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
        Disjoint U V ∧ U ∪ V = (range F)ᶜ ∧
        frontier U = range F ∧ frontier V = range F ∧
        {z : Plane | B < z 1} ⊆ U ∧ {z : Plane | z 1 < -B} ⊆ V := by
    have nocross (F : C(ℝ, Plane)) (B : ℝ) (hB : 0 < B)
        (hbound : ∀ x : ℝ, |F x 1| < B)
        (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0)
        (u w : Plane) (hu : u 1 ≤ -B) (hw : B ≤ w 1) :
        ¬ JoinedIn (Set.range F)ᶜ u w := by
      have crossing_strip {a b c d : ℝ} (hab : a < b) (hcd : c < d)
          (h v : ℝ → Plane)
          (hh : ContinuousOn h (Icc (-1) 1)) (hv : ContinuousOn v (Icc (-1) 1))
          (hhY : ∀ t ∈ Icc (-1 : ℝ) 1, c < h t 1 ∧ h t 1 < d)
          (hvX : ∀ t ∈ Icc (-1 : ℝ) 1, a < v t 0 ∧ v t 0 < b)
          (hh1 : h (-1) 0 ≤ a) (hh2 : b ≤ h 1 0)
          (hv1 : v (-1) 1 ≤ c) (hv2 : d ≤ v 1 1) :
          ∃ s ∈ Icc (-1 : ℝ) 1, ∃ t ∈ Icc (-1 : ℝ) 1, h s = v t := by
        let H : ℝ → Plane := fun s => !₂[max a (min b (h s 0)), h s 1]
        let V : ℝ → Plane := fun t => !₂[v t 0, max c (min d (v t 1))]
        have hH : ContinuousOn H (Icc (-1) 1) := by
          apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
          apply continuousOn_pi.mpr
          intro i
          fin_cases i
          · exact (show Continuous (fun x : ℝ => max a (min b x)) by fun_prop).comp_continuousOn
              ((EuclideanSpace.proj 0).continuous.comp_continuousOn hh)
          · exact (EuclideanSpace.proj 1).continuous.comp_continuousOn hh
        have hV : ContinuousOn V (Icc (-1) 1) := by
          apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
          apply continuousOn_pi.mpr
          intro i
          fin_cases i
          · exact (EuclideanSpace.proj 0).continuous.comp_continuousOn hv
          · exact (show Continuous (fun x : ℝ => max c (min d x)) by fun_prop).comp_continuousOn
              ((EuclideanSpace.proj 1).continuous.comp_continuousOn hv)
        have hHE (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
            H t 0 ∈ Icc a b ∧ H t 1 ∈ Icc c d := by
          exact ⟨⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩, (hhY t ht).1.le, (hhY t ht).2.le⟩
        have hVE (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
            V t 0 ∈ Icc a b ∧ V t 1 ∈ Icc c d := by
          exact ⟨⟨(hvX t ht).1.le, (hvX t ht).2.le⟩, le_max_left _ _, max_le hcd.le (min_le_left _ _)⟩
        have hH1 : H (-1) 0 = a := by
          dsimp [H]
          rw [min_eq_right (hh1.trans hab.le), max_eq_left hh1]
        have hH2 : H 1 0 = b := by
          dsimp [H]
          rw [min_eq_left hh2, max_eq_right hab.le]
        have hV1 : V (-1) 1 = c := by
          dsimp [V]
          rw [min_eq_right (hv1.trans hcd.le), max_eq_left hv1]
        have hV2 : V 1 1 = d := by
          dsimp [V]
          rw [min_eq_left hv2, max_eq_right hcd.le]
        obtain ⟨s, hs, t, ht, he⟩ := ClassificationJordanCurve.crossing ClassificationJordanCurve.Brouwer.brouwerFPT
          hab.le hcd.le H V hH hV hHE hVE hH1 hH2 hV1 hV2
        have clamp {l u x z : ℝ} (hlu : l < u) (hz : l < z ∧ z < u)
            (he : max l (min u x) = z) : x = z := by
          by_cases hx : x ≤ l
          · rw [min_eq_right (hx.trans hlu.le), max_eq_left hx] at he
            linarith [hz.1]
          · by_cases hxu : u ≤ x
            · rw [min_eq_left hxu, max_eq_right hlu.le] at he
              linarith [hz.2]
            · rwa [min_eq_right (le_of_not_ge hxu), max_eq_right (le_of_not_ge hx)] at he
        refine ⟨s, hs, t, ht, ?_⟩
        have he0 := congrArg (fun p : Plane => p 0) he
        have he1 := congrArg (fun p : Plane => p 1) he
        ext i
        fin_cases i
        · exact clamp hab (hvX t ht) he0
        · exact (clamp hcd (hhY s hs) he1.symm).symm
      intro hjoin
      obtain ⟨v, hv, hv0, hv1, hvmem⟩ := ClassificationJordanCurve.arc_path hjoin
      have hvc : ContinuousOn (fun t : ℝ => |v t 0|) (Icc (-1) 1) :=
        continuous_abs.comp_continuousOn ((EuclideanSpace.proj 0).continuous.comp_continuousOn hv)
      obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hvc).bddAbove
      let R := max M 0 + 1
      have hR : 0 < R := by dsimp [R]; positivity
      have hMv (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : |v t 0| < R := by
        have hm := hM (Set.mem_image_of_mem _ ht)
        dsimp [R]
        linarith [le_max_left M 0]
      obtain ⟨A, hA0, hA1⟩ := hends R
      let h : ℝ → Plane := fun s => F (A * s)
      have hhc : ContinuousOn h (Icc (-1) 1) :=
        (F.continuous.comp (by fun_prop : Continuous (fun s : ℝ => A * s))).continuousOn
      have hhY (t : ℝ) (_ht : t ∈ Icc (-1 : ℝ) 1) : -B < h t 1 ∧ h t 1 < B :=
        abs_lt.mp (hbound (A * t))
      have hvX (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : -R < v t 0 ∧ v t 0 < R :=
        abs_lt.mp (hMv t ht)
      have hh0 : h (-1) 0 ≤ -R := by simpa [h] using hA0.le
      have hh1 : R ≤ h 1 0 := by simpa [h] using hA1.le
      have hv0' : v (-1) 1 ≤ -B := by simpa [hv0] using hu
      have hv1' : B ≤ v 1 1 := by simpa [hv1] using hw
      obtain ⟨s, hs, t, ht, he⟩ := crossing_strip (by linarith : -R < R)
        (by linarith : -B < B) h v hhc hv hhY hvX hh0 hh1 hv0' hv1'
      exact hvmem t ht ⟨A * s, he⟩
    have orient {X : Type} [TopologicalSpace X] [LocallyPathConnectedSpace X]
        (L U V A B : Set X)
        (hU : IsOpen U) (hV : IsOpen V) (hcU : IsConnected U) (hcV : IsConnected V)
        (hd : Disjoint U V) (hpart : U ∪ V = Lᶜ)
        (hA : IsConnected A) (hB : IsConnected B) (hAL : A ⊆ Lᶜ) (hBL : B ⊆ Lᶜ)
        (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ JoinedIn Lᶜ a b) :
        (A ⊆ U ∧ B ⊆ V) ∨ (A ⊆ V ∧ B ⊆ U) := by
      have hAs : A ⊆ U ∪ V := hpart.symm ▸ hAL
      have hBs : B ⊆ U ∪ V := hpart.symm ▸ hBL
      have hUL : U ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inl hx
      have hVL : V ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inr hx
      obtain ⟨a, ha⟩ := hA.nonempty
      obtain ⟨b, hb⟩ := hB.nonempty
      rcases hA.isPreconnected.subset_or_subset hU hV hd hAs with hAU | hAV
      · rcases hB.isPreconnected.subset_or_subset hU hV hd hBs with hBU | hBV
        · exact False.elim (hno a ha b hb
            (((hU.isConnected_iff_isPathConnected.mp hcU).joinedIn a (hAU ha) b (hBU hb)).mono hUL))
        · exact Or.inl ⟨hAU, hBV⟩
      · rcases hB.isPreconnected.subset_or_subset hU hV hd hBs with hBU | hBV
        · exact Or.inr ⟨hAV, hBU⟩
        · exact False.elim (hno a ha b hb
            (((hV.isConnected_iff_isPathConnected.mp hcV).joinedIn a (hAV ha) b (hBV hb)).mono hVL))
  
    let L := Set.range F
    let A : Set Plane := {z | z 1 < -B}
    let D : Set Plane := {z | B < z 1}
    have hAn : A.Nonempty := ⟨!₂[0, -B - 1], by dsimp [A]; linarith⟩
    have hDn : D.Nonempty := ⟨!₂[0, B + 1], by dsimp [D]; linarith⟩
    have hAc : IsConnected A := by
      apply Convex.isConnected _ hAn
      exact (convex_Iio (-B)).is_linear_preimage (EuclideanSpace.proj (1 : Fin 2)).isLinear
    have hDc : IsConnected D := by
      apply Convex.isConnected _ hDn
      exact (convex_Ioi B).is_linear_preimage (EuclideanSpace.proj (1 : Fin 2)).isLinear
    have hAL : A ⊆ Lᶜ := by
      rintro z hz ⟨x, rfl⟩
      have hh := (abs_lt.mp (hbound x)).1
      exact (not_lt_of_ge hh.le) hz
    have hDL : D ⊆ Lᶜ := by
      rintro z hz ⟨x, rfl⟩
      have hh := (abs_lt.mp (hbound x)).2
      exact (not_lt_of_ge hh.le) hz
    obtain ⟨a, ha⟩ := hAn
    have hJ := proper_line_inversion_isJordanCurve F hF hinj a (hAL ha)
    obtain ⟨U, V, hU, hV, hcU, hcV, hd, hpart, hfU, hfV⟩ :=
      proper_line_sides_of_inversion_jordan L a (hAL ha) hJ
    have hno (a : Plane) (ha : a ∈ A) (b : Plane) (hb : b ∈ D) : ¬ JoinedIn Lᶜ a b :=
      nocross F B hB hbound hends a b ha.le hb.le
    rcases orient (X := Plane) L U V A D hU hV hcU hcV hd hpart hAc hDc hAL hDL hno with h | h
    · exact ⟨V, U, hV, hU, hcV, hcU, hd.symm, by simpa only [union_comm] using hpart,
        hfV, hfU, h.2, h.1⟩
    · exact ⟨U, V, hU, hV, hcU, hcV, hd, hpart, hfU, hfV, h.2, h.1⟩
  have nesting (L U V : Set Plane) (hL : IsConnected L)
      (hU : IsOpen U) (hV : IsOpen V) (hcU : IsConnected U) (hcV : IsConnected V)
      (hd : Disjoint U V) (hpart : U ∪ V = Lᶜ)
      (hfU : frontier U = L) (hfV : frontier V = L)
      (T B : ℝ) (hT : 0 < T)
      (hupper : {z : Plane | B < z 1} ⊆ U)
      (hlower : {z : Plane | z 1 < -B} ⊆ V)
      (hdis : Disjoint L ((Homeomorph.addRight (Plane.mk 0 T)) '' L)) :
      let e := Homeomorph.addRight (Plane.mk 0 T)
      e '' U ⊂ U ∧ e '' L ⊆ U ∧ L ⊆ e '' V := by
    dsimp only
    have ordered {X : Type} [TopologicalSpace X]
        (L₁ L₂ U₁ V₁ U₂ V₂ : Set X)
        (hL₁ : L₁.Nonempty) (hL₂ : IsConnected L₂)
        (hU₁ : IsOpen U₁) (hV₁ : IsOpen V₁) (hU₂ : IsOpen U₂) (hV₂ : IsOpen V₂)
        (hcU₁ : IsConnected U₁) (hcV₁ : IsConnected V₁)
        (hd₁ : Disjoint U₁ V₁) (hd₂ : Disjoint U₂ V₂)
        (hp₁ : U₁ ∪ V₁ = L₁ᶜ) (hp₂ : U₂ ∪ V₂ = L₂ᶜ)
        (hfU₁ : frontier U₁ = L₁) (hfV₁ : frontier V₁ = L₁)
        (hdL : Disjoint L₁ L₂)
        (hcommonU : (U₁ ∩ U₂).Nonempty) (hcommonV : (V₁ ∩ V₂).Nonempty) :
        U₁ ⊂ U₂ ∨ U₂ ⊂ U₁ := by
      have hU₁L : Disjoint U₁ L₁ := by
        apply disjoint_left.mpr
        intro x hx hL
        exact (show x ∈ L₁ᶜ from hp₁ ▸ Or.inl hx) hL
      have hV₁L : Disjoint V₁ L₁ := by
        apply disjoint_left.mpr
        intro x hx hL
        exact (show x ∈ L₁ᶜ from hp₁ ▸ Or.inr hx) hL
      have hU₂L : Disjoint U₂ L₂ := by
        apply disjoint_left.mpr
        intro x hx hL
        exact (show x ∈ L₂ᶜ from hp₂ ▸ Or.inl hx) hL
      have hclU : closure U₁ = U₁ ∪ L₁ := by rw [closure_eq_self_union_frontier, hfU₁]
      have hclV : closure V₁ = V₁ ∪ L₁ := by rw [closure_eq_self_union_frontier, hfV₁]
      have hsub : L₂ ⊆ U₁ ∪ V₁ := by
        rw [hp₁]
        exact fun x hx h => disjoint_left.mp hdL h hx
      rcases hL₂.isPreconnected.subset_or_subset hU₁ hV₁ hd₁ hsub with hLU | hLV
      · have hsubcl : closure V₁ ⊆ U₂ ∪ V₂ := by
          rw [hp₂, hclV]
          rintro x (hx | hx) hL
          · exact disjoint_left.mp hd₁ (hLU hL) hx
          · exact disjoint_left.mp hdL hx hL
        have hcl : closure V₁ ⊆ V₂ := by
          rcases hcV₁.closure.isPreconnected.subset_or_subset hU₂ hV₂ hd₂ hsubcl with h | h
          · obtain ⟨x, hx₁, hx₂⟩ := hcommonV
            exact False.elim (disjoint_left.mp hd₂ (h (subset_closure hx₁)) hx₂)
          · exact h
        have hUU : U₂ ⊆ U₁ := by
          intro x hx
          by_contra hx₁
          have hxcl : x ∈ closure V₁ := by
            rw [hclV]
            by_cases hxL : x ∈ L₁
            · exact Or.inr hxL
            · have hside : x ∈ U₁ ∪ V₁ := hp₁.symm ▸ hxL
              exact Or.inl (hside.resolve_left hx₁)
          exact disjoint_left.mp hd₂ hx (hcl hxcl)
        right
        apply Set.ssubset_iff_subset_ne.mpr
        refine ⟨hUU, ?_⟩
        intro he
        obtain ⟨x, hx⟩ := hL₂.nonempty
        exact disjoint_left.mp hU₂L (he.symm ▸ hLU hx) hx
      · have hsubcl : closure U₁ ⊆ U₂ ∪ V₂ := by
          rw [hp₂, hclU]
          rintro x (hx | hx) hL
          · exact disjoint_left.mp hd₁ hx (hLV hL)
          · exact disjoint_left.mp hdL hx hL
        have hcl : closure U₁ ⊆ U₂ := by
          rcases hcU₁.closure.isPreconnected.subset_or_subset hU₂ hV₂ hd₂ hsubcl with h | h
          · exact h
          · obtain ⟨x, hx₁, hx₂⟩ := hcommonU
            exact False.elim (disjoint_left.mp hd₂ hx₂ (h (subset_closure hx₁)))
        left
        apply Set.ssubset_iff_subset_ne.mpr
        refine ⟨subset_closure.trans hcl, ?_⟩
        intro he
        obtain ⟨x, hx⟩ := hL₁
        have hxc : x ∈ closure U₁ := hclU.symm ▸ Or.inr hx
        exact disjoint_left.mp hU₁L (he.symm ▸ hcl hxc) hx
  
    let δ := Plane.mk 0 T
    let e : Plane ≃ₜ Plane := Homeomorph.addRight δ
    have hcommonU : (U ∩ e '' U).Nonempty := by
      refine ⟨Plane.mk 0 (B+T+1), hupper (by dsimp [Plane.mk]; linarith), ?_⟩
      refine ⟨Plane.mk 0 (B+1), hupper (by dsimp [Plane.mk]; linarith), ?_⟩
      ext i
      fin_cases i <;> simp [e, δ, Plane.mk] <;> ring
    have hcommonV : (V ∩ e '' V).Nonempty := by
      refine ⟨Plane.mk 0 (-B-1), hlower (by dsimp [Plane.mk]; linarith), ?_⟩
      refine ⟨Plane.mk 0 (-B-1-T), hlower (by dsimp [Plane.mk]; linarith), ?_⟩
      ext i
      fin_cases i <;> simp [e, δ, Plane.mk] <;> ring
    have hpartE : (e '' U) ∪ (e '' V) = (e '' L)ᶜ := by
      rw [← image_union, hpart, e.image_compl]
    have horder := ordered (X := Plane) L (e '' L) U V (e '' U) (e '' V)
      hL.nonempty (hL.image _ e.continuous.continuousOn) hU hV
      (e.isOpenMap _ hU) (e.isOpenMap _ hV) hcU hcV hd
      ((disjoint_image_iff e.injective).mpr hd) hpart hpartE hfU hfV hdis
      hcommonU hcommonV
    have hnobad : ¬ U ⊆ e '' U := by
      intro hbad
      have hstep (z : Plane) (hz : z ∈ U) : z - δ ∈ U := by
        obtain ⟨w, hw, he⟩ := hbad hz
        change w + δ = z at he
        have hwz : w = z - δ := eq_sub_of_add_eq he
        exact hwz ▸ hw
      obtain ⟨x, hx⟩ := hcU.nonempty
      have hiter (n : ℕ) : x - (n : ℝ) • δ ∈ U := by
        induction n with
        | zero => simpa using hx
        | succ n hn =>
          have hh := hstep _ hn
          convert hh using 1
          ext i
          fin_cases i <;> simp [δ, Plane.mk] <;> ring
      obtain ⟨N, hN⟩ := exists_nat_gt ((x 1 + B) / T)
      have hNT := (div_lt_iff₀ hT).mp hN
      have hlow : x - (N : ℝ) • δ ∈ V := by
        apply hlower
        change x 1 - (N : ℝ) * T < -B
        linarith
      exact disjoint_left.mp hd (hiter N) hlow
    have hnested : e '' U ⊂ U := horder.resolve_left (fun h => hnobad h.subset)
    have hUL : Disjoint U L := by
      apply disjoint_left.mpr
      intro x hx hxl
      exact (show x ∈ Lᶜ from hpart ▸ Or.inl hx) hxl
    have hlineAbove : e '' L ⊆ U := by
      intro x hx
      have hfront : x ∈ frontier (e '' U) := by
        rw [← e.image_frontier U, hfU]
        exact hx
      have hcl : x ∈ closure U := (closure_mono hnested.subset) (frontier_subset_closure hfront)
      rw [closure_eq_self_union_frontier, hfU] at hcl
      exact hcl.resolve_right (fun h => disjoint_left.mp hdis h hx)
    have hlineBelow : L ⊆ e '' V := by
      intro x hx
      have hxE : x ∈ (e '' L)ᶜ := fun h => disjoint_left.mp hdis hx h
      have hside : x ∈ e '' U ∪ e '' V := hpartE.symm ▸ hxE
      exact hside.resolve_left (fun h => disjoint_left.mp hUL (hnested.subset h) hx)
    exact ⟨hnested, hlineAbove, hlineBelow⟩

  have hper : Function.Periodic (fun x => G x 1) T := by
    intro x
    have hh := congrArg (fun z : Plane => z 1) (hp 1 x)
    simpa [Plane.mk] using hh
  have hycont : Continuous (fun x => G x 1) := (EuclideanSpace.proj 1).continuous.comp G.continuous
  have hcompact : IsCompact (range (fun x => G x 1)) := by
    rw [← hper.image_Icc hT 0]
    exact isCompact_Icc.image hycont
  obtain ⟨M, hM⟩ := (hcompact.image continuous_abs).bddAbove
  let B := max M 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (x : ℝ) : |G x 1| < B := by
    have hh := hM ⟨G x 1, ⟨x, rfl⟩, rfl⟩
    dsimp [B]
    linarith [le_max_left M 0]
  have hends (R : ℝ) : ∃ A : ℝ, G (-A) 0 < -R ∧ R < G A 0 := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((R + |G 0 0|) / T)
    have hNT := (div_lt_iff₀ hT).mp hN
    refine ⟨(N : ℝ) * T, ?_, ?_⟩
    · have hh := congrArg (fun z : Plane => z 0) (hp (-(N : ℤ)) 0)
      simp only [Int.cast_neg, Int.cast_natCast, zero_add, neg_mul] at hh
      change G (-((N : ℝ) * T)) 0 = G 0 0 + -((N : ℝ) * T) at hh
      linarith [le_abs_self (G 0 0)]
    · have hh := congrArg (fun z : Plane => z 0) (hp (N : ℤ) 0)
      simp only [Int.cast_natCast, zero_add] at hh
      change G ((N : ℝ) * T) 0 = G 0 0 + (N : ℝ) * T at hh
      linarith [neg_abs_le (G 0 0)]
  obtain ⟨U, V, hU, hV, hcU, hcV, hd, hpart, hfU, hfV, hupper, hlower⟩ :=
    sides G hG.isProperMap hG.injective B hB hbound hends
  have hnested := nesting (range G) U V (isConnected_range G.continuous)
    hU hV hcU hcV hd hpart hfU hfV T B hT hupper hlower hdis
  exact ⟨U, V, B, hB, hU, hV, hcU, hcV, hd, hpart, hfU, hfV, hupper, hlower, hnested⟩

#print axioms normalized_line_ordered_sides

theorem nested_vertical_bands_pairwise (U V : Set Plane) (T : ℝ) (hd : Disjoint U V)
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

/-- The complementary sides are invariant under every horizontal deck translation. -/
theorem normalized_line_side_periodicity (G : C(ℝ, Plane)) (T B : ℝ)
    (hp : ∀ (n : ℤ) x, G (x + (n : ℝ) * T) = G x + Plane.mk ((n : ℝ) * T) 0)
    (U V : Set Plane) (hU : IsOpen U) (hV : IsOpen V)
    (hcU : IsConnected U) (hcV : IsConnected V) (hd : Disjoint U V)
    (hpart : U ∪ V = (range G)ᶜ)
    (hupper : {z : Plane | B < z 1} ⊆ U)
    (hlower : {z : Plane | z 1 < -B} ⊆ V) :
    ∀ n : ℤ, (fun z : Plane => z + Plane.mk ((n : ℝ)*T) 0) '' U = U ∧
      (fun z : Plane => z + Plane.mk ((n : ℝ)*T) 0) '' V = V := by
  let X : ℤ → Plane ≃ₜ Plane := fun n => Homeomorph.addRight (Plane.mk ((n:ℝ)*T) 0)
  have line (n : ℤ) : X n '' range G = range G := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x + (n:ℝ)*T, hp n x⟩
    · rintro ⟨x, rfl⟩
      refine ⟨G (x - (n:ℝ)*T), mem_range_self _, ?_⟩
      change G (x - (n:ℝ)*T) + Plane.mk ((n:ℝ)*T) 0 = G x
      rw [← hp n]
      congr 1
      ring
  have comp (n : ℤ) (S : Set Plane) : X (-n) '' (X n '' S) = S := by
    rw [← image_comp]
    have he : (X (-n) : Plane → Plane) ∘ X n = id := by
      funext z
      ext i
      fin_cases i <;> simp [X, Plane.mk] <;> ring
    rw [he, image_id]
  have subsets (n : ℤ) : X n '' U ⊆ U ∧ X n '' V ⊆ V := by
    have hcover : X n '' (U ∪ V) = U ∪ V := by
      rw [hpart, (X n).image_compl, line]
    have hsubU : X n '' U ⊆ U ∪ V := by
      rw [← hcover]
      exact image_mono subset_union_left
    have hsubV : X n '' V ⊆ U ∪ V := by
      rw [← hcover]
      exact image_mono subset_union_right
    have hup : (X n '' U ∩ U).Nonempty := by
      refine ⟨X n (Plane.mk 0 (B+1)), mem_image_of_mem _ (hupper ?_), hupper ?_⟩
      · change B < B+1
        linarith
      · change B < B+1+0
        linarith
    have hlo : (X n '' V ∩ V).Nonempty := by
      refine ⟨X n (Plane.mk 0 (-B-1)), mem_image_of_mem _ (hlower ?_), hlower ?_⟩
      · change -B-1 < -B
        linarith
      · change -B-1+0 < -B
        linarith
    constructor
    · rcases (hcU.image _ (X n).continuous.continuousOn).isPreconnected.subset_or_subset
          hU hV hd hsubU with h | h
      · exact h
      · obtain ⟨z, hz, hzU⟩ := hup
        exact False.elim (disjoint_left.mp hd hzU (h hz))
    · rcases (hcV.image _ (X n).continuous.continuousOn).isPreconnected.subset_or_subset
          hU hV hd hsubV with h | h
      · obtain ⟨z, hz, hzV⟩ := hlo
        exact False.elim (disjoint_left.mp hd (h hz) hzV)
      · exact h
  intro n
  constructor
  · apply subset_antisymm (subsets n).1
    have h := image_mono (subsets (-n)).1 (f := X n)
    have he := comp (-n) U
    simp only [neg_neg] at he
    rwa [he] at h
  · apply subset_antisymm (subsets n).2
    have h := image_mono (subsets (-n)).2 (f := X n)
    have he := comp (-n) V
    simp only [neg_neg] at he
    rwa [he] at h

/-- Genuine complementary bands produced from the line, without side receipts. -/
theorem normalized_line_has_nested_periodic_bands (G : C(ℝ, Plane)) (hG : IsClosedEmbedding G)
    (T : ℝ) (hT : 0 < T)
    (hp : ∀ (n : ℤ) x, G (x + (n : ℝ) * T) = G x + Plane.mk ((n : ℝ) * T) 0)
    (hdis : Disjoint (range G) ((Homeomorph.addRight (Plane.mk 0 T)) '' range G)) :
    ∃ U V : Set Plane, ∃ B : ℝ,
      0 < B ∧ IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (range G)ᶜ ∧
      frontier U = range G ∧ frontier V = range G ∧
      {z : Plane | B < z 1} ⊆ U ∧ {z : Plane | z 1 < -B} ⊆ V ∧
      let e := Homeomorph.addRight (Plane.mk 0 T)
      e '' U ⊂ U ∧ e '' range G ⊆ U ∧ range G ⊆ e '' V ∧
      (∀ n : ℤ, (fun z : Plane => z + Plane.mk ((n:ℝ)*T) 0) '' (U ∩ e '' V) = U ∩ e '' V) ∧
      Pairwise (fun i j : ℤ => Disjoint
        ((Homeomorph.addRight (Plane.mk 0 ((i:ℝ)*T))) '' (U ∩ e '' V))
        ((Homeomorph.addRight (Plane.mk 0 ((j:ℝ)*T))) '' (U ∩ e '' V))) := by
  obtain ⟨U,V,B,hB,hU,hV,hcU,hcV,hd,hpart,hfU,hfV,hupper,hlower,hnest,habove,hbelow⟩ :=
    normalized_line_ordered_sides G hG T hT hp hdis
  refine ⟨U,V,B,hB,hU,hV,hcU,hcV,hd,hpart,hfU,hfV,hupper,hlower,hnest,habove,hbelow,?_,?_⟩
  · intro n
    let X : Plane ≃ₜ Plane := Homeomorph.addRight (Plane.mk ((n:ℝ)*T) 0)
    let e : Plane ≃ₜ Plane := Homeomorph.addRight (Plane.mk 0 T)
    have hper := normalized_line_side_periodicity G T B hp U V hU hV hcU hcV hd hpart hupper hlower n
    have commute : X '' (e '' V) = e '' (X '' V) := by
      rw [← image_comp, ← image_comp]
      congr 1
      funext z
      ext i
      fin_cases i <;> simp [X,e,Plane.mk]
    change X '' (U ∩ e '' V) = U ∩ e '' V
    rw [image_inter X.injective,commute]
    change X '' U ∩ e '' (X '' V) = U ∩ e '' V
    change X '' U = U ∧ X '' V = V at hper
    rw [hper.1,hper.2]
  · simpa using nested_vertical_bands_pairwise U V T hd hnest.subset

#print axioms normalized_line_side_periodicity
#print axioms normalized_line_has_nested_periodic_bands

/-- An arc whose interior avoids the line and whose endpoint is on one open side
lies in that side together with its frontier. -/
theorem lineMap_inside_side (L U V : Set Plane) (hU : IsOpen U) (hV : IsOpen V)
    (hd : Disjoint U V) (hpart : U ∪ V = Lᶜ) (hfront : frontier U = L)
    (p q : Plane) (hend : p ∈ U ∨ q ∈ U)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap p q t ∉ L) :
    segment ℝ p q ⊆ U ∪ L := by
  let f : ℝ → Plane := AffineMap.lineMap p q
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hsub : f '' Ioo (0:ℝ) 1 ⊆ U ∪ V := by
    rintro _ ⟨t,ht,rfl⟩
    exact hpart.symm ▸ havoid t ht
  have hconn : IsPreconnected (f '' Ioo (0:ℝ) 1) :=
    isPreconnected_Ioo.image f hf.continuousOn
  have hin : f '' Ioo (0:ℝ) 1 ⊆ U := by
    rcases hconn.subset_or_subset hU hV hd hsub with h | h
    · exact h
    · have cl0 : f 0 ∈ closure (f '' Ioo (0:ℝ) 1) := by
        apply hf.continuousAt.continuousWithinAt.mem_closure_image
        rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
        exact left_mem_Icc.mpr (by norm_num)
      have cl1 : f 1 ∈ closure (f '' Ioo (0:ℝ) 1) := by
        apply hf.continuousAt.continuousWithinAt.mem_closure_image
        rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
        exact right_mem_Icc.mpr (by norm_num)
      have discl : Disjoint U (closure V) := hd.closure_right hU
      rcases hend with hp | hq
      · exact False.elim (disjoint_left.mp discl hp (closure_mono h (by simpa [f] using cl0)))
      · exact False.elim (disjoint_left.mp discl hq (closure_mono h (by simpa [f] using cl1)))
  have hcl : segment ℝ p q ⊆ closure U := by
    rw [segment_eq_image_lineMap]
    rintro _ ⟨t,ht,rfl⟩
    apply closure_mono hin
    apply hf.continuousAt.continuousWithinAt.mem_closure_image
    rwa [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
  rw [← hfront, ← closure_eq_self_union_frontier]
  exact hcl

#print axioms lineMap_inside_side

theorem vertical_sides_unbounded (U V : Set Plane) (B : ℝ)
    (hupper : {z : Plane | B < z 1} ⊆ U)
    (hlower : {z : Plane | z 1 < -B} ⊆ V) :
    ¬ Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V := by
  have bound (S : Set Plane) (hS : Bornology.IsBounded S) :
      ∃ M : ℝ, ∀ z ∈ S, |z 1| ≤ M := by
    have hc := hS.isCompact_closure.image
      ((EuclideanSpace.proj 1).continuous.abs)
    obtain ⟨M,hM⟩ := hc.bddAbove
    exact ⟨M,fun z hz => hM ⟨z,subset_closure hz,rfl⟩⟩
  constructor
  · intro h
    obtain ⟨M,hM⟩ := bound U h
    have hz : Plane.mk 0 (max B M+1) ∈ U := hupper (by
      change B < max B M+1
      linarith [le_max_left B M])
    have hh := hM _ hz
    change |max B M+1| ≤ M at hh
    linarith [le_abs_self (max B M+1), le_max_right B M]
  · intro h
    obtain ⟨M,hM⟩ := bound V h
    have hz : Plane.mk 0 (-(max B M+1)) ∈ V := hlower (by
      change -(max B M+1) < -B
      linarith [le_max_left B M])
    have hh := hM _ hz
    change |-(max B M+1)| ≤ M at hh
    rw [abs_neg] at hh
    linarith [le_abs_self (max B M+1), le_max_right B M]

/-- The actual four-edge cell is inside the band constructed from its line and
its adjacent translate. No complementary-side hypothesis is supplied. -/
theorem normalized_four_edge_cell_inside_actual_band (G : C(ℝ, Plane)) (hG : IsClosedEmbedding G)
    (T : ℝ) (hT : 0 < T)
    (hp : ∀ (n : ℤ) x, G (x + (n : ℝ) * T) = G x + Plane.mk ((n : ℝ) * T) 0)
    (hdis : Disjoint (range G) ((Homeomorph.addRight (Plane.mk 0 T)) '' range G))
    (x y : ℝ)
    (havoid : ∀ t ∈ Ioo (0:ℝ) 1,
      AffineMap.lineMap (G x) (G y + Plane.mk 0 T) t ∉
        range G ∪ (Homeomorph.addRight (Plane.mk 0 T)) '' range G)
    (hJordan : IsJordanCurve
      ((G '' Icc x (x+T) ∪
        (fun z : Plane => z + Plane.mk T 0) '' segment ℝ (G x) (G y + Plane.mk 0 T)) ∪
        (segment ℝ (G x) (G y + Plane.mk 0 T) ∪
        (fun s : ℝ => G s + Plane.mk 0 T) '' Icc y (y+T)))) :
    let C := ((G '' Icc x (x+T) ∪
        (fun z : Plane => z + Plane.mk T 0) '' segment ℝ (G x) (G y + Plane.mk 0 T)) ∪
        (segment ℝ (G x) (G y + Plane.mk 0 T) ∪
        (fun s : ℝ => G s + Plane.mk 0 T) '' Icc y (y+T)))
    ∃ U V : Set Plane,
      Disjoint U V ∧ (Homeomorph.addRight (Plane.mk 0 T)) '' U ⊆ U ∧
      inside C ⊆ U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V ∧
      (∀ n : ℤ, (fun z : Plane => z+Plane.mk ((n:ℝ)*T) 0) ''
        (U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V) =
        U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V) ∧
      Pairwise (fun i j : ℤ => Disjoint
        ((Homeomorph.addRight (Plane.mk 0 ((i:ℝ)*T))) ''
          (U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V))
        ((Homeomorph.addRight (Plane.mk 0 ((j:ℝ)*T))) ''
          (U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V))) := by
  dsimp only
  let C := ((G '' Icc x (x+T) ∪
        (fun z : Plane => z + Plane.mk T 0) '' segment ℝ (G x) (G y + Plane.mk 0 T)) ∪
        (segment ℝ (G x) (G y + Plane.mk 0 T) ∪
        (fun s : ℝ => G s + Plane.mk 0 T) '' Icc y (y+T)))
  let e : Plane ≃ₜ Plane := Homeomorph.addRight (Plane.mk 0 T)
  let X : Plane ≃ₜ Plane := Homeomorph.addRight (Plane.mk T 0)
  let E := segment ℝ (G x) (G y + Plane.mk 0 T)
  obtain ⟨U,V,B,hB,hU,hV,hcU,hcV,hd,hpart,hfU,hfV,hupper,hlower,hnest,habove,hbelow,hperiod,hbands⟩ :=
    normalized_line_has_nested_periodic_bands G hG T hT hp hdis
  have hpartE : e '' V ∪ e '' U = (e '' range G)ᶜ := by
    rw [← image_union, union_comm V U, hpart, e.image_compl]
  have hfEV : frontier (e '' V) = e '' range G := by
    rw [← e.image_frontier,hfV]
  have hEup : E ⊆ U ∪ range G := by
    apply lineMap_inside_side (range G) U V hU hV hd hpart hfU (G x) (G y+Plane.mk 0 T)
    · exact Or.inr (habove ⟨G y,mem_range_self y,rfl⟩)
    · intro t ht hL
      exact havoid t ht (Or.inl hL)
  have hEdown : E ⊆ e '' V ∪ e '' range G := by
    apply lineMap_inside_side (e '' range G) (e '' V) (e '' U)
      (e.isOpenMap _ hV) (e.isOpenMap _ hU) ((disjoint_image_iff e.injective).mpr hd.symm)
      hpartE hfEV (G x) (G y+Plane.mk 0 T)
    · exact Or.inl (hbelow (mem_range_self x))
    · intro t ht hL
      exact havoid t ht (Or.inr hL)
  have hpUV := normalized_line_side_periodicity G T B hp U V hU hV hcU hcV hd hpart hupper hlower 1
  have hXU : X '' U = U := by simpa [X] using hpUV.1
  have hXV : X '' V = V := by simpa [X] using hpUV.2
  have hXL : X '' range G = range G := by
    ext z
    constructor
    · rintro ⟨_,⟨s,rfl⟩,rfl⟩
      exact ⟨s+T,by simpa [X] using hp 1 s⟩
    · rintro ⟨s,rfl⟩
      refine ⟨G (s-T),mem_range_self _,?_⟩
      have hh := hp 1 (s-T)
      simpa [X] using hh.symm
  have hcomm (S : Set Plane) : X '' (e '' S) = e '' (X '' S) := by
    rw [← image_comp, ← image_comp]
    congr 1
    funext z
    ext i
    fin_cases i <;> simp [X,e,Plane.mk]
  have hXup : X '' (U ∪ range G) = U ∪ range G := by
    rw [image_union,hXU,hXL]
  have hXdown : X '' (e '' V ∪ e '' range G) = e '' V ∪ e '' range G := by
    rw [image_union,hcomm,hcomm,hXV,hXL]
  have hCup : C ⊆ U ∪ range G := by
    rintro z ((hzP | hzR) | (hzE | hzQ))
    · exact Or.inr (by obtain ⟨s,hs,rfl⟩ := hzP; exact mem_range_self s)
    · exact hXup ▸ image_mono hEup hzR
    · exact hEup hzE
    · exact Or.inl (habove (by obtain ⟨s,hs,rfl⟩ := hzQ; exact ⟨G s,mem_range_self s,rfl⟩))
  have hCdown : C ⊆ e '' V ∪ e '' range G := by
    rintro z ((hzP | hzR) | (hzE | hzQ))
    · exact Or.inl (hbelow (by obtain ⟨s,hs,rfl⟩ := hzP; exact mem_range_self s))
    · exact hXdown ▸ image_mono hEdown hzR
    · exact hEdown hzE
    · exact Or.inr (by obtain ⟨s,hs,rfl⟩ := hzQ; exact ⟨G s,mem_range_self s,rfl⟩)
  have hunbounded := vertical_sides_unbounded U V B hupper hlower
  have heUpper : {z : Plane | B+T < z 1} ⊆ e '' U := by
    intro z hz
    refine ⟨e.symm z,hupper ?_,e.apply_symm_apply z⟩
    change B < z 1-T
    change B+T < z 1 at hz
    linarith
  have heLower : {z : Plane | z 1 < -(B+T)} ⊆ e '' V := by
    intro z hz
    refine ⟨e.symm z,hlower ?_,e.apply_symm_apply z⟩
    change z 1-T < -B
    change z 1 < -(B+T) at hz
    linarith
  have heUnbounded := vertical_sides_unbounded (e '' U) (e '' V) (B+T) heUpper heLower
  have hinU : inside C ⊆ U := jordan_inside_contained_in_proper_line_side hJordan
    hU hV hcV hd hpart hfV hunbounded.2 hCup
  have hinEV : inside C ⊆ e '' V := jordan_inside_contained_in_proper_line_side hJordan
    (e.isOpenMap _ hV) (e.isOpenMap _ hU) (hcU.image _ e.continuous.continuousOn)
    ((disjoint_image_iff e.injective).mpr hd.symm) hpartE
    (by rw [← e.image_frontier,hfU]) heUnbounded.1 hCdown
  exact ⟨U,V,hd,hnest.subset,fun z hz => ⟨hinU hz,hinEV hz⟩,hperiod,hbands⟩

#print axioms normalized_four_edge_cell_inside_actual_band

theorem plane_homeomorph_inside_transport (e : Plane ≃ₜ Plane) (C : Set Plane) :
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

theorem band_contained_disk_different_rows (C U V : Set Plane) (T : ℝ)
    (hinside : inside C ⊆ U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V)
    (hperiod : ∀ n : ℤ, (fun z : Plane => z+Plane.mk ((n:ℝ)*T) 0) ''
      (U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V) =
      U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V)
    (hbands : Pairwise (fun i j : ℤ => Disjoint
      ((Homeomorph.addRight (Plane.mk 0 ((i:ℝ)*T))) ''
        (U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V))
      ((Homeomorph.addRight (Plane.mk 0 ((j:ℝ)*T))) ''
        (U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V)))) :
    ∀ i j : ℤ × ℤ, i.2 ≠ j.2 → Disjoint
      (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' C))
      (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) '' C)) := by
  let X : ℤ → Plane ≃ₜ Plane := fun n => Homeomorph.addRight (Plane.mk ((n:ℝ)*T) 0)
  let Y : ℤ → Plane ≃ₜ Plane := fun n => Homeomorph.addRight (Plane.mk 0 ((n:ℝ)*T))
  let Z : ℤ × ℤ → Plane ≃ₜ Plane := fun i => Homeomorph.addRight (Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))
  let W := U ∩ (Homeomorph.addRight (Plane.mk 0 T)) '' V
  have form (i : ℤ × ℤ) : inside (Z i '' C) = Y i.2 '' inside (X i.1 '' C) := by
    rw [← (plane_homeomorph_inside_transport (Z i) C).1,
      ← (plane_homeomorph_inside_transport (X i.1) C).1, ← image_comp]
    congr 1
    funext z
    ext k
    fin_cases k <;> simp [Z,Y,X,Plane.mk]
  have rowIn (n : ℤ) : inside (X n '' C) ⊆ W := by
    rw [← (plane_homeomorph_inside_transport (X n) C).1]
    have hh := image_mono hinside (f := X n)
    change X n '' inside C ⊆ X n '' W at hh
    have hper : X n '' W = W := hperiod n
    rwa [hper] at hh
  intro i j hij
  change Disjoint (inside (Z i '' C)) (inside (Z j '' C))
  rw [form,form]
  exact (hbands hij).mono (image_mono (rowIn i.1)) (image_mono (rowIn j.1))

theorem normalized_four_edge_cell_vertical_separation (G : C(ℝ, Plane)) (hG : IsClosedEmbedding G)
    (T : ℝ) (hT : 0 < T)
    (hp : ∀ (n : ℤ) x, G (x + (n : ℝ) * T) = G x + Plane.mk ((n : ℝ) * T) 0)
    (hdis : Disjoint (range G) ((Homeomorph.addRight (Plane.mk 0 T)) '' range G))
    (x y : ℝ)
    (havoid : ∀ t ∈ Ioo (0:ℝ) 1,
      AffineMap.lineMap (G x) (G y + Plane.mk 0 T) t ∉
        range G ∪ (Homeomorph.addRight (Plane.mk 0 T)) '' range G)
    (hJordan : IsJordanCurve
      ((G '' Icc x (x+T) ∪
        (fun z : Plane => z + Plane.mk T 0) '' segment ℝ (G x) (G y + Plane.mk 0 T)) ∪
        (segment ℝ (G x) (G y + Plane.mk 0 T) ∪
        (fun s : ℝ => G s + Plane.mk 0 T) '' Icc y (y+T)))) :
    let C := ((G '' Icc x (x+T) ∪
        (fun z : Plane => z + Plane.mk T 0) '' segment ℝ (G x) (G y + Plane.mk 0 T)) ∪
        (segment ℝ (G x) (G y + Plane.mk 0 T) ∪
        (fun s : ℝ => G s + Plane.mk 0 T) '' Icc y (y+T)))
    (∀ i j : ℤ × ℤ, i.2 ≠ j.2 → Disjoint
      (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' C))
      (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) '' C))) ∧
    (Pairwise (fun i j : ℤ => Disjoint
      (inside ((fun z : Plane => z+Plane.mk ((i:ℝ)*T) 0) '' C))
      (inside ((fun z : Plane => z+Plane.mk ((j:ℝ)*T) 0) '' C))) →
    Pairwise (fun i j : ℤ × ℤ => Disjoint
      (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' C))
      (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) '' C)))) := by
  dsimp only
  obtain ⟨U,V,hd,hnest,hinside,hperiod,hbands⟩ :=
    normalized_four_edge_cell_inside_actual_band G hG T hT hp hdis x y havoid hJordan
  exact ⟨band_contained_disk_different_rows _ U V T hinside hperiod hbands,
    fun hrow => vertical_translate_inside_pairwise _ U V T hd hnest hinside hperiod hrow⟩

#print axioms normalized_four_edge_cell_vertical_separation
