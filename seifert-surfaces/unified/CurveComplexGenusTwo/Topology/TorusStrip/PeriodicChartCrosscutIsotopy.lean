import CurveComplexGenusTwo.Topology.CrosscutIsotopy
import Schoenflies.JordanClosed
import Mathlib
open Set Schoenflies CurveComplex Bornology Filter
open scoped Topology
set_option maxHeartbeats 5000000

theorem periodic_chart_crosscut_isotopy (T : ℝ) (hT : 0 < T) (φ : Plane ≃ₜ Plane)
    (hdeck : ∀ i : ℤ × ℤ, i ≠ 0 → Disjoint (φ '' Plane.closedSquare 0 1)
      ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (φ '' Plane.closedSquare 0 1)))
    (A B : Set Plane) (a b : Plane)
    (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
    (ha : φ.symm a ∈ modelCurve) (hb : φ.symm b ∈ modelCurve)
    (hAi : A \ {a,b} ⊆ φ '' Plane.openSquare 0 1)
    (hBi : B \ {a,b} ⊆ φ '' Plane.openSquare 0 1) :
    let δ : ℤ × ℤ → Plane := fun i => Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
    ∃ P : AmbientIsotopy Plane,
      (∀ t i z, P.map (t,z+δ i)=P.map (t,z)+δ i) ∧
      (∀ i, P.finalMap '' ((fun z : Plane => z+δ i) '' A)=
        (fun z : Plane => z+δ i) '' B) ∧
      (∀ t z, z ∉ ⋃ i : ℤ × ℤ, (fun w : Plane => w+δ i) ''
        (φ '' Plane.openSquare 0 1) → P.map (t,z)=z) := by
  dsimp only
  let δ : ℤ × ℤ → Plane := fun i => Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
  have crosscut (φ : Plane ≃ₜ Plane) (A B : Set Plane) (a b : Plane)
      (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
      (ha : φ.symm a ∈ modelCurve) (hb : φ.symm b ∈ modelCurve)
      (hAi : A \ {a,b} ⊆ φ '' Plane.openSquare 0 1)
      (hBi : B \ {a,b} ⊆ φ '' Plane.openSquare 0 1) :
      ∃ H : AmbientIsotopy Plane, H.finalMap '' A = B ∧
        ∀ t x, x ∉ φ '' Plane.openSquare 0 1 → H.map (t,x) = x := by
    have imageArc (C : Set Plane) (hC : IsArcBetween C a b) :
        IsArcBetween (φ.symm '' C) (φ.symm a) (φ.symm b) :=
      hC.image_of_injOn (subset_univ _) φ.symm.continuous.continuousOn
        φ.symm.injective.injOn
    have imageInterior (C : Set Plane)
        (hCi : C \ {a,b} ⊆ φ '' Plane.openSquare 0 1) :
        (φ.symm '' C) \ {φ.symm a,φ.symm b} ⊆ Plane.openSquare 0 1 := by
      rintro z ⟨⟨x,hx,rfl⟩,hn⟩
      have hxnot : x ∉ ({a,b} : Set Plane) := by
        intro hh
        apply hn
        rcases hh with hh | hh <;> simp_all
      obtain ⟨y,hy,he⟩ := hCi ⟨hx,hxnot⟩
      simpa only [← he, φ.symm_apply_apply] using hy
    obtain ⟨R,H,hR,hfinal,hlarge,hfix⟩ := position_crosscut_supported_isotopy
      (φ.symm '' A) (φ.symm '' B) (φ.symm a) (φ.symm b)
      (imageArc A hA) (imageArc B hB) ha hb (imageInterior A hAi) (imageInterior B hBi)
    let P : AmbientIsotopy Plane := {
      map := ⟨fun p => φ (H.map (p.1,φ.symm p.2)), by fun_prop⟩
      homeomorphism_at := by
        intro t
        obtain ⟨e,he⟩ := H.homeomorphism_at t
        refine ⟨(φ.symm.trans e).trans φ, ?_⟩
        intro x
        change φ (e (φ.symm x)) = φ (H.map (t,φ.symm x))
        rw [he]
      at_zero := by
        intro x
        change φ (H.map (⟨0,by norm_num⟩,φ.symm x)) = x
        rw [H.at_zero,φ.apply_symm_apply] }
    refine ⟨P,?_,?_⟩
    · ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        have h : H.finalMap (φ.symm x) ∈ φ.symm '' B := by
          rw [← hfinal]
          exact mem_image_of_mem _ (mem_image_of_mem _ hx)
        obtain ⟨y,hy,he⟩ := h
        change φ (H.finalMap (φ.symm x)) ∈ B
        rw [← he,φ.apply_symm_apply]
        exact hy
      · intro hz
        have h : φ.symm z ∈ H.finalMap '' (φ.symm '' A) := by
          rw [hfinal]
          exact mem_image_of_mem _ hz
        obtain ⟨_,⟨x,hx,rfl⟩,he⟩ := h
        refine ⟨x,hx,?_⟩
        change φ (H.finalMap (φ.symm x)) = z
        rw [he,φ.apply_symm_apply]
    · intro t x hx
      change φ (H.map (t,φ.symm x)) = x
      rw [hfix t _ (fun hh => hx ⟨φ.symm x,hh,φ.apply_symm_apply x⟩),φ.apply_symm_apply]
  have periodicMove (T : ℝ) (hT : 0 < T) (D : Set Plane) (hD : IsCompact D)
      (hdeck : ∀ a : ℤ × ℤ, a ≠ 0 → Disjoint D
        ((fun z : Plane => z+Plane.mk ((a.1:ℝ)*T) ((a.2:ℝ)*T)) '' D))
      (H : AmbientIsotopy Plane) (hH : ∀ t z, z ∉ interior D → H.map (t,z)=z) :
      let δ : ℤ × ℤ → Plane := fun i => Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
      ∃ P : AmbientIsotopy Plane,
        (∀ t i z, P.map (t,z+δ i)=P.map (t,z)+δ i) ∧
        (∀ t i z, z ∈ D → P.map (t,z+δ i)=H.map (t,z)+δ i) ∧
        (∀ t z, z ∉ ⋃ i : ℤ × ℤ, (fun w : Plane => w+δ i) '' interior D → P.map (t,z)=z) := by
    classical
    dsimp only
    let δ : ℤ × ℤ → Plane := fun i => Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
    have supported {X : Type} [TopologicalSpace X] {ι κ : Type}
        (K : ι → Set X) (hclosed : ∀ i, IsClosed (K i)) (hlf : LocallyFinite K)
        (hoverlap : ∀ i j x, i ≠ j → x ∈ K i → x ∈ K j → x ∉ interior (K i))
        (e : ι → Interval → X ≃ₜ X)
        (hc : ∀ i, Continuous (fun p : Interval × X => e i p.1 p.2))
        (hz : ∀ i x, e i ⟨0, by norm_num⟩ x = x)
        (hsupp : ∀ i t x, x ∉ interior (K i) → e i t x = x)
        (τ : κ → X → X) (shift : κ → ι → ι)
        (hcell : ∀ a i x, x ∈ K i → τ a x ∈ K (shift a i))
        (hexterior : ∀ a x, x ∉ ⋃ i, interior (K i) → τ a x ∉ ⋃ i, interior (K i))
        (hequiv : ∀ a i t x, x ∈ K i → e (shift a i) t (τ a x) = τ a (e i t x)) :
        ∃ H : AmbientIsotopy X,
          (∀ i t x, x ∈ K i → H.map (t, x) = e i t x) ∧
          (∀ t x, x ∉ ⋃ i, interior (K i) → H.map (t, x) = x) ∧
          (∀ a t x, H.map (t, τ a x) = τ a (H.map (t, x))) := by
      classical
      have glue
          (K : (Option ι) → Set X) (hclosed : ∀ i, IsClosed (K i))
          (hlf : LocallyFinite K) (hcover : ⋃ i, K i = univ)
          (e : (Option ι) → Interval → X ≃ₜ X)
          (hcont : ∀ i, Continuous (fun p : Interval × X => e i p.1 p.2))
          (hzero : ∀ i x, e i ⟨0, by norm_num⟩ x = x)
          (hpres : ∀ i t, MapsTo (e i t) (K i) (K i))
          (hpresInv : ∀ i t, MapsTo (e i t).symm (K i) (K i))
          (hmatch : ∀ i j t x, x ∈ K i → x ∈ K j → e i t x = e j t x)
          (hmatchInv : ∀ i j t x, x ∈ K i → x ∈ K j →
            (e i t).symm x = (e j t).symm x)
          (τ : κ → X → X) (shift : κ → (Option ι) → (Option ι))
          (hcell : ∀ a i x, x ∈ K i → τ a x ∈ K (shift a i))
          (hequiv : ∀ a i t x, x ∈ K i → e (shift a i) t (τ a x) = τ a (e i t x)) :
          ∃ H : AmbientIsotopy X,
            (∀ i t x, x ∈ K i → H.map (t, x) = e i t x) ∧
            (∀ a t x, H.map (t, τ a x) = τ a (H.map (t, x))) := by
        classical
        have hex (x : X) : ∃ i, x ∈ K i := by
          have hx : x ∈ ⋃ i, K i := hcover.symm ▸ mem_univ x
          exact mem_iUnion.mp hx
        let pick : X → (Option ι) := fun x => Classical.choose (hex x)
        have hpick (x : X) : x ∈ K (pick x) := Classical.choose_spec (hex x)
        let f : Interval × X → X := fun p => e (pick p.2) p.1 p.2
        let g : Interval → X → X := fun t x => (e (pick x) t).symm x
        have hf (i : (Option ι)) (t : Interval) (x : X) (hx : x ∈ K i) :
            f (t, x) = e i t x := hmatch _ _ _ _ (hpick x) hx
        have hg (i : (Option ι)) (t : Interval) (x : X) (hx : x ∈ K i) :
            g t x = (e i t).symm x := hmatchInv _ _ _ _ (hpick x) hx
        have hfcont : Continuous f := by
          have hlfProd : LocallyFinite (fun i => Prod.snd ⁻¹' K i : (Option ι) → Set (Interval × X)) :=
            hlf.preimage_continuous continuous_snd
          apply hlfProd.continuous
          · ext p
            simp only [mem_iUnion, mem_preimage, mem_univ, iff_true]
            exact hex p.2
          · intro i
            exact (hclosed i).preimage continuous_snd
          · intro i
            apply (hcont i).continuousOn.congr
            intro p hp
            exact hf i p.1 p.2 hp
        have hgcont (t : Interval) : Continuous (g t) := by
          apply hlf.continuous hcover hclosed
          intro i
          apply (e i t).symm.continuous.continuousOn.congr
          intro x hx
          exact hg i t x hx
        have hleft (t : Interval) (x : X) : g t (f (t, x)) = x := by
          let i := pick x
          have hx : x ∈ K i := hpick x
          rw [hf i t x hx, hg i t (e i t x) (hpres i t hx)]
          exact (e i t).symm_apply_apply x
        have hright (t : Interval) (x : X) : f (t, g t x) = x := by
          let i := pick x
          have hx : x ∈ K i := hpick x
          rw [hg i t x hx, hf i t ((e i t).symm x) (hpresInv i t hx)]
          exact (e i t).apply_symm_apply x
        let H : AmbientIsotopy X := {
          map := ⟨f, hfcont⟩
          homeomorphism_at := by
            intro t
            let E : X ≃ₜ X := {
              toFun := fun x => f (t, x)
              invFun := g t
              left_inv := hleft t
              right_inv := hright t
              continuous_toFun := hfcont.comp (continuous_const.prodMk continuous_id)
              continuous_invFun := hgcont t }
            exact ⟨E, fun x => rfl⟩
          at_zero := by
            intro x
            exact hzero (pick x) x }
        refine ⟨H, hf, ?_⟩
        intro a t x
        change f (t, τ a x) = τ a (f (t, x))
        rw [hf (shift a (pick x)) t (τ a x) (hcell a (pick x) x (hpick x)),
          hf (pick x) t x (hpick x)]
        exact hequiv a (pick x) t x (hpick x)
      let E := (⋃ i, interior (K i))ᶜ
      let K' : Option ι → Set X := Option.elim' E K
      let e' : Option ι → Interval → X ≃ₜ X := fun i =>
        match i with
        | none => fun _ => Homeomorph.refl X
        | some i => e i
      have hEclosed : IsClosed E := isOpen_iUnion (fun _ => isOpen_interior) |>.isClosed_compl
      have hK'closed : ∀ i, IsClosed (K' i) := by
        intro i; cases i with
        | none => exact hEclosed
        | some i => exact hclosed i
      have hcover : ⋃ i, K' i = univ := by
        apply eq_univ_of_forall
        intro x
        by_cases hx : x ∈ ⋃ i, interior (K i)
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          exact mem_iUnion.mpr ⟨some i, interior_subset hi⟩
        · exact mem_iUnion.mpr ⟨none, hx⟩
      have hInvsupp (i : ι) (t : Interval) (x : X) (hx : x ∉ interior (K i)) :
          (e i t).symm x = x := by
        calc
          (e i t).symm x = (e i t).symm (e i t x) := congrArg (e i t).symm (hsupp i t x hx).symm
          _ = x := (e i t).symm_apply_apply x
      have hpres (i : Option ι) (t : Interval) : MapsTo (e' i t) (K' i) (K' i) := by
        cases i with
        | none => exact fun _ hx => hx
        | some i =>
          intro x hx
          by_contra hy
          have hyint : e i t x ∉ interior (K i) := fun h => hy (interior_subset h)
          have hh := hsupp i t (e i t x) hyint
          have heq : x = e i t x := (e i t).injective hh.symm
          exact hy (heq ▸ hx)
      have hpresInv (i : Option ι) (t : Interval) : MapsTo (e' i t).symm (K' i) (K' i) := by
        cases i with
        | none => exact fun _ hx => hx
        | some i =>
          intro x hx
          by_contra hy
          have hyint : (e i t).symm x ∉ interior (K i) := fun h => hy (interior_subset h)
          have hh := hInvsupp i t ((e i t).symm x) hyint
          have heq : x = (e i t).symm x := (e i t).symm.injective hh.symm
          exact hy (heq ▸ hx)
      have hmatch : ∀ i j t x, x ∈ K' i → x ∈ K' j → e' i t x = e' j t x := by
        intro i j t x hi hj
        cases i with
        | none =>
          cases j with
          | none => rfl
          | some j =>
            exact (hsupp j t x (fun h => hi (mem_iUnion.mpr ⟨j, h⟩))).symm
        | some i =>
          cases j with
          | none => exact hsupp i t x (fun h => hj (mem_iUnion.mpr ⟨i, h⟩))
          | some j =>
            by_cases hij : i = j
            · subst j; rfl
            · rw [hsupp i t x (hoverlap i j x hij hi hj),
                hsupp j t x (hoverlap j i x (Ne.symm hij) hj hi)]
      have hmatchInv : ∀ i j t x, x ∈ K' i → x ∈ K' j →
          (e' i t).symm x = (e' j t).symm x := by
        intro i j t x hi hj
        cases i with
        | none =>
          cases j with
          | none => rfl
          | some j =>
            exact (hInvsupp j t x (fun h => hi (mem_iUnion.mpr ⟨j, h⟩))).symm
        | some i =>
          cases j with
          | none => exact hInvsupp i t x (fun h => hj (mem_iUnion.mpr ⟨i, h⟩))
          | some j =>
            by_cases hij : i = j
            · subst j; rfl
            · rw [hInvsupp i t x (hoverlap i j x hij hi hj),
                hInvsupp j t x (hoverlap j i x (Ne.symm hij) hj hi)]
      let shift' : κ → Option ι → Option ι := fun a => Option.map (shift a)
      have hcell' : ∀ a i x, x ∈ K' i → τ a x ∈ K' (shift' a i) := by
        intro a i x hx
        cases i with
        | none => exact hexterior a x hx
        | some i => exact hcell a i x hx
      have hequiv' : ∀ a i t x, x ∈ K' i →
          e' (shift' a i) t (τ a x) = τ a (e' i t x) := by
        intro a i t x hx
        cases i with
        | none => rfl
        | some i => exact hequiv a i t x hx
      obtain ⟨H, hH, hHeq⟩  := glue K' hK'closed (hlf.option_elim' E) hcover e'
        (by intro i; cases i with
            | none => exact continuous_snd
            | some i => exact hc i)
        (by intro i; cases i with
            | none => exact fun _ => rfl
            | some i => exact hz i)
        hpres hpresInv hmatch hmatchInv τ shift' hcell' hequiv'
      exact ⟨H, fun i t x hx => hH (some i) t x hx,
        fun t x hx => hH none t x hx, hHeq⟩
    have latticeLF (K : Set Plane) (hK : IsCompact K) (T : ℝ) (hT : 0 < T) :
        LocallyFinite (fun n : ℤ × ℤ => (fun z : Plane => z+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)) '' K) := by
      have lattice (K : Set (ℝ × ℝ)) (hK : IsCompact K) (T : ℝ) (hT : 0 < T) :
        LocallyFinite (fun i : ℤ × ℤ =>
          (fun z : ℝ × ℝ => z + ((i.1 : ℝ) * T, (i.2 : ℝ) * T)) '' K) := by
      
        obtain ⟨M₀, hM₀⟩ := (hK.image (continuous_abs.comp continuous_fst)).bddAbove
        obtain ⟨M₁, hM₁⟩ := (hK.image (continuous_abs.comp continuous_snd)).bddAbove
        let M : ℝ := max (max M₀ M₁) 0
        have hb₀ (z : ℝ × ℝ) (hz : z ∈ K) : |z.1| ≤ M :=
          (hM₀ ⟨z, hz, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
        have hb₁ (z : ℝ × ℝ) (hz : z ∈ K) : |z.2| ≤ M :=
          (hM₁ ⟨z, hz, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
        intro x
        let U : Set (ℝ × ℝ) :=
          (Prod.fst ⁻¹' Ioo (x.1 - 1) (x.1 + 1)) ∩
          (Prod.snd ⁻¹' Ioo (x.2 - 1) (x.2 + 1))
        have hU : U ∈ 𝓝 x := by
          apply ((isOpen_Ioo.preimage continuous_fst).inter
            (isOpen_Ioo.preimage continuous_snd)).mem_nhds
          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        obtain ⟨N, hN⟩ := exists_nat_gt ((max |x.1| |x.2| + M + 1) / T)
        have hNT := (div_lt_iff₀ hT).mp hN
        refine ⟨U, hU, (Set.finite_Icc (-(N : ℤ), -(N : ℤ)) ((N : ℤ), (N : ℤ))).subset ?_⟩
        intro i hi
        obtain ⟨w, ⟨z, hz, rfl⟩, hw⟩ := hi
        have hz₀ := abs_le.mp (hb₀ z hz)
        have hz₁ := abs_le.mp (hb₁ z hz)
        have hw₀ : x.1 - 1 < z.1 + (i.1 : ℝ) * T ∧
            z.1 + (i.1 : ℝ) * T < x.1 + 1 := hw.1
        have hw₁ : x.2 - 1 < z.2 + (i.2 : ℝ) * T ∧
            z.2 + (i.2 : ℝ) * T < x.2 + 1 := hw.2
        have hi₀lo : -(N : ℝ) < (i.1 : ℝ) := by
          nlinarith [neg_abs_le x.1, le_max_left |x.1| |x.2|]
        have hi₀hi : (i.1 : ℝ) < (N : ℝ) := by
          nlinarith [le_abs_self x.1, le_max_left |x.1| |x.2|]
        have hi₁lo : -(N : ℝ) < (i.2 : ℝ) := by
          nlinarith [neg_abs_le x.2, le_max_right |x.1| |x.2|]
        have hi₁hi : (i.2 : ℝ) < (N : ℝ) := by
          nlinarith [le_abs_self x.2, le_max_right |x.1| |x.2|]
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · exact_mod_cast hi₀lo.le
        · exact_mod_cast hi₁lo.le
        · exact_mod_cast hi₀hi.le
        · exact_mod_cast hi₁hi.le
      let e : Plane ≃ₜ (ℝ × ℝ) := {
        toFun := fun z => (z 0,z 1)
        invFun := fun z => Plane.mk z.1 z.2
        left_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk]
        right_inv := by intro z; cases z; simp [Plane.mk]
        continuous_toFun := by fun_prop
        continuous_invFun := by
          apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
          apply continuous_pi
          intro i
          fin_cases i <;> fun_prop }
      have hf := lattice (e '' K) (hK.image e.continuous) T hT
      have hfp := hf.preimage_continuous e.continuous
      apply hfp.subset
      intro n
      rintro z ⟨w,hw,rfl⟩
      refine ⟨e w,mem_image_of_mem e hw,?_⟩
      simp [e,Plane.mk]
    have hδ (i j : ℤ × ℤ) : δ (i+j)=δ i+δ j := by
      ext k
      fin_cases k <;> simp [δ,Plane.mk,Int.cast_add] <;> ring
    let K : ℤ × ℤ → Set Plane := fun i => (Homeomorph.addRight (δ i)) '' D
    have hclosed (i : ℤ × ℤ) : IsClosed (K i) := (Homeomorph.addRight (δ i)).isClosedMap D hD.isClosed
    have hlf : LocallyFinite K := latticeLF D hD T hT
    have hdis (i j : ℤ × ℤ) (hij : i ≠ j) : Disjoint (K i) (K j) := by
      apply disjoint_left.mpr
      rintro z ⟨u,hu,he⟩ ⟨w,hw,hwe⟩
      have hji : j-i ≠ 0 := sub_ne_zero.mpr hij.symm
      apply disjoint_left.1 (hdeck (j-i) hji) hu
      refine ⟨w,hw,?_⟩
      change w+δ (j-i)=u
      apply add_right_cancel (b := δ i)
      calc
        (w+δ (j-i))+δ i = w+δ j := by rw [add_assoc,← hδ,sub_add_cancel]
        _ = u+δ i := hwe.trans he.symm
    choose E hE using H.homeomorphism_at
    let e : (ℤ × ℤ) → Interval → Plane ≃ₜ Plane := fun i t =>
      ((Homeomorph.addRight (-δ i)).trans (E t)).trans (Homeomorph.addRight (δ i))
    have he (i : ℤ × ℤ) (t : Interval) (z : Plane) :
        e i t z=H.map (t,z-δ i)+δ i := by
      change E t (z + -δ i)+δ i=_
      rw [hE]
      rfl
    have hsupp (i : ℤ × ℤ) (t : Interval) (z : Plane) (hz : z ∉ interior (K i)) : e i t z=z := by
      have hn : z-δ i ∉ interior D := by
        intro hh
        have hm : z ∈ (Homeomorph.addRight (δ i)) '' interior D := ⟨z-δ i,hh,by simp⟩
        rw [(Homeomorph.addRight (δ i)).image_interior] at hm
        exact hz hm
      rw [he,hH t _ hn]
      simp
    let τ : (ℤ × ℤ) → Plane → Plane := fun i z => z + δ i
    let shift : (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ) := fun i j => j+i
    have hcell (a i : ℤ × ℤ) (x : Plane) (hx : x ∈ K i) : τ a x ∈ K (shift a i) := by
      obtain ⟨u, hu, rfl⟩ := hx
      exact ⟨u, hu, by simp [τ, shift, K, hδ, add_assoc]⟩
    have hexterior (a : ℤ × ℤ) (x : Plane) (hx : x ∉ ⋃ i, interior (K i)) :
        τ a x ∉ ⋃ i, interior (K i) := by
      intro hh
      obtain ⟨i, hi⟩ := mem_iUnion.mp hh
      have himg : (Homeomorph.addRight (δ a)) '' K (i-a) = K i := by
        ext z
        constructor
        · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
          refine ⟨u, hu, ?_⟩
          have hda : δ (i-a) + δ a = δ i := by rw [← hδ, sub_add_cancel]
          simp [hda, add_assoc]
        · rintro ⟨u, hu, rfl⟩
          refine ⟨u+δ (i-a), ⟨u, hu, rfl⟩, ?_⟩
          have hda : δ (i-a) + δ a = δ i := by rw [← hδ, sub_add_cancel]
          simp [hda, add_assoc]
      have hi' : τ a x ∈ (Homeomorph.addRight (δ a)) '' interior (K (i-a)) := by
        rw [(Homeomorph.addRight (δ a)).image_interior, himg]
        exact hi
      obtain ⟨w, hw, heq⟩ := hi'
      have hwx : w = x := add_right_cancel heq
      exact hx (mem_iUnion.mpr ⟨i-a, hwx ▸ hw⟩)
    have hequiv (a i : ℤ × ℤ) (t : Interval) (x : Plane) (_hx : x ∈ K i) :
        e (shift a i) t (τ a x) = τ a (e i t x) := by
      rw [he, he]
      simp only [τ, shift, hδ]
      have ha : x + δ a - (δ i + δ a) = x - δ i := by abel
      rw [ha]
      abel
    have hcont : ∀ i, Continuous (fun p : Interval × Plane => e i p.1 p.2) := by
      intro i
      simp_rw [he]
      fun_prop
    have hzero : ∀ i x, e i ⟨0,by norm_num⟩ x=x := by
      intro i x
      rw [he,H.at_zero]
      simp
    obtain ⟨P,hP,hPfix,hPeq⟩ := supported (X := Plane) (ι := ℤ × ℤ) (κ := ℤ × ℤ) K hclosed hlf
      (fun i j x hij hi hj => False.elim (disjoint_left.1 (hdis i j hij) hi hj)) e
      hcont hzero
      hsupp τ shift hcell hexterior hequiv
    refine ⟨P,fun t i z => hPeq i t z,?_,?_⟩
    · intro t i z hz
      rw [hP i t (z+δ i) ⟨z,hz,rfl⟩,he]
      simp [δ]
    · intro t z hz
      apply hPfix t z
      intro hh
      apply hz
      obtain ⟨i,hi⟩ := mem_iUnion.mp hh
      apply mem_iUnion.mpr
      refine ⟨i,?_⟩
      rw [← (Homeomorph.addRight (δ i)).image_interior] at hi
      exact hi
  let D := φ '' Plane.closedSquare 0 1
  have hD : IsCompact D := (isCompact_closedSquare (0 : Plane) 1).image φ.continuous
  have hInt : interior D=φ '' Plane.openSquare 0 1 := by
    rw [← φ.image_interior,interior_closedSquare_zero_one]
  have hAD : A ⊆ D := by
    intro z hz
    by_cases he : z ∈ ({a,b} : Set Plane)
    · rcases he with he | he
      · have hzEq : z=a := he
        subst z
        exact ⟨φ.symm a,modelCurve_subset_closedSquare ha,φ.apply_symm_apply a⟩
      · have hzEq : z=b := he
        subst z
        exact ⟨φ.symm b,modelCurve_subset_closedSquare hb,φ.apply_symm_apply b⟩
    · obtain ⟨w,hw,hwe⟩ := hAi ⟨hz,he⟩
      exact ⟨w,mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hw).le,hwe⟩
  obtain ⟨H,hHAB,hHfix⟩ := crosscut φ A B a b hA hB ha hb hAi hBi
  have hHs : ∀ t z, z ∉ interior D → H.map (t,z)=z := by
    intro t z hz
    rw [hInt] at hz
    exact hHfix t z hz
  obtain ⟨P,hPer,hApply,hFix⟩ := periodicMove T hT D hD hdeck H hHs
  refine ⟨P,hPer,?_,?_⟩
  · intro i
    ext z
    constructor
    · rintro ⟨_,⟨w,hw,rfl⟩,rfl⟩
      have hm : H.finalMap w ∈ B := hHAB ▸ mem_image_of_mem H.finalMap hw
      change P.map (⟨1,by norm_num⟩,w+δ i) ∈ (fun z => z+δ i) '' B
      rw [hApply _ i w (hAD hw)]
      exact ⟨H.finalMap w,hm,rfl⟩
    · rintro ⟨w,hw,rfl⟩
      have hm : w ∈ H.finalMap '' A := hHAB.symm ▸ hw
      obtain ⟨q,hq,hqe⟩ := hm
      refine ⟨q+δ i,⟨q,hq,rfl⟩,?_⟩
      change P.map (⟨1,by norm_num⟩,q+δ i)=w+δ i
      rw [hApply _ i q (hAD hq)]
      exact congrArg (fun z : Plane => z+δ i) hqe
  · intro t z hz
    apply hFix t z
    simpa only [hInt] using hz

#print axioms periodic_chart_crosscut_isotopy
