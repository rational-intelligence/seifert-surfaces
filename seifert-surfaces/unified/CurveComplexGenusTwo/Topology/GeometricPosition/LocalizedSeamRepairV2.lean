import CurveComplexGenusTwo.Topology.GeometricPosition.FiniteSeamAvoidanceV2
import CurveComplexGenusTwo.Topology.GeometricPosition.CurveSubdivision

universe u
namespace CurveComplex.PositionUniverseV2
/-- Localize all equal-mesh seam motions in disjoint neighborhoods preserving
all assigned closed-piece chart containments throughout the ambient isotopy.
Incident charts and nonincident pieces are determined from the actual circle
parametrization; no support/compatibility witness is assumed. -/
theorem position_localized_seam_repair
    (S : Type u) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (J : Type*) [Fintype J] (r : J → Curve S)
    (c : Curve S) (n : ℕ) (hn : 2 ≤ n)
    (arc : Fin n → C(Interval, S))
    (harc : ∀ k t, arc k t = c.map (Circle.exp
      (-Real.pi + 2 * Real.pi * (((k.val : ℝ) + (t : ℝ)) / n))))
    (e : Fin n → OpenPartialHomeomorph S Schoenflies.Plane)
    (hchart : ∀ k, Set.range (arc k) ⊆ (e k).source)
    (W : Fin n → Set S) (hW : ∀ k, IsOpen (W k))
    (hseamW : ∀ k, arc k ⟨0, by norm_num⟩ ∈ W k) :
    ∃ U : Fin n → Set S, ∃ H : AmbientIsotopy S,
      (∀ k, IsOpen (U k)) ∧
      (∀ k, arc k ⟨0, by norm_num⟩ ∈ U k) ∧
      (∀ k, U k ⊆ W k) ∧
      (∀ k l, k ≠ l → Disjoint (U k) (U l)) ∧
      (∀ k i, arc k ⟨0, by norm_num⟩ ∈ Set.range (arc i) →
        U k ⊆ (e i).source) ∧
      (∀ k i, arc k ⟨0, by norm_num⟩ ∉ Set.range (arc i) →
        Disjoint (U k) (Set.range (arc i))) ∧
      (∀ k j, H.finalMap (arc k ⟨0, by norm_num⟩) ∉ (r j).image) ∧
      (∀ t x, x ∉ ⋃ k, U k → H.map (t, x) = x) ∧
      (∀ k t x, x ∈ U k → H.map (t, x) ∈ U k) ∧
      (∀ i t, (fun x => H.map (t, x)) '' Set.range (arc i) ⊆ (e i).source) := by
  classical
  haveI : T2Space S := inferInstance
  let p : Fin n → S := fun k => arc k ⟨0,by norm_num⟩
  have hpi : Function.Injective p := by
    have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    let θ : Fin n → ℝ := fun k => -Real.pi+2*Real.pi*((k.val:ℝ)/n)
    have hθ (k : Fin n) : θ k ∈ Set.Icc (-Real.pi)
        (-Real.pi+2*Real.pi*((n-1:ℝ)/n)) := by
      have hk : (k.val:ℝ) ≤ (n:ℝ)-1 := by
        have hh : k.val+1 ≤ n := Nat.succ_le_of_lt k.isLt
        have hhr : (k.val:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast hh
        linarith
      have hkn : (0:ℝ) ≤ k.val := Nat.cast_nonneg _
      have hl := div_nonneg hkn hn0.le
      have hu := div_le_div_of_nonneg_right hk hn0.le
      dsimp [θ]
      constructor <;> nlinarith [Real.pi_pos]
    have hlen : (-Real.pi+2*Real.pi*((n-1:ℝ)/n))-(-Real.pi) < 2*Real.pi := by
      have hratio : ((n:ℝ)-1)/n < 1 := (div_lt_one hn0).mpr (by linarith)
      nlinarith [Real.pi_pos]
    intro k l he
    change arc k ⟨0,by norm_num⟩ = arc l ⟨0,by norm_num⟩ at he
    simp only [harc,add_zero] at he
    have hh := Circle.exp_injOn_Icc hlen (hθ k) (hθ l) (c.embedded.injective he)
    have hdiv : (k.val:ℝ)/n = (l.val:ℝ)/n := by dsimp [θ] at hh; nlinarith [Real.pi_pos]
    have hkval : (k.val:ℝ) = l.val := (div_left_inj' hn0.ne').mp hdiv
    exact Fin.ext (Nat.cast_injective hkval)
  have hCclosed (i : Fin n) : IsClosed (Set.range (arc i)) :=
    (isCompact_range (arc i).continuous).isClosed
  let V : Fin n → Fin n → Set S := fun k i =>
    if p k ∈ Set.range (arc i) then (e i).source else (Set.range (arc i))ᶜ
  have hVopen (k i : Fin n) : IsOpen (V k i) := by
    dsimp [V]
    split
    · exact (e i).open_source
    · exact (hCclosed i).isOpen_compl
  have hpV (k i : Fin n) : p k ∈ V k i := by
    dsimp [V]
    split
    · rename_i h; exact hchart i h
    · assumption
  obtain ⟨D,hD,hDdis⟩ := (Set.finite_range p).t2_separation
  let U : Fin n → Set S := fun k => W k ∩ (D (p k) ∩ ⋂ i, V k i)
  have hUopen (k : Fin n) : IsOpen (U k) :=
    (hW k).inter ((hD (p k)).2.inter (isOpen_iInter_of_finite (hVopen k)))
  have hpU (k : Fin n) : p k ∈ U k :=
    ⟨hseamW k,(hD (p k)).1,Set.mem_iInter.mpr (hpV k)⟩
  have hUW (k : Fin n) : U k ⊆ W k := Set.inter_subset_left
  have hUdis (k l : Fin n) (hkl : k ≠ l) : Disjoint (U k) (U l) :=
    (hDdis (Set.mem_range_self k) (Set.mem_range_self l)
      (fun h => hkl (hpi h))).mono
      (fun x hx => hx.2.1) (fun x hx => hx.2.1)
  have hinc (k i : Fin n) (hki : p k ∈ Set.range (arc i)) : U k ⊆ (e i).source := by
    intro x hx
    have hv := Set.mem_iInter.mp hx.2.2 i
    simpa only [V,if_pos hki] using hv
  have hmiss (k i : Fin n) (hki : p k ∉ Set.range (arc i)) :
      Disjoint (U k) (Set.range (arc i)) := by
    rw [Set.disjoint_left]
    intro x hx hxi
    have hv := Set.mem_iInter.mp hx.2.2 i
    have hn : x ∉ Set.range (arc i) := by simpa only [V,if_neg hki,Set.mem_compl_iff] using hv
    exact hn hxi
  have hid : ∃ H : AmbientIsotopy S, ∀ t x, H.map (t,x) = x := by
    exact ⟨{ map := ⟨fun z => z.2, continuous_snd⟩,
              homeomorphism_at := fun t => ⟨Homeomorph.refl S,fun x => rfl⟩,
              at_zero := fun x => rfl },fun t x => rfl⟩
  have hcomp (H G : AmbientIsotopy S) :
      ∃ K : AmbientIsotopy S, ∀ t x, K.map (t,x) = G.map (t,H.map (t,x)) := by
    refine ⟨{ map := ⟨fun z => G.map (z.1,H.map z),
      G.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩,
              homeomorphism_at := ?_,at_zero := ?_ },fun t x => rfl⟩
    · intro t
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      obtain ⟨f,hf⟩ := G.homeomorphism_at t
      exact ⟨e.trans f,fun x => (hf (e x)).trans
        (congrArg (fun y => G.map (t,y)) (he x))⟩
    · intro x
      change G.map (⟨0,by norm_num⟩,H.map (⟨0,by norm_num⟩,x)) = x
      rw [H.at_zero,G.at_zero]
  have hstay (G : AmbientIsotopy S) (k : Fin n)
      (hfix : ∀ t x, x ∉ U k → G.map (t,x) = x) :
      ∀ t x, x ∈ U k → G.map (t,x) ∈ U k := by
    intro t x hx
    by_contra hn
    obtain ⟨e,he⟩ := G.homeomorphism_at t
    have heq : e (G.map (t,x)) = e x := by
      rw [he,he]
      exact hfix t (G.map (t,x)) hn
    exact hn ((e.injective heq).symm ▸ hx)
  have hbuild (P : Finset (Fin n)) : ∃ H : AmbientIsotopy S,
      (∀ k ∈ P, ∀ j, H.finalMap (p k) ∉ (r j).image) ∧
      (∀ t x, x ∉ ⋃ k, U k → H.map (t,x) = x) ∧
      (∀ k t x, x ∈ U k → H.map (t,x) ∈ U k) ∧
      (∀ k, k ∉ P → ∀ t, H.map (t,p k) = p k) := by
    induction P using Finset.induction_on with
    | empty =>
      obtain ⟨H,hH⟩ := hid
      refine ⟨H,by simp,?_,?_,?_⟩
      · intro t x hx; exact hH t x
      · intro k t x hx; rwa [hH]
      · intro k hk t; exact hH t (p k)
    | @insert k P hkP ih =>
      obtain ⟨H,hHavoid,hHfix,hHstay,hHunprocessed⟩ := ih
      obtain ⟨G,hGavoid,hGfix⟩ := position_finite_seam_avoidance S J r
        {p k} (U k) (hUopen k) (by
          intro x hx
          have hxpk : x = p k := Finset.mem_singleton.mp hx
          exact hxpk.symm ▸ hpU k)
      have hGstay := hstay G k hGfix
      obtain ⟨K,hK⟩ := hcomp H G
      refine ⟨K,?_,?_,?_,?_⟩
      · intro l hl j
        rw [AmbientIsotopy.finalMap,hK]
        change G.finalMap (H.finalMap (p l)) ∉ (r j).image
        rcases Finset.mem_insert.mp hl with rfl | hlP
        · have hHpk : H.finalMap (p l) = p l := hHunprocessed l hkP ⟨1,by norm_num⟩
          rw [hHpk]
          exact hGavoid (p l) (Finset.mem_singleton_self _) j
        · have hlk : l ≠ k := by intro he; exact hkP (he ▸ hlP)
          have hpHU : H.finalMap (p l) ∈ U l := hHstay l ⟨1,by norm_num⟩ (p l) (hpU l)
          have hnUk : H.finalMap (p l) ∉ U k := fun hm =>
            Set.disjoint_left.mp (hUdis l k hlk) hpHU hm
          have hGsame : G.finalMap (H.finalMap (p l)) = H.finalMap (p l) :=
            hGfix ⟨1,by norm_num⟩ _ hnUk
          rw [hGsame]
          exact hHavoid l hlP j
      · intro t x hx
        rw [hK,hHfix t x hx]
        apply hGfix
        intro hxk
        exact hx (Set.mem_iUnion.mpr ⟨k,hxk⟩)
      · intro l t x hx
        rw [hK]
        have hxHU := hHstay l t x hx
        by_cases hlk : l = k
        · subst l; exact hGstay t _ hxHU
        · have hnUk : H.map (t,x) ∉ U k := fun hm =>
            Set.disjoint_left.mp (hUdis l k hlk) hxHU hm
          rw [hGfix t _ hnUk]
          exact hxHU
      · intro l hl t
        have hlP : l ∉ P := fun h => hl (Finset.mem_insert_of_mem h)
        have hlk : l ≠ k := by intro h; exact hl (h ▸ Finset.mem_insert_self k P)
        rw [hK,hHunprocessed l hlP t]
        apply hGfix
        exact fun hm => Set.disjoint_left.mp (hUdis l k hlk) (hpU l) hm
  obtain ⟨H,hHavoid,hHfix,hHstay,hHunprocessed⟩ := hbuild Finset.univ
  refine ⟨U,H,hUopen,hpU,hUW,hUdis,hinc,hmiss,?_,hHfix,hHstay,?_⟩
  · intro k j; exact hHavoid k (Finset.mem_univ k) j
  · intro i t y hy
    obtain ⟨x,hx,rfl⟩ := hy
    by_cases hxU : x ∈ ⋃ k, U k
    · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hxU
      have hpC : p k ∈ Set.range (arc i) := by
        by_contra hn
        exact Set.disjoint_left.mp (hmiss k i hn) hk hx
      exact hinc k i hpC (hHstay k t x hk)
    · change H.map (t,x) ∈ (e i).source
      rw [hHfix t x hxU]
      exact hchart i hx

end CurveComplex.PositionUniverseV2
