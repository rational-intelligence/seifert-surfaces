import CurveComplexGenusTwo.Topology.GeometricPosition.PointAvoidCurveV2
universe u
namespace CurveComplex.PositionUniverseV2
/-- Move every point in a specified finite seam set off a fixed finite curve
family, with support in any prescribed open neighborhood of the seams. -/
theorem position_finite_seam_avoidance
    (S : Type u) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (J : Type*) [Fintype J] (r : J → Curve S)
    (P : Finset S) (W : Set S) (hW : IsOpen W) (hPW : (P : Set S) ⊆ W) :
    ∃ H : AmbientIsotopy S,
      (∀ p ∈ P, ∀ j, H.finalMap p ∉ (r j).image) ∧
      (∀ t x, x ∉ W → H.map (t, x) = x) := by
  classical
  have hid : ∃ H : AmbientIsotopy S, ∀ t x, H.map (t, x) = x := by
    refine ⟨{ map := ⟨fun z => z.2, continuous_snd⟩,
              homeomorphism_at := fun t => ⟨Homeomorph.refl S, fun x => rfl⟩,
              at_zero := fun x => rfl }, fun t x => rfl⟩
  have hcomp (H G : AmbientIsotopy S) :
      ∃ K : AmbientIsotopy S, ∀ t x, K.map (t, x) = G.map (t, H.map (t, x)) := by
    refine ⟨{ map := ⟨fun z => G.map (z.1, H.map z),
      G.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩,
              homeomorphism_at := ?_, at_zero := ?_ }, fun t x => rfl⟩
    · intro t
      obtain ⟨e, he⟩ := H.homeomorphism_at t
      obtain ⟨f, hf⟩ := G.homeomorphism_at t
      exact ⟨e.trans f, fun x => (hf (e x)).trans (congrArg (fun y => G.map (t,y)) (he x))⟩
    · intro x
      change G.map (⟨0, by norm_num⟩, H.map (⟨0, by norm_num⟩, x)) = x
      rw [H.at_zero, G.at_zero]
  have hstay (H : AmbientIsotopy S) (A : Set S)
      (hfix : ∀ t x, x ∉ A → H.map (t, x) = x)
      (p : S) (hp : p ∈ A) : H.finalMap p ∈ A := by
    by_contra hn
    obtain ⟨e, he⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
    have hh : e (H.finalMap p) = e p := by
      rw [he, he]
      exact hfix ⟨1, by norm_num⟩ _ hn
    have hpq := e.injective hh
    exact hn (hpq.symm ▸ hp)
  have havoid (H : AmbientIsotopy S) (A : Set S)
      (hfix : ∀ x ∈ A, H.finalMap x = x)
      (p : S) (hp : p ∉ A) : H.finalMap p ∉ A := by
    intro hmem
    obtain ⟨e, he⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
    have hh : e (H.finalMap p) = e p := by
      rw [he, he]
      exact hfix _ hmem
    exact hp ((e.injective hh) ▸ hmem)
  have hpointFamily (B : Finset J) (p : S) (V : Set S)
      (hV : IsOpen V) (hpV : p ∈ V) :
      ∃ H : AmbientIsotopy S,
        (∀ j ∈ B, H.finalMap p ∉ (r j).image) ∧
        ∀ t x, x ∉ V → H.map (t,x) = x := by
    induction B using Finset.induction_on generalizing p V with
    | empty =>
      obtain ⟨H, hH⟩ := hid
      exact ⟨H, by simp, fun t x _ => hH t x⟩
    | @insert j B hjB ih =>
      obtain ⟨H, hH, hHfix⟩ := ih p V hV hpV
      let q := H.finalMap p
      have hqV : q ∈ V := hstay H V hHfix p hpV
      by_cases hqj : q ∈ (r j).image
      · let old : Set S := ⋃ k ∈ B, (r k).image
        have hclosed : IsClosed old := isClosed_biUnion_finset (fun k hk =>
          (isCompact_range (r k).embedded.continuous).isClosed)
        have hqold : q ∉ old := by
          intro h
          obtain ⟨k, hk, hqk⟩ := Set.mem_iUnion₂.mp h
          exact hH k hk hqk
        let V' := V ∩ oldᶜ
        obtain ⟨G, hGq, hGfix⟩ := position_point_off_curve S (r j) q hqj
          V' (hV.inter hclosed.isOpen_compl) ⟨hqV, hqold⟩
        obtain ⟨K, hK⟩ := hcomp H G
        refine ⟨K, ?_, ?_⟩
        · intro k hk
          rw [AmbientIsotopy.finalMap, hK]
          change G.finalMap q ∉ (r k).image
          rcases Finset.mem_insert.mp hk with rfl | hkB
          · exact hGq
          · apply havoid G (r k).image ?_ q (hH k hkB)
            intro x hx
            apply hGfix
            intro hV'x
            exact hV'x.2 (Set.mem_iUnion₂.mpr ⟨k, hkB, hx⟩)
        · intro t x hx
          rw [hK, hHfix t x hx]
          apply hGfix
          exact fun h => hx h.1
      · refine ⟨H, ?_, hHfix⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hkB
        · exact hqj
        · exact hH k hkB
  induction P using Finset.induction_on with
  | empty =>
    obtain ⟨H, hH⟩ := hid
    exact ⟨H, by simp, fun t x _ => hH t x⟩
  | @insert p P hpP ih =>
    have hPW' : (P : Set S) ⊆ W := fun x hx => hPW (Finset.mem_insert_of_mem hx)
    obtain ⟨H, hH, hHfix⟩ := ih hPW'
    let q := H.finalMap p
    have hpW : p ∈ W := hPW (Finset.mem_insert_self _ _)
    have hqW : q ∈ W := hstay H W hHfix p hpW
    let old : Set S := H.finalMap '' (P : Set S)
    have holdfinite : old.Finite := P.finite_toSet.image _
    have hqold : q ∉ old := by
      rintro ⟨x, hx, hxq⟩
      obtain ⟨e, he⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
      have heq : e x = e p := by simpa only [he, q, AmbientIsotopy.finalMap] using hxq
      exact hpP ((e.injective heq) ▸ hx)
    let V := W ∩ oldᶜ
    obtain ⟨G, hG, hGfix⟩ := hpointFamily Finset.univ q V
      (hW.inter holdfinite.isClosed.isOpen_compl) ⟨hqW, hqold⟩
    obtain ⟨K, hK⟩ := hcomp H G
    refine ⟨K, ?_, ?_⟩
    · intro x hx j
      rw [AmbientIsotopy.finalMap, hK]
      change G.finalMap (H.finalMap x) ∉ (r j).image
      rcases Finset.mem_insert.mp hx with rfl | hxP
      · exact hG j (Finset.mem_univ _)
      · have hfixq : G.finalMap (H.finalMap x) = H.finalMap x := by
          apply hGfix
          intro hxV
          exact hxV.2 ⟨x, hxP, rfl⟩
        rw [hfixq]
        exact hH x hxP j
    · intro t x hx
      rw [hK, hHfix t x hx]
      apply hGfix
      exact fun h => hx h.1
end CurveComplex.PositionUniverseV2
