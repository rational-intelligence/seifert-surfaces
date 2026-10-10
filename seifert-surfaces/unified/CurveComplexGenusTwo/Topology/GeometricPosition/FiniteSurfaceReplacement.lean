import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import CurveComplexGenusTwo.Topology.IsotopyCurveTransport
namespace CurveComplex
open Set Schoenflies
/-- Replace finitely many actual horizontal crosscut subarcs in mutually disjoint
surface chart patches. The whole essential curve has exactly the selected
subarcs removed and the prescribed proper target arcs inserted. -/
theorem position_finite_surface_replacement
    (S : Type*) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (c : EssentialCurve S) (K : Type*) [Fintype K]
    (E : K → OpenPartialHomeomorph S Schoenflies.Plane)
    (hdis : ∀ i j, i ≠ j → Disjoint (E i).source (E j).source)
    (hSquare : ∀ k, Schoenflies.Plane.closedSquare 0 1 ⊆ (E k).target)
    (A : Set Schoenflies.Plane)
    (hA : Schoenflies.IsArcBetween A (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0))
    (hAi : A \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆
      Schoenflies.Plane.openSquare 0 1)
    (hc : ∀ k, {x : S | x ∈ (E k).source ∧ E k x ∈ Schoenflies.Plane.closedSquare 0 1} ∩
      c.val.image = {x : S | x ∈ (E k).source ∧ E k x ∈ A})
    (B : K → Set Schoenflies.Plane)
    (hB : ∀ k, Schoenflies.IsArcBetween (B k)
      (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0))
    (hBi : ∀ k, B k \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆
      Schoenflies.Plane.openSquare 0 1) :
    ∃ H : AmbientIsotopy S, ∃ d : EssentialCurve S,
      d.val.image = H.finalMap '' c.val.image ∧
      Quotient.mk (essentialCurveSetoid S) d = Quotient.mk (essentialCurveSetoid S) c ∧
      d.val.image =
        (c.val.image \ ⋃ k, {x : S | x ∈ (E k).source ∧ E k x ∈ A}) ∪
        ⋃ k, {x : S | x ∈ (E k).source ∧ E k x ∈ B k} := by
  classical
  let Ap : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ A}
  let Bp : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ B k}
  let Dp : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ Plane.openSquare 0 1}
  have hAsquare : A ⊆ Plane.closedSquare 0 1 := by
    intro z hz
    by_cases he : z ∈ ({Plane.mk (-1) 0,Plane.mk 1 0} : Set Plane)
    · rcases he with rfl | he
      · norm_num [Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk]
      · rw [Set.mem_singleton_iff.mp he]
        norm_num [Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk]
    · exact Plane.openSquare_subset_closedSquare 0 1 (hAi ⟨hz,he⟩)
  have hApcurve (k : K) : Ap k ⊆ c.val.image := by
    intro z hz
    have hh : z ∈ {x : S | x ∈ (E k).source ∧ E k x ∈ Plane.closedSquare 0 1} ∩ c.val.image := by
      rw [hc k]
      exact hz
    exact hh.2
  have hDcurve (k : K) : Dp k ∩ c.val.image ⊆ Ap k := by
    intro x hx
    change x ∈ {x : S | x ∈ (E k).source ∧ E k x ∈ A}
    rw [← hc k]
    exact ⟨⟨hx.1.1,Plane.openSquare_subset_closedSquare 0 1 hx.1.2⟩,hx.2⟩
  have hPull (k : K) (F : Set Plane) :
      {x : S | ∃ u : (E k).source, u.val = x ∧
        ((E k).toHomeomorphSourceTarget u : Plane) ∈ F} =
      {x : S | x ∈ (E k).source ∧ E k x ∈ F} := by
    ext x
    constructor
    · rintro ⟨u,rfl,hu⟩
      exact ⟨u.property,hu⟩
    · intro hx
      exact ⟨⟨x,hx.1⟩,rfl,hx.2⟩
  have hpatch (k : K) : ∃ G : AmbientIsotopy S,
      G.finalMap '' Ap k = Bp k ∧ ∀ t x, x ∉ Dp k → G.map (t,x) = x := by
    obtain ⟨G,hGA,hGfix⟩ := position_crosscut_surface_square_support S
      (E k).source (E k).target (E k).open_source (E k).toHomeomorphSourceTarget
      (hSquare k) A (B k) (Plane.mk (-1) 0) (Plane.mk 1 0) hA (hB k)
      (by norm_num [modelCurve,Plane.supNorm,Plane.mk])
      (by norm_num [modelCurve,Plane.supNorm,Plane.mk]) hAi (hBi k)
    rw [hPull,hPull] at hGA
    simp only [hPull] at hGfix
    exact ⟨G,hGA,hGfix⟩
  choose G hGA hGfix using hpatch
  have hfixRest (k : K) (x : S) (hx : x ∈ c.val.image \ Ap k) : (G k).finalMap x = x := by
    apply hGfix k ⟨1,by norm_num⟩
    intro hD
    exact hx.2 (hDcurve k ⟨hD,hx.1⟩)
  have hfixOther (k j : K) (hkj : k ≠ j) (x : S) (hx : x ∈ (E j).source) :
      (G k).finalMap x = x := by
    apply hGfix k ⟨1,by norm_num⟩
    intro hD
    exact Set.disjoint_left.mp (hdis k j hkj) hD.1 hx
  have hcompose (H G : AmbientIsotopy S) :
      ∃ K : AmbientIsotopy S, ∀ t x, K.map (t,x) = G.map (t,H.map (t,x)) := by
    refine ⟨{
      map := ⟨fun z => G.map (z.1,H.map z),
      G.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩,
      homeomorphism_at := ?_, at_zero := ?_ },fun _ _ => rfl⟩
    · intro t
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      obtain ⟨f,hf⟩ := G.homeomorphism_at t
      exact ⟨e.trans f,fun x => (hf (e x)).trans
        (congrArg (fun z => G.map (t,z)) (he x))⟩
    · intro x
      change G.map (⟨0,by norm_num⟩,H.map (⟨0,by norm_num⟩,x)) = x
      rw [H.at_zero,G.at_zero]
  let As : Finset K → Set S := fun P => ⋃ k ∈ P, Ap k
  let Bs : Finset K → Set S := fun P => ⋃ k ∈ P, Bp k
  have hbuild (P : Finset K) : ∃ H : AmbientIsotopy S,
      H.finalMap '' c.val.image = (c.val.image \ As P) ∪ Bs P := by
    induction P using Finset.induction_on with
    | empty =>
      let H : AmbientIsotopy S := {
        map := ⟨fun z => z.2,continuous_snd⟩
        homeomorphism_at := fun _ => ⟨Homeomorph.refl S,fun _ => rfl⟩
        at_zero := fun _ => rfl }
      refine ⟨H,?_⟩
      change (fun x : S => x) '' c.val.image = _
      simp [As,Bs]
    | @insert k P hk ih =>
      obtain ⟨H,hH⟩ := ih
      have hAsinsert : As (insert k P) = Ap k ∪ As P := by simp [As]
      have hBsinsert : Bs (insert k P) = Bp k ∪ Bs P := by simp [Bs]
      have hnotAs (x : S) (hx : x ∈ Ap k) : x ∉ As P := by
        intro h
        obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp h
        have hkj : k ≠ j := fun he => hk (he.symm ▸ hj)
        exact Set.disjoint_left.mp (hdis k j hkj) hx.1 hxj.1
      let R : Set S := (c.val.image \ As (insert k P)) ∪ Bs P
      have hdecomp : (c.val.image \ As P) ∪ Bs P = Ap k ∪ R := by
        ext x
        constructor
        · intro hx
          rcases hx with hx | hx
          · by_cases hxA : x ∈ Ap k
            · exact Or.inl hxA
            · exact Or.inr (Or.inl ⟨hx.1,by rw [hAsinsert]; exact fun h => h.elim hxA hx.2⟩)
          · exact Or.inr (Or.inr hx)
        · intro hx
          rcases hx with hx | hx
          · exact Or.inl ⟨hApcurve k hx,hnotAs x hx⟩
          · rcases hx with hx | hx
            · exact Or.inl ⟨hx.1,fun h => hx.2 (hAsinsert.symm ▸ Or.inr h)⟩
            · exact Or.inr hx
      have hRfix (x : S) (hx : x ∈ R) : (G k).finalMap x = x := by
        rcases hx with hx | hx
        · apply hfixRest k x
          refine ⟨hx.1,?_⟩
          intro h
          exact hx.2 (hAsinsert.symm ▸ Or.inl h)
        · obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp hx
          exact hfixOther k j (fun he => hk (he.symm ▸ hj)) x hxj.1
      have hGR : (G k).finalMap '' R = R := by
        ext x
        constructor
        · rintro ⟨y,hy,rfl⟩
          simpa [hRfix y hy] using hy
        · intro hx
          exact ⟨x,hx,hRfix x hx⟩
      have hnew : (G k).finalMap '' ((c.val.image \ As P) ∪ Bs P) =
          (c.val.image \ As (insert k P)) ∪ Bs (insert k P) := by
        rw [hdecomp,Set.image_union,hGA k,hGR,hBsinsert]
        change Bp k ∪ ((c.val.image \ As (insert k P)) ∪ Bs P) =
          (c.val.image \ As (insert k P)) ∪ (Bp k ∪ Bs P)
        ext x
        simp only [Set.mem_union]
        tauto
      obtain ⟨F,hF⟩ := hcompose H (G k)
      refine ⟨F,?_⟩
      have hmaps : F.finalMap = (G k).finalMap ∘ H.finalMap :=
        funext (hF ⟨1,by norm_num⟩)
      calc
        F.finalMap '' c.val.image = (G k).finalMap '' (H.finalMap '' c.val.image) := by
          rw [Set.image_image,hmaps]
          rfl
        _ = _ := by rw [hH,hnew]
  obtain ⟨H,hH⟩ := hbuild Finset.univ
  obtain ⟨d,hd,hclass⟩ := position_essential_curve_of_isotopy H c
  refine ⟨H,d,hd,hclass,?_⟩
  rw [hd,hH]
  simp [As,Bs,Ap,Bp]


end CurveComplex
