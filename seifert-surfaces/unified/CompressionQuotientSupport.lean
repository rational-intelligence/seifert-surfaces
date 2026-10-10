import CompressionContracts
open scoped Manifold ContDiff BigOperators
open Set Topology TopologicalSpace
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma capEdge_injective : Function.Injective CompressionAnnulus.capEdge := by
  intro z w h
  apply Subtype.ext
  apply Complex.ext
  · have hh := congrArg (fun v : ClosedDisk => (v : Euc 2) 0) h
    simpa [CompressionAnnulus.capEdge, circleVector, PiLp.single_apply] using hh
  · have hh := congrArg (fun v : ClosedDisk => (v : Euc 2) 1) h
    simpa [CompressionAnnulus.capEdge, circleVector, PiLp.single_apply] using hh

namespace CompressionQuotientSupport
variable {S : CompactOrientedSurface.{0}} {M : Type}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  {f : NeatEmbedding S M} {D : InteriorCompressingDisk f} (A : CompressionAnnulus D)

private def rawRetract : (A.Remainder ⊕ (Fin 2 × ClosedDisk)) → A.Remainder
  | .inl x => x
  | .inr (k,x) => A.edgePoint k (Function.invFun CompressionAnnulus.capEdge x)

private def setRetract : A.SurgerySpace → A.Remainder :=
  Quot.lift (rawRetract A) (by
    intro a b h
    cases h with
    | attach k z =>
      change A.edgePoint k z = A.edgePoint k
        (Function.invFun CompressionAnnulus.capEdge (CompressionAnnulus.capEdge z))
      rw [Function.leftInverse_invFun capEdge_injective z])

lemma remainderInclusion_injective : Function.Injective A.remainderInclusion := by
  intro x y h
  exact congrArg (setRetract A) h

lemma continuous_remainderInclusion : Continuous A.remainderInclusion :=
  continuous_quot_mk.comp continuous_inl

lemma continuous_capInclusion (k : Fin 2) : Continuous (A.capInclusion k) :=
  continuous_quot_mk.comp (continuous_inr.comp (continuous_const.prodMk continuous_id))

lemma attach_eq (k : Fin 2) (z : Circle) :
    A.remainderInclusion (A.edgePoint k z) = A.capInclusion k (CompressionAnnulus.capEdge z) :=
  Quot.sound (.attach k z)

lemma boundary_remains (x : S) (hx : x ∈ S.boundary) : x ∈ A.removedᶜ := by
  rintro ⟨p,hp,hpx⟩
  exact A.interior_surface ⟨p,hpx⟩ hx


noncomputable def boundaryMap (P : SmoothCompressionSurface A) : ↥S.boundary → ↥P.surface.boundary :=
  fun x => ⟨P.realization.symm (A.remainderInclusion ⟨x.val,boundary_remains A x.val x.property⟩),
    (P.boundary_matches _).mpr x.property⟩

lemma boundaryMap_continuous (P : SmoothCompressionSurface A) : Continuous (boundaryMap A P) := by
  apply Continuous.subtype_mk
  exact P.realization.symm.continuous.comp ((continuous_remainderInclusion A).comp
    (continuous_subtype_val.subtype_mk _))

lemma boundaryMap_injective (P : SmoothCompressionSurface A) : Function.Injective (boundaryMap A P) := by
  intro x y h
  apply Subtype.ext
  have hr := (remainderInclusion_injective A)
    (P.realization.symm.injective (congrArg Subtype.val h))
  exact congrArg (fun r : A.Remainder => (r : S)) hr

lemma boundaryMap_surjective (P : SmoothCompressionSurface A) : Function.Surjective (boundaryMap A P) := by
  intro y
  have hy : P.realization.symm (P.realization y.val) ∈ P.surface.boundary := by
    simpa only [Homeomorph.symm_apply_apply] using y.property
  obtain ⟨r,hr⟩ := Quot.exists_rep (P.realization y.val)
  cases r with
  | inl x =>
    have heq : A.remainderInclusion x = P.realization y.val := hr
    have hx : (x : S) ∈ S.boundary := (P.boundary_matches x).mp (heq ▸ hy)
    refine ⟨⟨x.val,hx⟩,?_⟩
    apply Subtype.ext
    change P.realization.symm (A.remainderInclusion _) = y.val
    simpa only [Homeomorph.symm_apply_apply] using congrArg P.realization.symm heq
  | inr kx =>
    have heq : A.capInclusion kx.1 kx.2 = P.realization y.val := hr
    exact False.elim ((P.caps_interior kx.1 kx.2) (heq ▸ hy))

noncomputable def boundaryHomeomorph (P : SmoothCompressionSurface A) :
    ↥S.boundary ≃ₜ ↥P.surface.boundary := by
  letI : CompactSpace ↥S.boundary := isCompact_iff_compactSpace.mp
    ((𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by decide)).isCompact
  let e := Equiv.ofBijective (boundaryMap A P)
    ⟨boundaryMap_injective A P,boundaryMap_surjective A P⟩
  exact (boundaryMap_continuous A P).homeoOfEquivCompactToT2 (f := e)

noncomputable def connectedComponentsEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y :=
  Quotient.congr e.toEquiv (by
    intro x y
    change connectedComponent x = connectedComponent y ↔ connectedComponent (e x) = connectedComponent (e y)
    rw [← ConnectedComponents.coe_eq_coe, ← ConnectedComponents.coe_eq_coe]
    rw [ConnectedComponents.coe_eq_coe',ConnectedComponents.coe_eq_coe']
    constructor
    · intro h
      exact e.continuous.mapsTo_connectedComponent y h
    · intro h
      simpa only [Homeomorph.symm_apply_apply] using e.symm.continuous.mapsTo_connectedComponent (e y) h)

lemma boundaryCount_preserved (P : SmoothCompressionSurface A) : boundaryCount P.surface = boundaryCount S := by
  exact (Nat.card_congr (connectedComponentsEquiv (boundaryHomeomorph A P))).symm

end CompressionQuotientSupport
