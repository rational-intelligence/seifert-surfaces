import CurveComplexGenusTwo.Filtration.FiltrationRelative

namespace CurveGenusTwo.Filtration

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

/-- Inclusion of finite complexes on the exact-support relative chains. -/
noncomputable def relativeChainInclusion (K L : FiniteComplex V)
    (a : ArcLabels V B) (h : K.simplices ⊆ L.simplices)
    (p : ℕ) (n : ℤ) :
    relativeChains K a p n →+ relativeChains L a p n :=
  FreeAbelianGroup.lift fun σ =>
    FreeAbelianGroup.of
      (⟨⟨σ.1.1, h σ.1.2.1, σ.1.2.2⟩, σ.2⟩ : RelativeSimplexAt L a p n)

omit [LinearOrder V] in
private theorem relativeChainInclusion_of (K L : FiniteComplex V)
    (a : ArcLabels V B) (h : K.simplices ⊆ L.simplices)
    (p : ℕ) (n : ℤ) (σ : RelativeSimplexAt K a p n) :
    relativeChainInclusion K L a h p n (FreeAbelianGroup.of σ) =
      FreeAbelianGroup.of
        (⟨⟨σ.1.1, h σ.1.2.1, σ.1.2.2⟩, σ.2⟩ : RelativeSimplexAt L a p n) := by
  exact FreeAbelianGroup.lift_apply_of _ _

set_option backward.isDefEq.respectTransparency false

/-- The relative differential commutes with inclusion of finite complexes. -/
theorem relativeChainInclusion_boundary (K L : FiniteComplex V)
    (a : ArcLabels V B) (h : K.simplices ⊆ L.simplices)
    (p : ℕ) (n : ℤ) :
    (relativeBoundary L a p n).comp (relativeChainInclusion K L a h p n) =
      (relativeChainInclusion K L a h p (n - 1)).comp
        (relativeBoundary K a p n) := by
  classical
  apply FreeAbelianGroup.lift_ext
  intro σ
  change relativeBoundary L a p n
      (relativeChainInclusion K L a h p n (FreeAbelianGroup.of σ)) =
    relativeChainInclusion K L a h p (n - 1)
      (relativeBoundary K a p n (FreeAbelianGroup.of σ))
  let τ : RelativeSimplexAt L a p n :=
    ⟨⟨σ.1.1, h σ.1.2.1, σ.1.2.2⟩, σ.2⟩
  rw [relativeChainInclusion_of]
  change relativeBoundary L a p n (FreeAbelianGroup.of τ) =
    relativeChainInclusion K L a h p (n - 1)
      (relativeBoundary K a p n (FreeAbelianGroup.of σ))
  rw [show relativeBoundary L a p n (FreeAbelianGroup.of τ) =
      relativeFaceBoundary L a p n τ by simp [relativeBoundary],
    show relativeBoundary K a p n (FreeAbelianGroup.of σ) =
      relativeFaceBoundary K a p n σ by simp [relativeBoundary]]
  unfold relativeFaceBoundary
  rw [map_sum]
  simp only [show τ.1.1 = σ.1.1 from rfl]
  apply Finset.sum_congr rfl
  intro v hv
  split
  · next hvL =>
    split
    · next hvK =>
      rw [map_zsmul, relativeChainInclusion_of]
    · next hvK =>
      exfalso
      apply hvK
      exact ⟨⟨K.down_closed (Finset.erase_subset v σ.1.1) σ.1.2.1,
        hvL.1.2⟩, hvL.2⟩
  · next hvL =>
    split
    · next hvK =>
      exfalso
      apply hvL
      exact ⟨⟨h hvK.1.1, hvK.1.2⟩, hvK.2⟩
    · next hvK => simp

/-- Relative cycles at an integral filtration degree. -/
noncomputable def relativeCycles (K : FiniteComplex V) (a : ArcLabels V B)
    (p : ℕ) (n : ℤ) : AddSubgroup (relativeChains K a p n) :=
  (relativeBoundary K a p n).ker

/-- The image of a relative differential consists of cycles. -/
theorem relativeBoundary_range_le_cycles (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) :
    (relativeBoundary K a p n).range ≤ relativeCycles K a p (n - 1) := by
  intro c hc
  obtain ⟨d, rfl⟩ := hc
  change relativeBoundary K a p (n - 1) (relativeBoundary K a p n d) = 0
  have hs := congrArg (fun f => f d)
    (relative_boundary_boundary K a p n)
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply] using hs

/-- Homology at degree `n - 1` of the exact-support relative chain complex. -/
noncomputable abbrev filtrationRelativeHomologyShifted (K : FiniteComplex V)
    (a : ArcLabels V B) (p : ℕ) (n : ℤ) : Type u :=
  (relativeCycles K a p (n - 1)) ⧸
    ((relativeBoundary K a p n).range.comap
      (relativeCycles K a p (n - 1)).subtype)

/-- Inclusion restricts to relative cycles. -/
noncomputable def relativeCyclesInclusion (K L : FiniteComplex V)
    (a : ArcLabels V B) (h : K.simplices ⊆ L.simplices)
    (p : ℕ) (n : ℤ) :
    relativeCycles K a p n →+ relativeCycles L a p n where
  toFun c := ⟨relativeChainInclusion K L a h p n c.1, by
    have hc : relativeBoundary K a p n c.1 = 0 := c.2
    have hn := congrArg (fun f => f c.1)
      (relativeChainInclusion_boundary K L a h p n)
    change relativeBoundary L a p n
        (relativeChainInclusion K L a h p n c.1) =
      relativeChainInclusion K L a h p (n - 1)
        (relativeBoundary K a p n c.1) at hn
    change relativeBoundary L a p n
      (relativeChainInclusion K L a h p n c.1) = 0
    rw [hn, hc, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)

/-- Inclusion induces a map on exact-support relative homology. -/
noncomputable def filtrationRelativeHomologyMapShifted (K L : FiniteComplex V)
    (a : ArcLabels V B) (h : K.simplices ⊆ L.simplices)
    (p : ℕ) (n : ℤ) :
    filtrationRelativeHomologyShifted K a p n →+
      filtrationRelativeHomologyShifted L a p n := by
  let f := relativeCyclesInclusion K L a h p (n - 1)
  let H := (relativeBoundary L a p n).range.comap
    (relativeCycles L a p (n - 1)).subtype
  have hmap : ((relativeBoundary K a p n).range.comap
      (relativeCycles K a p (n - 1)).subtype) ≤ H.comap f := by
    intro c hc
    change f c ∈ H
    change (f c).1 ∈ (relativeBoundary L a p n).range
    obtain ⟨d, hd⟩ := hc
    refine ⟨relativeChainInclusion K L a h p n d, ?_⟩
    have hnat := congrArg (fun g => g d)
      (relativeChainInclusion_boundary K L a h p n)
    change relativeBoundary L a p n
        (relativeChainInclusion K L a h p n d) =
      relativeChainInclusion K L a h p (n - 1)
        (relativeBoundary K a p n d) at hnat
    have hdc : (relativeChainInclusion K L a h p (n - 1))
        (relativeBoundary K a p n d) = (f c).1 := by
      rw [hd]
      rfl
    simpa only [hdc] using hnat
  let q : relativeCycles L a p (n - 1) →+
      filtrationRelativeHomologyShifted L a p n :=
    QuotientAddGroup.mk' H
  have hker : ((relativeBoundary K a p n).range.comap
      (relativeCycles K a p (n - 1)).subtype) ≤
      (q.comp f).ker := by
    intro c hc
    change q (f c) = 0
    apply (QuotientAddGroup.eq_zero_iff (f c)).2
    exact hmap hc
  exact QuotientAddGroup.lift _ (q.comp f) hker

theorem filtrationRelativeHomologyMapShifted_mk (K L : FiniteComplex V)
    (a : ArcLabels V B) (h : K.simplices ⊆ L.simplices)
    (p : ℕ) (n : ℤ) (c : relativeCycles K a p (n - 1)) :
    filtrationRelativeHomologyMapShifted K L a h p n
        (QuotientAddGroup.mk' _ c) =
      QuotientAddGroup.mk' _ (relativeCyclesInclusion K L a h p (n - 1) c) := by
  rfl

#print axioms relativeChainInclusion_boundary
#print axioms filtrationRelativeHomologyMapShifted
#print axioms filtrationRelativeHomologyMapShifted_mk

end CurveGenusTwo.Filtration
