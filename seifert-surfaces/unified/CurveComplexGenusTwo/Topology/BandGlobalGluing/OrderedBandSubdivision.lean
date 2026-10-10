import CurveComplexGenusTwo.Topology.BandGlobalGluing.EndPortNeighborhoods
import CurveComplexGenusTwo.Topology.BandGlobalGluing.SquareIntersection
import CurveComplexGenusTwo.Topology.FrontierCircle.BandStraightening

open Set Topology unitInterval
namespace CurveComplex

/-- A center point strictly between the longitudinal ends of an embedded
local rectangle is an interior point of its range in the surface. -/
theorem local_rectangle_center_interior
    {S : Type*} [TopologicalSpace S] [ChartedSpace Schoenflies.Plane S]
    {δ : ℝ} (hδ : 0 < δ)
    (B : Icc (1/3:ℝ) (2/3) × Icc (-δ) δ → S) (hB : IsEmbedding B)
    (t : Icc (1/3:ℝ) (2/3)) (ht0 : (1/3:ℝ) < t) (ht1 : (t:ℝ) < 2/3) :
    B (t,⟨0,by constructor <;> linarith⟩) ∈ interior (Set.range B) := by
  let f : Schoenflies.Plane → S := fun z =>
    B (projIcc (1/3) (2/3) (by norm_num) (z 0),
       projIcc (-δ) δ (by linarith) (z 1))
  let V : Set Schoenflies.Plane :=
    {z | z 0 ∈ Ioo (1/3:ℝ) (2/3) ∧ z 1 ∈ Ioo (-δ) δ}
  have hV : IsOpen V := (isOpen_Ioo.preimage (by fun_prop)).inter
    (isOpen_Ioo.preimage (by fun_prop))
  have hf : Continuous f := hB.continuous.comp
    ((continuous_projIcc.comp (by fun_prop)).prodMk
      (continuous_projIcc.comp (by fun_prop)))
  have hi : InjOn f V := by
    intro z hz w hw he
    have hh := hB.injective he
    have h0 := congrArg (fun q : Icc (1/3:ℝ) (2/3) × Icc (-δ) δ => (q.1 : ℝ)) hh
    have h1 := congrArg (fun q : Icc (1/3:ℝ) (2/3) × Icc (-δ) δ => (q.2 : ℝ)) hh
    simp only [projIcc_of_mem (show (1/3:ℝ) ≤ 2/3 by norm_num)
      ⟨hz.1.1.le,hz.1.2.le⟩,
      projIcc_of_mem (show (1/3:ℝ) ≤ 2/3 by norm_num)
      ⟨hw.1.1.le,hw.1.2.le⟩] at h0
    simp only [projIcc_of_mem (show -δ ≤ δ by linarith)
      ⟨hz.2.1.le,hz.2.2.le⟩,
      projIcc_of_mem (show -δ ≤ δ by linarith)
      ⟨hw.2.1.le,hw.2.2.le⟩] at h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hopen : IsOpen (f '' V) :=
    surface_invariance_of_domain_probe f V hV hf.continuousOn hi
  have hsub : f '' V ⊆ Set.range B := by
    rintro z ⟨w,hw,rfl⟩
    exact Set.mem_range_self _
  apply (hopen.subset_interior_iff.mpr hsub)
  refine ⟨Schoenflies.Plane.mk t 0,
    ⟨⟨ht0,ht1⟩,by
      change -δ < (0:ℝ) ∧ (0:ℝ) < δ
      constructor <;> linarith [hδ]⟩,?_⟩
  simp [f,projIcc_of_mem (show (1/3:ℝ) ≤ 2/3 by norm_num) t.property,
    projIcc_of_mem (show -δ ≤ δ by linarith)
      (show (0:ℝ) ∈ Icc (-δ) δ by constructor <;> linarith)]

/-- The first outside arc has an ordered finite subdivision. Each closed
subarc is contained in the ambient interior of a prescribed endpoint
rectangle or of an actually constructed local band disjoint from the crossing
square and the other outside arc. -/
theorem OneCrossingBandBase.first_ordered_band_subdivision
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace Schoenflies.Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    ∃ τ : ℕ → I, τ 0 = 0 ∧ Monotone τ ∧
      (∃ N, ∀ n ≥ N, τ n = 1) ∧
      ∀ n, (D.firstArc '' Icc (τ n) (τ (n+1)) ⊆
          interior (Set.range (D.ends 2))) ∨
        (D.firstArc '' Icc (τ n) (τ (n+1)) ⊆
          interior (Set.range (D.ends 0))) ∨
        ∃ (m : I) (η δ : ℝ) (hδ : 0 < δ)
          (B : Icc (1/3:ℝ) (2/3) × Icc (-δ) δ → S),
          0 < (m:ℝ) ∧ (m:ℝ) < 1 ∧ 0 < η ∧ IsEmbedding B ∧
          Disjoint (Set.range B) (Set.range D.square) ∧
          Disjoint (Set.range B) (Set.range D.secondArc) ∧
          D.firstArc '' Icc (τ n) (τ (n+1)) ⊆ interior (Set.range B) ∧
          ∀ z : Icc (1/3:ℝ) (2/3),
            B (z,⟨0,by constructor <;> linarith⟩) =
              D.firstArc.extend ((m:ℝ)-η+2*η*(z:ℝ)) := by
  classical
  let U : Set S := (Set.range D.square ∪ Set.range D.secondArc)ᶜ
  have hU : IsOpen U :=
    ((isCompact_range D.square_embedded.continuous).isClosed.union
      (isCompact_range D.secondArc.continuous).isClosed).isOpen_compl
  let Mid : Type := {t : I // 0 < (t:ℝ) ∧ (t:ℝ) < 1}
  have hgood (m : Mid) : D.firstArc m.val ∈ U := by
    intro hz
    rcases hz with hsquare | hsecond
    · have he : D.firstArc m.val ∈
          ({D.firstArc (0:I), D.firstArc (1:I)} : Set S) := by
        exact D.firstArc_square_intersection ▸
          ⟨Set.mem_range_self m.val,hsquare⟩
      rcases he with he | he
      · have ht := D.firstArc_embedded.injective he
        have hpos := m.property.1
        rw [ht] at hpos
        norm_num at hpos
      · have ht := D.firstArc_embedded.injective he
        have hlt := m.property.2
        rw [ht] at hlt
        norm_num at hlt
    · exact Set.disjoint_left.mp D.arcs_disjoint
        (Set.mem_range_self m.val) hsecond
  have hlocal (m : Mid) :
      ∃ η : ℝ, 0 < η ∧
      ∃ δ : ℝ, ∃ hδ : 0 < δ,
      ∃ B : Icc (1/3:ℝ) (2/3) × Icc (-δ) δ → S,
        IsEmbedding B ∧ Set.range B ⊆ U ∧
        (∀ z : Icc (1/3:ℝ) (2/3),
          B (z,⟨0,by constructor <;> linarith⟩) =
            D.firstArc.extend ((m:ℝ)-η+2*η*(z:ℝ))) := by
    obtain ⟨η,hη,_,_,δ,hδ,B,hB,hBU,hcenter,_⟩ :=
      Schoenflies.exists_local_rectangular_band_on_surface
        D.firstArc D.firstArc_embedded m.val m.property.1 m.property.2
        U hU (hgood m)
    exact ⟨η,hη,δ,hδ,B,hB,hBU,hcenter⟩
  choose η hη δ hδ B hB hBU hcenter using hlocal
  let c : Bool ⊕ Mid → Set I := fun j => match j with
    | Sum.inl false => D.firstArc ⁻¹' interior (Set.range (D.ends 2))
    | Sum.inl true => D.firstArc ⁻¹' interior (Set.range (D.ends 0))
    | Sum.inr m => D.firstArc ⁻¹' interior (Set.range (B m))
  have hcopen (j : Bool ⊕ Mid) : IsOpen (c j) := by
    cases j with
    | inl b => cases b <;> exact isOpen_interior.preimage D.firstArc.continuous
    | inr m => exact isOpen_interior.preimage D.firstArc.continuous
  have hcover : (Set.univ : Set I) ⊆ ⋃ j, c j := by
    intro t _
    rcases lt_or_eq_of_le t.property.1 with h0 | h0
    · rcases lt_or_eq_of_le t.property.2 with h1 | h1
      · let m : Mid := ⟨t,h0,h1⟩
        have hmid := local_rectangle_center_interior (hδ m) (B m) (hB m)
          (⟨1/2,by norm_num⟩ : Icc (1/3:ℝ) (2/3))
          (by norm_num) (by norm_num)
        have hcalc : (m:ℝ)-η m+2*η m*(1/2:ℝ) = (t:ℝ) := by
          change (t:ℝ)-η m+2*η m*(1/2:ℝ) = (t:ℝ)
          ring
        have hpoint : B m (⟨1/2,by norm_num⟩,
            ⟨0,by constructor <;> linarith [hδ m]⟩) = D.firstArc t := by
          rw [hcenter m, hcalc]
          exact D.firstArc.extend_extends' t
        have hmembership : t ∈ c (Sum.inr m) := by
          change D.firstArc t ∈ interior (Set.range (B m))
          rw [← hpoint]
          exact hmid
        exact mem_iUnion.mpr ⟨Sum.inr m, hmembership⟩
      · have ht : t = (1:I) := Subtype.ext h1
        subst t
        have hend : D.firstArc (1:I) ∈ interior (Set.range (D.ends 0)) := by
          rw [D.firstArc.target, ← D.ends_seam]
          exact endRectangle_center_interior (D.ends 0) (D.ends_embedded 0)
        exact mem_iUnion.mpr ⟨Sum.inl true, hend⟩
    · have ht : t = (0:I) := Subtype.ext h0.symm
      subst t
      have hstart : D.firstArc (0:I) ∈ interior (Set.range (D.ends 2)) := by
        rw [D.firstArc.source, ← D.ends_seam]
        exact endRectangle_center_interior (D.ends 2) (D.ends_embedded 2)
      exact mem_iUnion.mpr ⟨Sum.inl false, hstart⟩
  obtain ⟨τ,hτ0,hτmono,hτend,hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcopen hcover
  refine ⟨τ,hτ0,hτmono,hτend,?_⟩
  intro n
  obtain ⟨j,hj⟩ := hsub n
  cases j with
  | inl b =>
      cases b
      · exact Or.inl (Set.image_subset_iff.mpr hj)
      · exact Or.inr (Or.inl (Set.image_subset_iff.mpr hj))
  | inr m =>
      apply Or.inr
      apply Or.inr
      refine ⟨m,η m,δ m,hδ m,B m,m.property.1,m.property.2,hη m,
        hB m,?_,?_,Set.image_subset_iff.mpr hj,hcenter m⟩
      · exact Set.disjoint_left.mpr
          (fun z hz hs => hBU m hz (Or.inl hs))
      · exact Set.disjoint_left.mpr
          (fun z hz hq => hBU m hz (Or.inr hq))

#print axioms local_rectangle_center_interior
#print axioms OneCrossingBandBase.first_ordered_band_subdivision
end CurveComplex
