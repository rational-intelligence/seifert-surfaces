import CurveComplexGenusTwo.Topology.FrontierCircle.BandStraightening
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge

open Topology Set
namespace CurveComplex

abbrev EndRectangle := Icc (-1:ℝ) 1 × Icc (-1:ℝ) 1

/-- Four small rectangles centered at the alternating axis attachment points.
The second parameter points outward from the crossing square. -/
noncomputable def crossingEndRectangle (ε : ℝ) (i : Fin 4) (z : EndRectangle) : ℝ × ℝ :=
  match i with
  | 0 => (ε/4*(z.1:ℝ), ε+ε/4*(z.2:ℝ))
  | 1 => (ε+ε/4*(z.2:ℝ), ε/4*(z.1:ℝ))
  | 2 => (ε/4*(z.1:ℝ), -(ε+ε/4*(z.2:ℝ)))
  | 3 => (-(ε+ε/4*(z.2:ℝ)), ε/4*(z.1:ℝ))

theorem crossingEndRectangle_continuous (ε : ℝ) (i : Fin 4) :
    Continuous (crossingEndRectangle ε i) := by
  fin_cases i
  · change Continuous (fun z : EndRectangle => (ε/4*(z.1:ℝ), ε+ε/4*(z.2:ℝ)))
    fun_prop
  · change Continuous (fun z : EndRectangle => (ε+ε/4*(z.2:ℝ), ε/4*(z.1:ℝ)))
    fun_prop
  · change Continuous (fun z : EndRectangle => (ε/4*(z.1:ℝ), -(ε+ε/4*(z.2:ℝ))))
    fun_prop
  · change Continuous (fun z : EndRectangle => (-(ε+ε/4*(z.2:ℝ)), ε/4*(z.1:ℝ)))
    fun_prop

theorem crossingEndRectangle_isEmbedding {ε : ℝ} (hε : 0 < ε) (i : Fin 4) :
    IsEmbedding (crossingEndRectangle ε i) := by
  apply ((crossingEndRectangle_continuous ε i).isClosedEmbedding ?_).isEmbedding
  intro z w he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  fin_cases i <;> dsimp [crossingEndRectangle] at h1 h2
  all_goals
    apply Prod.ext <;> apply Subtype.ext <;> nlinarith

theorem crossingEndRectangle_mem_large_square {ε : ℝ} (hε : 0 < ε)
    (i : Fin 4) (z : EndRectangle) :
    crossingEndRectangle ε i z ∈ Metric.closedBall ((0,0):ℝ×ℝ) (2*ε) := by
  have hs := z.1.property
  have ht := z.2.property
  fin_cases i <;>
    simp only [crossingEndRectangle,Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_zero,Prod.snd_zero,sub_zero,Real.norm_eq_abs,
      max_le_iff,abs_neg,abs_le]
  all_goals constructor <;> constructor <;> nlinarith [hs.1,hs.2,ht.1,ht.2]

theorem crossingEndRectangle_square_iff {ε : ℝ} (hε : 0 < ε)
    (i : Fin 4) (z : EndRectangle) :
    crossingEndRectangle ε i z ∈ Metric.closedBall ((0,0):ℝ×ℝ) ε ↔ (z.2:ℝ) ≤ 0 := by
  have hs := z.1.property
  have ht := z.2.property
  fin_cases i <;>
    simp only [crossingEndRectangle,Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_zero,Prod.snd_zero,sub_zero,Real.norm_eq_abs,
      max_le_iff,abs_neg,abs_le]
  all_goals constructor
  all_goals first
    | (rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩; nlinarith)
    | (intro h; constructor <;> constructor <;> nlinarith [hs.1,hs.2,ht.1,ht.2])

theorem crossingEndRectangle_pairwise_disjoint {ε : ℝ} (hε : 0 < ε) :
    Pairwise (fun i j : Fin 4 => Disjoint (Set.range (crossingEndRectangle ε i))
      (Set.range (crossingEndRectangle ε j))) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro x ⟨z,rfl⟩ ⟨w,he⟩
  have hs := z.1.property
  have ht := z.2.property
  have hu := w.1.property
  have hv := w.2.property
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  fin_cases i <;> fin_cases j <;> first
    | exact hij rfl
    | (dsimp [crossingEndRectangle] at h1 h2; nlinarith [hs.1,hs.2,ht.1,ht.2,hu.1,hu.2,hv.1,hv.2])

/-- Transport all four attachment rectangles through the crossing chart.
Their negative halves are exactly the part lying in the smaller square. -/
theorem crossing_chart_four_attachment_rectangles
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {U : Set S} {V : Set (ℝ × ℝ)} (h : U ≃ₜ V)
    {ε : ℝ} (hε : 0 < ε)
    (hV : Metric.closedBall ((0,0):ℝ×ℝ) (2*ε) ⊆ V) :
    ∃ d : Metric.closedBall ((0,0):ℝ×ℝ) ε → S,
    ∃ E : Fin 4 → EndRectangle → S,
      IsEmbedding d ∧ (∀ i, IsEmbedding (E i)) ∧
      Pairwise (fun i j => Disjoint (Set.range (E i)) (Set.range (E j))) ∧
      (∀ i z, E i z ∈ Set.range d ↔ (z.2:ℝ) ≤ 0) ∧
      (∀ i z, ∃ hz : E i z ∈ U,
        (h ⟨E i z,hz⟩ : ℝ × ℝ) = crossingEndRectangle ε i z) := by
  let d : Metric.closedBall ((0,0):ℝ×ℝ) ε → S := fun z =>
    (h.symm ⟨z,hV (Metric.closedBall_subset_closedBall (by linarith) z.property)⟩).val
  let E : Fin 4 → EndRectangle → S := fun i z =>
    (h.symm ⟨crossingEndRectangle ε i z,
      hV (crossingEndRectangle_mem_large_square hε i z)⟩).val
  have hdC : Continuous d := by
    exact continuous_subtype_val.comp (h.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))
  have hdI : Function.Injective d := by
    intro z w he
    apply Subtype.ext
    have he' := h.symm.injective (Subtype.ext he)
    exact congrArg (fun q : V => (q : ℝ × ℝ)) he'
  have hEC (i : Fin 4) : Continuous (E i) := by
    exact continuous_subtype_val.comp (h.symm.continuous.comp
      ((crossingEndRectangle_continuous ε i).subtype_mk _))
  have hEI (i : Fin 4) : Function.Injective (E i) := by
    intro z w he
    apply (crossingEndRectangle_isEmbedding hε i).injective
    have he' := h.symm.injective (Subtype.ext he)
    exact congrArg (fun q : V => (q : ℝ × ℝ)) he'
  refine ⟨d,E,(hdC.isClosedEmbedding hdI).isEmbedding,
    fun i => ((hEC i).isClosedEmbedding (hEI i)).isEmbedding,?_,?_,?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨z,rfl⟩ ⟨w,he⟩
    have he' := congrArg Subtype.val (h.symm.injective (Subtype.ext he))
    exact Set.disjoint_left.mp (crossingEndRectangle_pairwise_disjoint hε hij)
      (Set.mem_range_self z) ⟨w,he'⟩
  · intro i z
    constructor
    · rintro ⟨w,he⟩
      have he' := congrArg Subtype.val (h.symm.injective (Subtype.ext he))
      apply (crossingEndRectangle_square_iff hε i z).mp
      change (w : ℝ × ℝ) = crossingEndRectangle ε i z at he'
      rw [← he']
      exact w.property
    · intro hz
      refine ⟨⟨crossingEndRectangle ε i z,
        (crossingEndRectangle_square_iff hε i z).mpr hz⟩,?_⟩
      rfl

  · intro i z
    refine ⟨(h.symm ⟨crossingEndRectangle ε i z,
      hV (crossingEndRectangle_mem_large_square hε i z)⟩).property,?_⟩
    exact congrArg Subtype.val (h.apply_symm_apply _)

/-- The radial centers of the attachment rectangles are exactly the two
crossing coordinate axes. -/
theorem crossingEndRectangle_axes {ε : ℝ} (hε : 0 < ε)
    (i : Fin 4) (z : EndRectangle) :
    ((crossingEndRectangle ε i z).1 = 0 ↔ (i = 0 ∨ i = 2) ∧ (z.1:ℝ) = 0) ∧
    ((crossingEndRectangle ε i z).2 = 0 ↔ (i = 1 ∨ i = 3) ∧ (z.1:ℝ) = 0) := by
  have ht := z.2.property
  fin_cases i <;> simp only [crossingEndRectangle]
  all_goals norm_num
  all_goals constructor <;> first
    | (constructor <;> intro he <;> nlinarith)
    | (intro he; nlinarith [ht.1,ht.2])

/-- Four actual controlled end rectangles at an original topological crossing.
No charted-space instance is required: the crossing supplies the chart. -/
theorem crossesAt_four_attachment_rectangles
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} {p : S} (hcross : CrossesAt a b p) :
    ∃ ε : ℝ, ∃ hε : 0 < ε,
    ∃ d : Metric.closedBall ((0,0):ℝ×ℝ) ε → S,
    ∃ E : Fin 4 → EndRectangle → S,
      IsEmbedding d ∧ (∀ i, IsEmbedding (E i)) ∧
      Pairwise (fun i j => Disjoint (Set.range (E i)) (Set.range (E j))) ∧
      (∀ i z, E i z ∈ Set.range d ↔ (z.2:ℝ) ≤ 0) ∧
      (∀ i z, (E i z ∈ a.image ↔ (i = 0 ∨ i = 2) ∧ (z.1:ℝ) = 0) ∧
        (E i z ∈ b.image ↔ (i = 1 ∨ i = 3) ∧ (z.1:ℝ) = 0)) := by
  obtain ⟨U,V,hp,h,hU,hV,hzero,haxes,ρ,hρ,hρV⟩ :=
    exists_closed_disk_in_crossing_chart hcross
  have he : 0 < ρ/2 := by linarith
  have hbig : Metric.closedBall ((0,0):ℝ×ℝ) (2*(ρ/2)) ⊆ V := by
    convert hρV using 1 <;> congr 1 <;> ring
  obtain ⟨d,E,hd,hE,hdisj,hsq,hcoord⟩ :=
    crossing_chart_four_attachment_rectangles h he hbig
  refine ⟨ρ/2,he,d,E,hd,hE,hdisj,hsq,?_⟩
  intro i z
  obtain ⟨hz,hzcoord⟩ := hcoord i z
  have ha := haxes (E i z) hz
  rw [hzcoord] at ha
  exact ⟨ha.1.trans (crossingEndRectangle_axes he i z).1,
    ha.2.trans (crossingEndRectangle_axes he i z).2⟩

#print axioms crossesAt_four_attachment_rectangles
#print axioms crossing_chart_four_attachment_rectangles
#print axioms crossingEndRectangle_isEmbedding
#print axioms crossingEndRectangle_square_iff
#print axioms crossingEndRectangle_pairwise_disjoint
end CurveComplex
