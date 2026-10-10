import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualSupportedAxisRectangleExtension
import CurveComplexGenusTwo.Topology.BandGlobalGluing.FullSquareExtensionHeader
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.UniformSpace.Compact
set_option maxHeartbeats 6000000
open Set Topology unitInterval Metric
namespace CurveComplex
open Schoenflies
theorem source_shrunk_axis_rectangle_supported_extension (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
    (hc : ∀ t : Icc (-1 : ℝ) 1,
      B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
    (hmeet : Set.range B ∩ {z : Plane | z 1 = 0} =
      (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ ∧ δ ≤ 1,
    ∃ flip : Bool, ∃ H : Plane ≃ₜ Plane,
      (∀ z, z ∉ Plane.openSquare 0 2 → H z = z) ∧
      (∀ t : ℝ, H (Plane.mk t 0) = Plane.mk t 0) ∧
      ∀ z : ↥(Plane.closedSquare 0 1),
        H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) =
          B ⟨Plane.mk (z.val 0) (δ*z.val 1),by
            have hz : max |z.val 0| |z.val 1| ≤ 1 := by
              simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
            have hx := (le_max_left _ _).trans hz
            have hy := (le_max_right _ _).trans hz
            simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm,abs_mul,abs_of_pos hδ.1] using
              max_le hx ((mul_le_mul_of_nonneg_left hy hδ.1.le).trans (by simpa using hδ.2))⟩ := by
  have bounded (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (hc : ∀ t : Icc (-1 : ℝ) 1,
        B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
      (hmeet : Set.range B ∩ {z : Plane | z 1 = 0} =
        (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
      ∃ δ : ℝ, ∃ hδ : 0 < δ ∧ δ ≤ 1,
        ∃ C : ↥(Plane.closedSquare 0 1) → Plane, IsEmbedding C ∧
          Set.range C ⊆ Plane.openSquare 0 2 ∧
          (∀ t : Icc (-1 : ℝ) 1,
            C ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0) ∧
          (Set.range C ∩ {z : Plane | z 1 = 0} =
            (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) ∧
          ∀ z, C z = B ⟨Plane.mk (z.val 0) (δ*z.val 1),by
            have hz : max |z.val 0| |z.val 1| ≤ 1 := by
              simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
            have hx := (le_max_left _ _).trans hz
            have hy := (le_max_right _ _).trans hz
            simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm,abs_mul,abs_of_pos hδ.1] using
              max_le hx ((mul_le_mul_of_nonneg_left hy hδ.1.le).trans (by simpa using hδ.2))⟩ := by
    let Q := Plane.closedSquare 0 1
    let W := Icc (-1 : ℝ) 1
    let : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
    let : CompactSpace W := isCompact_iff_compactSpace.mp isCompact_Icc
    let J : W × W → Q := fun z => ⟨Plane.mk z.1 z.2,by
      simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using
        max_le (abs_le.mpr z.1.property) (abs_le.mpr z.2.property)⟩
    have hJ : Continuous J := by dsimp [J]; fun_prop
    let O := (B ∘ J) ⁻¹' Plane.openSquare 0 2
    have hO : IsOpen O := (Plane.isOpen_openSquare 0 2).preimage (hB.continuous.comp hJ)
    have haxis : (univ : Set W) ×ˢ ({⟨0,by norm_num [W]⟩} : Set W) ⊆ O := by
      rintro ⟨x,y⟩ ⟨_,hy⟩
      have he : y = ⟨0,by norm_num [W]⟩ := mem_singleton_iff.mp hy
      subst y
      change B (J (x,⟨0,by norm_num [W]⟩)) ∈ Plane.openSquare 0 2
      rw [hc]
      have hx := abs_le.mpr x.property
      simpa [Plane.openSquare,Plane.supDist,Plane.supNorm] using
        max_lt (lt_of_le_of_lt hx (by norm_num)) (by norm_num : |(0:ℝ)| < 2)
    obtain ⟨A,V,hA,hV,hWA,h0V,hAV⟩ :=
      generalized_tube_lemma isCompact_univ isCompact_singleton hO haxis
    obtain ⟨d,hd,hdV⟩ := Metric.mem_nhds_iff.mp
      (hV.mem_nhds (h0V (mem_singleton _)))
    let δ := min (d/2) 1
    have hδ0 : 0 < δ := lt_min (half_pos hd) (by norm_num)
    have hδ1 : δ ≤ 1 := min_le_right _ _
    have hδd : δ < d := (min_le_left _ _).trans_lt (half_lt_self hd)
    let k : Q → Q := fun z => ⟨Plane.mk (z.val 0) (δ*z.val 1),by
      have hz : max |z.val 0| |z.val 1| ≤ 1 := by
        simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
      have hx := (le_max_left _ _).trans hz
      have hy := (le_max_right _ _).trans hz
      simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm,abs_mul,abs_of_pos hδ0] using
        max_le hx ((mul_le_mul_of_nonneg_left hy hδ0.le).trans (by simpa using hδ1))⟩
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hki : Function.Injective k := by
      intro z w he
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i
      · simpa [k,Plane.mk] using congrArg (fun q : Q => q.val 0) he
      · have hy := congrArg (fun q : Q => q.val 1) he
        exact mul_left_cancel₀ hδ0.ne' hy
    let C := B ∘ k
    have hC : IsEmbedding C := hB.comp (hkc.isClosedEmbedding hki).isEmbedding
    have hCU : Set.range C ⊆ Plane.openSquare 0 2 := by
      rintro x ⟨z,rfl⟩
      have hz : max |z.val 0| |z.val 1| ≤ 1 := by
        simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
      let u : W := ⟨z.val 0,abs_le.mp ((le_max_left _ _).trans hz)⟩
      let v : W := ⟨δ*z.val 1,by
        have hh := (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hz) hδ0.le).trans (by simpa using hδ1)
        exact abs_le.mp (by simpa [abs_mul,abs_of_pos hδ0] using hh)⟩
      have hv : v ∈ V := by
        apply hdV
        change dist v (⟨0,by norm_num [W]⟩ : W) < d
        rw [Subtype.dist_eq,Real.dist_eq]
        change |δ*z.val 1-0| < d
        rw [sub_zero,abs_mul,abs_of_pos hδ0]
        exact ((mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hz) hδ0.le).trans (by simp)).trans_lt hδd
      have hh : (u,v) ∈ O := hAV ⟨hWA (mem_univ u),hv⟩
      exact hh
    have hCc (t : W) : C ⟨Plane.mk t 0,by
        simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0 := by
      change B (k _) = _
      have hk : k ⟨Plane.mk t 0,by
          simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ =
          ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := by
        apply Subtype.ext
        ext i
        fin_cases i <;> simp [k]
      rw [hk,hc]
    refine ⟨δ,⟨hδ0,hδ1⟩,C,hC,hCU,hCc,?_,fun _ => rfl⟩
    apply Set.Subset.antisymm
    · rintro x ⟨⟨z,rfl⟩,hx⟩
      exact hmeet ▸ (show C z ∈ Set.range B ∩ {z : Plane | z 1 = 0} from
        ⟨Set.mem_range_self (k z),hx⟩)
    · rintro x ⟨t,_,rfl⟩
      exact ⟨⟨⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩,hCc t⟩,by simp [Plane.mk]⟩
  obtain ⟨δ,hδ,C,hC,hCU,hCc,hCmeet,hCformula⟩ := bounded B hB hc hmeet
  obtain ⟨flip,H,hfix,haxis,hformula⟩ := source_supported_axis_rectangle_extension 2 (by norm_num) C hC hCU hCc hCmeet
  exact ⟨δ,hδ,flip,H,hfix,haxis,fun z => (hformula z).trans (hCformula z)⟩

end CurveComplex
