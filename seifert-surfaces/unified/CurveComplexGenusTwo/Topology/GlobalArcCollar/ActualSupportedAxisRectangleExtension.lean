import CurveComplexGenusTwo.Topology.BandGlobalGluing.ParametrizedCrosscutScaffold
import CurveComplexGenusTwo.Topology.BandGlobalGluing.FullSquareExtensionHeader
import Mathlib.Analysis.Convex.Topology
set_option maxHeartbeats 6000000
open Set Topology unitInterval Metric
namespace CurveComplex
open Schoenflies
-- Proof-free reusable candidate; not used by any completed proof.
theorem source_supported_axis_rectangle_extension (R : ℝ) (hR : 1 < R)
    (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
    (hBU : Set.range B ⊆ Plane.openSquare 0 R)
    (hc : ∀ t : Icc (-1 : ℝ) 1,
      B ⟨Plane.mk t 0,by
        simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
    (hmeet : Set.range B ∩ {z : Plane | z 1 = 0} =
      (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
    ∃ flip : Bool, ∃ H : Plane ≃ₜ Plane,
      (∀ z, z ∉ Plane.openSquare 0 R → H z = z) ∧
      (∀ t : ℝ, H (Plane.mk t 0) = Plane.mk t 0) ∧
      ∀ z : ↥(Plane.closedSquare 0 1),
        H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) = B z := by
  have recognize (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (hc : ∀ t : Icc (-1 : ℝ) 1,
        B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
      (hmeet : Set.range B ∩ {z : Plane | z 1=0} =
        (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
      ∀ z, B z 1 = 0 ↔ z.val 1 = 0 := by
    intro z
    constructor
    · intro hz
      have hm : B z ∈ (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ :=
        hmeet ▸ ⟨Set.mem_range_self z,hz⟩
      obtain ⟨t,_,ht⟩ := hm
      have he : B z = B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := ht.symm.trans (hc t).symm
      have hh := congrArg (fun z : ↥(Plane.closedSquare 0 1) => z.val 1) (hB.injective he)
      exact hh
    · intro hz
      have hzQ : max |z.val 0| |z.val 1| ≤ 1 := by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
      let t : Icc (-1 : ℝ) 1 := ⟨z.val 0,abs_le.mp ((le_max_left _ _).trans hzQ)⟩
      have he : z = ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := by
        apply Subtype.ext
        apply PiLp.ext
        intro i
        fin_cases i
        · rfl
        · exact hz
      rw [he,hc]
      rfl
  have sides (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (haxis : ∀ z, B z 1=0 ↔ z.val 1=0)
      (hB0 : B ⟨0,by simp [Plane.closedSquare,Plane.supDist,Plane.supNorm]⟩ = 0) :
      ((∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1) ∧
        (∀ z : ↥(Plane.closedSquare 0 1),z.val 1<0 → B z 1<0)) ∨
      ((∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → B z 1<0) ∧
        (∀ z : ↥(Plane.closedSquare 0 1),z.val 1<0 → 0<B z 1)) := by
    have side (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
        (haxis : ∀ z, B z 1=0 ↔ z.val 1=0) :
        (∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1) ∨
        (∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → B z 1<0) := by
      let A : Set Plane := Plane.closedSquare 0 1 ∩ {z | 0<z 1}
      have hconv : Convex ℝ A := by
        intro x hx y hy a b ha hb hab
        refine ⟨(Plane.convex_closedSquare 0 1) hx.1 hy.1 ha hb hab,?_⟩
        change 0<a*x 1+b*y 1
        by_cases haz : a=0
        · have hb1 : b=1 := by linarith
          simpa [haz,hb1] using hy.2
        · have hap : 0<a := lt_of_le_of_ne ha (Ne.symm haz)
          exact add_pos_of_pos_of_nonneg (mul_pos hap hx.2) (mul_nonneg hb hy.2.le)
      let f : A → Plane := fun z => B ⟨z, z.property.1⟩
      have hfc : Continuous f := hB.continuous.comp (continuous_subtype_val.subtype_mk _)
      have hpreA : IsPreconnected (univ : Set A) := by
        have hconn : PreconnectedSpace A := (isPreconnected_iff_preconnectedSpace).mp hconv.isPreconnected
        letI := hconn
        exact isPreconnected_univ
      have hpre : IsPreconnected (Set.range f) := by
        simpa only [Set.image_univ] using hpreA.image f hfc.continuousOn
      have hcover : Set.range f ⊆ {z : Plane | 0<z 1} ∪ {z : Plane | z 1<0} := by
        rintro z ⟨t,rfl⟩
        have hz : f t 1 ≠ 0 := by
          intro hh
          have h0 := (haxis ⟨t,t.property.1⟩).mp hh
          exact ne_of_gt t.property.2 h0
        exact lt_or_gt_of_ne hz.symm
      have hopenpos : IsOpen {z : Plane | 0<z 1} := isOpen_lt continuous_const (by fun_prop)
      have hopenneg : IsOpen {z : Plane | z 1<0} := isOpen_lt (by fun_prop) continuous_const
      have hdis : Disjoint {z : Plane | 0<z 1} {z : Plane | z 1<0} :=
        Set.disjoint_left.mpr (fun z hz0 hz1 => (lt_asymm (show 0<z 1 from hz0) (show z 1<0 from hz1)))
      rcases hpre.subset_or_subset hopenpos hopenneg hdis hcover with hp | hn
      · left
        intro z hz
        exact hp ⟨⟨z,⟨z.property,hz⟩⟩,rfl⟩
      · right
        intro z hz
        exact hn ⟨⟨z,⟨z.property,hz⟩⟩,rfl⟩
    let Q := Plane.closedSquare 0 1
    letI : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
    let T : Q → Q := fun z => ⟨Plane.mk (z.val 0) (-z.val 1),by
      simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property⟩
    have hTc : Continuous T := by dsimp [T]; fun_prop
    have hTi : Function.Injective T := by
      intro z w he
      apply Subtype.ext
      have hx := congrArg (fun z : Q => z.val 0) he
      have hy := congrArg (fun z : Q => z.val 1) he
      apply PiLp.ext
      intro i
      fin_cases i
      · exact hx
      · change -z.val 1 = -w.val 1 at hy
        exact neg_injective hy
    have hTe : IsEmbedding T := (hTc.isClosedEmbedding hTi).isEmbedding
    have hTT (z : Q) : T (T z) = z := by
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [T,Plane.mk]
    let B' : Q → Plane := B ∘ T
    have hB' : IsEmbedding B' := hB.comp hTe
    have haxis' (z : Q) : B' z 1=0 ↔ z.val 1=0 := by
      change B (T z) 1=0 ↔ z.val 1=0
      rw [haxis]
      change -z.val 1=0 ↔ z.val 1=0
      exact neg_eq_zero
    have hplus := side B hB haxis
    have hminus0 := side B' hB' haxis'
    have hminus : (∀ z : Q,z.val 1<0 → 0<B z 1) ∨ (∀ z : Q,z.val 1<0 → B z 1<0) := by
      rcases hminus0 with hp | hn
      · left
        intro z hz
        have ht : 0<(T z).val 1 := by change 0< -z.val 1; linarith
        have hh := hp (T z) ht
        change B (T (T z)) 1>0 at hh
        rwa [hTT] at hh
      · right
        intro z hz
        have ht : 0<(T z).val 1 := by change 0< -z.val 1; linarith
        have hh := hn (T z) ht
        change B (T (T z)) 1<0 at hh
        rwa [hTT] at hh
    have hzero : (0:Plane) ∈ interior Q := by
      rw [Plane.interior_closedSquare]
      simp [Plane.openSquare,Plane.supDist,Plane.supNorm]
    have hzeroim : (0:Plane) ∈ interior (Set.range B) := by
      have hh := (embedded_planar_region_interior_iff_probe Q B hB ⟨0,interior_subset hzero⟩).mpr hzero
      rwa [hB0] at hh
    obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hzeroim)
    have hpm (s : ℝ) (hs : s=1 ∨ s= -1) : Plane.mk 0 (s*d/2) ∈ Set.range B := by
      apply interior_subset
      apply hball
      rw [Metric.mem_ball,dist_zero_right]
      rcases hs with rfl | rfl <;> simp [Plane.mk,EuclideanSpace.norm_eq,Fin.sum_univ_two,Real.sqrt_sq_eq_abs,abs_mul,abs_div,abs_of_pos hd] <;> linarith
    obtain ⟨zp,hzp⟩ := hpm 1 (Or.inl rfl)
    obtain ⟨zn,hzn⟩ := hpm (-1) (Or.inr rfl)
    have hzpR : B zp 1=d/2 := by have hh := congrArg (fun z : Plane => z 1) hzp; simpa using hh
    have hznR : B zn 1= -d/2 := by have hh := congrArg (fun z : Plane => z 1) hzn; simpa using hh
    rcases hplus with hp | hn
    · rcases hminus with mp | mn
      · exfalso
        rcases lt_trichotomy (zn.val 1) 0 with hneg | heq | hpos
        · have hh := mp zn hneg; linarith
        · have hh := (haxis zn).mpr heq; linarith
        · have hh := hp zn hpos; linarith
      · exact Or.inl ⟨hp,mn⟩
    · rcases hminus with mp | mn
      · exact Or.inr ⟨hn,mp⟩
      · exfalso
        rcases lt_trichotomy (zp.val 1) 0 with hneg | heq | hpos
        · have hh := mn zp hneg; linarith
        · have hh := (haxis zp).mpr heq; linarith
        · have hh := hn zp hpos; linarith
  have oriented (R : ℝ) (hR : 1<R)
      (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (hBU : Set.range B ⊆ Plane.openSquare 0 R)
      (hc : ∀ t : Icc (-1 : ℝ) 1,
        B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
      (hplus : ∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1)
      (hminus : ∀ z : ↥(Plane.closedSquare 0 1),z.val 1<0 → B z 1<0) :
      ∃ H : Plane ≃ₜ Plane,
        (∀ z, z ∉ Plane.openSquare 0 R → H z=z) ∧
        (∀ t : ℝ,H (Plane.mk t 0)=Plane.mk t 0) ∧
        ∀ z : ↥(Plane.closedSquare 0 1),H z=B z := by
    have positive (R : ℝ) (hR : 1<R)
        (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
        (hBU : Set.range B ⊆ Plane.openSquare 0 R)
        (hc : ∀ t : Icc (-1 : ℝ) 1,
          B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
        (hside : ∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1) :
        ∃ H : Plane ≃ₜ Plane,
          (∀ z, z ∉ Plane.openSquare 0 R → H z=z) ∧
          (∀ z, z 1≤0 → H z=z) ∧
          ∀ z : ↥(Plane.closedSquare 0 1),0≤z.val 1 → H z=B z := by
      have boundary (R : ℝ) (hR : 1<R)
          (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
          (hBU : Set.range B ⊆ Plane.openSquare 0 R)
          (hc : ∀ t : Icc (-1 : ℝ) 1,
            B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
          (hside : ∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1) :
          ∃ F : Plane ≃ₜ Plane,
            (∀ z, z ∉ Plane.openSquare 0 R → F z=z) ∧
            (∀ z, z 1≤0 → F z=z) ∧
            ∀ z : ↥(Plane.closedSquare 0 1),
              z.val ∈ modelCurve → 0≤z.val 1 → F z = B z := by
        have upper : ∃ f : I → Plane, IsEmbedding f ∧
            f 0 = Plane.mk (-1) 0 ∧ f 1 = Plane.mk 1 0 ∧
            (∀ t, f t ∈ modelCurve) ∧
            (∀ t : I,0<t → t<1 → 0<f t 1) ∧
            Set.range f = {z : Plane | z ∈ modelCurve ∧ 0≤z 1} := by
          let f : I → Plane := fun t => Plane.mk (max (-1) (min 1 (6*(t:ℝ)-3)))
            (min 1 (min (3*(t:ℝ)) (3-3*(t:ℝ))))
          have hfc : Continuous f := by dsimp [f]; fun_prop
          have hleft (t : I) (ht : (t:ℝ) ≤ 1/3) : f t=Plane.mk (-1) (3*(t:ℝ)) := by
            have ha : 6*(t:ℝ)-3 ≤ 1 := by linarith
            have hb : 6*(t:ℝ)-3 ≤ -1 := by linarith
            have hc : 3*(t:ℝ) ≤ 3-3*(t:ℝ) := by linarith
            have hd : 3*(t:ℝ) ≤ 1 := by linarith
            simp only [f,min_eq_right ha,max_eq_left hb,min_eq_left hc,min_eq_right hd]
          have hmid (t : I) (ht0 : 1/3 ≤ (t:ℝ)) (ht1 : (t:ℝ) ≤ 2/3) : f t=Plane.mk (6*(t:ℝ)-3) 1 := by
            have ha : 6*(t:ℝ)-3 ≤ 1 := by linarith
            have hb : -1 ≤ 6*(t:ℝ)-3 := by linarith
            have hc : 1 ≤ min (3*(t:ℝ)) (3-3*(t:ℝ)) := le_min (by linarith) (by linarith)
            simp only [f,min_eq_right ha,max_eq_right hb,min_eq_left hc]
          have hright (t : I) (ht : 2/3 ≤ (t:ℝ)) : f t=Plane.mk 1 (3-3*(t:ℝ)) := by
            have ha : 1 ≤ 6*(t:ℝ)-3 := by linarith
            have hc : 3-3*(t:ℝ) ≤ 3*(t:ℝ) := by linarith
            have hd : 3-3*(t:ℝ) ≤ 1 := by linarith
            simp only [f,min_eq_left ha,max_eq_right (by norm_num : (-1:ℝ)≤1),min_eq_right hc,min_eq_right hd]
          have hclass (t : I) :
              (f t=Plane.mk (-1) (3*(t:ℝ)) ∧ (t:ℝ)≤1/3) ∨
              (f t=Plane.mk (6*(t:ℝ)-3) 1 ∧ 1/3≤(t:ℝ) ∧ (t:ℝ)≤2/3) ∨
              (f t=Plane.mk 1 (3-3*(t:ℝ)) ∧ 2/3≤(t:ℝ)) := by
            by_cases hl : (t:ℝ)≤1/3
            · exact Or.inl ⟨hleft t hl,hl⟩
            · by_cases hr : (t:ℝ)≤2/3
              · exact Or.inr (Or.inl ⟨hmid t (le_of_not_ge hl) hr,le_of_not_ge hl,hr⟩)
              · exact Or.inr (Or.inr ⟨hright t (le_of_not_ge hr),le_of_not_ge hr⟩)
          have hfi : Function.Injective f := by
            intro t u he
            rcases hclass t with ⟨ht,htb⟩ | ⟨ht,htb0,htb1⟩ | ⟨ht,htb⟩
            all_goals rcases hclass u with ⟨hu,hub⟩ | ⟨hu,hub0,hub1⟩ | ⟨hu,hub⟩
            all_goals rw [ht,hu] at he
            all_goals have hx := congrArg (fun z : Plane => z 0) he
            all_goals have hy := congrArg (fun z : Plane => z 1) he
            all_goals simp [Plane.mk] at hx hy
            all_goals apply Subtype.ext
            all_goals nlinarith
          have hcurve (t : I) : f t ∈ modelCurve := by
            change max |f t 0| |f t 1|=1
            rcases hclass t with ⟨ht,htb⟩ | ⟨ht,htb0,htb1⟩ | ⟨ht,htb⟩
            · rw [ht]
              change max |(-1:ℝ)| |3*(t:ℝ)|=1
              rw [abs_neg,abs_one,abs_of_nonneg (by nlinarith [t.property.1]),max_eq_left (by linarith)]
            · rw [ht]
              change max |6*(t:ℝ)-3| |(1:ℝ)|=1
              rw [abs_one,max_eq_right (abs_le.mpr ⟨by linarith,by linarith⟩)]
            · rw [ht]
              change max |(1:ℝ)| |3-3*(t:ℝ)|=1
              rw [abs_one,abs_of_nonneg (by nlinarith [t.property.2]),max_eq_left (by linarith)]
          have hpos (t : I) (ht0 : 0<t) (ht1 : t<1) : 0<f t 1 := by
            rcases hclass t with ⟨ht,htb⟩ | ⟨ht,htb0,htb1⟩ | ⟨ht,htb⟩
            all_goals rw [ht]
            · change 0<3*(t:ℝ); have hh : (0:ℝ)<t := ht0; linarith
            · norm_num [Plane.mk]
            · change 0<3-3*(t:ℝ); have hh : (t:ℝ)<1 := ht1; linarith
          have hf0 : f 0=Plane.mk (-1) 0 := by norm_num [f]
          have hf1 : f 1=Plane.mk 1 0 := by norm_num [f]
          refine ⟨f,(hfc.isClosedEmbedding hfi).isEmbedding,hf0,hf1,hcurve,hpos,?_⟩
          ext v
          constructor
          · rintro ⟨t,rfl⟩
            refine ⟨hcurve t,?_⟩
            by_cases ht0 : t=0
            · rw [ht0,hf0]; norm_num [Plane.mk]
            · by_cases ht1 : t=1
              · rw [ht1,hf1]; norm_num [Plane.mk]
              · exact (hpos t (lt_of_le_of_ne t.property.1 (Ne.symm ht0)) (lt_of_le_of_ne t.property.2 ht1)).le
          · intro hv
            have hmodel : max |v 0| |v 1|=1 := hv.1
            have hx : |v 0|≤1 := (le_max_left _ _).trans hmodel.le
            have hy : v 1≤1 := (le_abs_self _).trans ((le_max_right _ _).trans hmodel.le)
            by_cases hxneg : v 0 = -1
            · let t : I := ⟨v 1/3,⟨by linarith [hv.2],by linarith⟩⟩
              have ht : (t:ℝ)≤1/3 := by dsimp [t]; linarith
              refine ⟨t,?_⟩
              rw [hleft t ht]
              apply PiLp.ext
              intro i
              fin_cases i
              · exact hxneg.symm
              · change 3*(v 1/3)=v 1; ring
            · by_cases hxpos : v 0=1
              · let t : I := ⟨1-v 1/3,⟨by linarith,by linarith [hv.2]⟩⟩
                have ht : 2/3≤(t:ℝ) := by dsimp [t]; linarith
                refine ⟨t,?_⟩
                rw [hright t ht]
                apply PiLp.ext
                intro i
                fin_cases i
                · exact hxpos.symm
                · change 3-3*(1-v 1/3)=v 1; ring
              · have hx0 : -1<v 0 := lt_of_le_of_ne (abs_le.mp hx).1 (Ne.symm hxneg)
                have hx1 : v 0<1 := lt_of_le_of_ne (abs_le.mp hx).2 hxpos
                have hy1 : v 1=1 := by
                  apply le_antisymm hy
                  by_contra hh
                  have hylt : v 1<1 := lt_of_not_ge hh
                  have habs : |v 1|<1 := by rw [abs_of_nonneg hv.2]; exact hylt
                  have hmax := max_lt (abs_lt.mpr ⟨hx0,hx1⟩) habs
                  rw [hmodel] at hmax
                  exact lt_irrefl _ hmax
                let t : I := ⟨(v 0+3)/6,⟨by linarith,by linarith⟩⟩
                have ht0 : 1/3≤(t:ℝ) := by dsimp [t]; linarith
                have ht1 : (t:ℝ)≤2/3 := by dsimp [t]; linarith
                refine ⟨t,?_⟩
                rw [hmid t ht0 ht1]
                apply PiLp.ext
                intro i
                fin_cases i
                · change 6*((v 0+3)/6)-3=v 0; ring
                · exact hy1.symm
        have normalize (R : ℝ) (hR : 0 < R) :
            ∃ N : Plane ≃ₜ Plane,
              (∀ z,N z=Plane.mk (z 0/R) (2*z 1/R-1)) ∧
              (∀ z,N z ∈ Plane.openSquare 0 1 ↔ |z 0|<R ∧ 0<z 1 ∧ z 1<R) := by
          let N : Plane ≃ₜ Plane := {
            toFun := fun z => Plane.mk (z 0/R) (2*z 1/R-1)
            invFun := fun z => Plane.mk (R*z 0) (R*(z 1+1)/2)
            left_inv := by
              intro z
              apply PiLp.ext
              intro i
              fin_cases i <;> simp [Plane.mk] <;> field_simp <;> ring
            right_inv := by
              intro z
              apply PiLp.ext
              intro i
              fin_cases i <;> simp [Plane.mk] <;> field_simp <;> ring
            continuous_toFun := by fun_prop
            continuous_invFun := by fun_prop
          }
          refine ⟨N,fun z => rfl,?_⟩
          intro z
          rw [mem_openSquare_zero_one]
          change max |z 0/R| |2*z 1/R-1|<1 ↔ _
          rw [max_lt_iff,abs_div,abs_of_pos hR,div_lt_one hR]
          simp only [abs_lt]
          constructor
          · rintro ⟨hx,hy0,hy1⟩
            refine ⟨hx,?_,?_⟩
            · have hh : 0 < 2*z 1/R := by linarith
              have hmul := (div_pos_iff.mp hh)
              rcases hmul with hh | hh
              · linarith [hh.1]
              · linarith [hh.2]
            · have hh : 2*z 1/R < 2 := by linarith
              have hv := (div_lt_iff₀ hR).mp hh
              linarith
          · rintro ⟨hx,hz0,hzR⟩
            refine ⟨hx,?_,?_⟩
            · have hh : 0 < 2*z 1/R := div_pos (by linarith) hR
              linarith
            · have hh : 2*z 1/R < 2 := (div_lt_iff₀ hR).mpr (by linarith)
              linarith
        have hRpos : 0<R := lt_trans zero_lt_one hR
        obtain ⟨f,hf,hf0,hf1,hfc,hfp,hfim⟩ := upper
        obtain ⟨N,hN,hNopen⟩ := normalize R hRpos
        let fq : I → ↥(Plane.closedSquare 0 1) := fun t => ⟨f t,by
          have hh : max |f t 0| |f t 1|=1 := hfc t
          simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using hh.le⟩
        have hfqc : Continuous fq := hf.continuous.subtype_mk _
        have hfqi : Function.Injective fq := fun t u he => hf.injective (congrArg Subtype.val he)
        have hfqe : IsEmbedding fq := (hfqc.isClosedEmbedding hfqi).isEmbedding
        let g : I → Plane := B ∘ fq
        have hg : IsEmbedding g := hB.comp hfqe
        have hg0 : g 0=f 0 := by
          have hh := hc ⟨-1,by norm_num⟩
          change B (fq 0)=f 0
          have he : fq 0=⟨Plane.mk (-1) 0,by simp [Plane.closedSquare,Plane.supDist,Plane.supNorm]⟩ := Subtype.ext hf0
          rw [he,hf0]
          exact hh
        have hg1 : g 1=f 1 := by
          have hh := hc ⟨1,by norm_num⟩
          change B (fq 1)=f 1
          have he : fq 1=⟨Plane.mk 1 0,by simp [Plane.closedSquare,Plane.supDist,Plane.supNorm]⟩ := Subtype.ext hf1
          rw [he,hf1]
          exact hh
        have hmodel (s : ℝ) (hs : |s|≤1) : N (Plane.mk s 0) ∈ modelCurve := by
          rw [hN]
          have hh : max |s/R| |(-1:ℝ)|=1 := by
            rw [abs_div,abs_of_pos hRpos,abs_neg,abs_one,max_eq_right]
            exact (div_le_one hRpos).mpr (hs.trans hR.le)
          simpa [modelCurve,Plane.supNorm,Plane.mk] using hh
        have ha : (N ∘ f) 0 ∈ modelCurve := by
          change N (f 0) ∈ modelCurve
          rw [hf0]
          exact hmodel (-1) (by norm_num)
        have hb : (N ∘ f) 1 ∈ modelCurve := by
          change N (f 1) ∈ modelCurve
          rw [hf1]
          exact hmodel 1 (by norm_num)
        have hfi (t : I) (ht0 : 0<t) (ht1 : t<1) : (N ∘ f) t ∈ Plane.openSquare 0 1 := by
          apply (hNopen (f t)).mpr
          have hm : max |f t 0| |f t 1|=1 := hfc t
          have hp := hfp t ht0 ht1
          refine ⟨lt_of_le_of_lt ((le_max_left _ _).trans hm.le) hR,hp,?_⟩
          exact lt_of_le_of_lt ((le_abs_self _).trans ((le_max_right _ _).trans hm.le)) hR
        have hgi (t : I) (ht0 : 0<t) (ht1 : t<1) : (N ∘ g) t ∈ Plane.openSquare 0 1 := by
          apply (hNopen (g t)).mpr
          have hm := hBU (Set.mem_range_self (fq t))
          have hmR : max |g t 0| |g t 1|<R := by simpa [Plane.openSquare,Plane.supDist,Plane.supNorm,g] using hm
          refine ⟨lt_of_le_of_lt (le_max_left _ _) hmR,hside (fq t) (hfp t ht0 ht1),?_⟩
          exact lt_of_le_of_lt ((le_abs_self _).trans (le_max_right _ _)) hmR
        obtain ⟨P,hP,hPfix⟩ := parametrized_relative_crosscut_replacement
          (N ∘ f) (N ∘ g) (N.isEmbedding.comp hf) (N.isEmbedding.comp hg)
          (congrArg N hg0).symm (congrArg N hg1).symm ha hb hfi hgi
        let F : Plane ≃ₜ Plane := (N.trans P).trans N.symm
        have hfix (z : Plane) (hz : N z ∉ Plane.openSquare 0 1) : F z=z := by
          change N.symm (P (N z))=z
          rw [hPfix _ hz,N.symm_apply_apply]
        refine ⟨F,?_,?_,?_⟩
        · intro z hz
          apply hfix
          intro hNz
          obtain ⟨hx,hy0,hyR⟩ := (hNopen z).mp hNz
          apply hz
          have hh : max |z 0| |z 1|<R := max_lt hx (by rw [abs_of_pos hy0]; exact hyR)
          simpa [Plane.openSquare,Plane.supDist,Plane.supNorm] using hh
        · intro z hz
          apply hfix
          intro hNz
          exact not_lt_of_ge hz ((hNopen z).mp hNz).2.1
        · intro z hzcurve hzy
          have hz : (z:Plane) ∈ Set.range f := hfim ▸ ⟨hzcurve,hzy⟩
          obtain ⟨t,ht⟩ := hz
          have hq : fq t=z := Subtype.ext ht
          change N.symm (P (N z.val))=B z
          rw [← ht]
          have hh := hP t
          change P (N (f t))=N (g t) at hh
          rw [hh]
          change N.symm (N (B (fq t)))=B z
          rw [N.symm_apply_apply,hq]
      have sameRange (e f : ↥(Plane.closedSquare 0 1) → Plane) (he : IsEmbedding e) (hf : IsEmbedding f)
          (hag : ∀ z : ↥(Plane.closedSquare 0 1), z.val ∈ modelCurve → e z=f z) :
          Set.range e=Set.range f := by
        classical
        have hboundary (k : ↥modelCurve → Plane) (hk : IsEmbedding k) :
            IsJordanCurve (Set.range k) ∧
              ∃ F : Plane ≃ₜ Plane, ∀ z : ↥modelCurve, F z = k z := by
        
          classical
          obtain ⟨f,hf,hfim⟩ := isJordanCurve_modelCurve
          have hfmem (t : I) : f t ∈ modelCurve := by
            rw [← hfim]
            exact ⟨t,t.property,rfl⟩
          let q : I → ↥modelCurve := fun t => ⟨f t,hfmem t⟩
          have hq : Continuous q := by
            exact (continuousOn_iff_continuous_restrict.mp hf.continuousOn).subtype_mk _
          let g : ℝ → Plane := fun t => k (q (projIcc 0 1 zero_le_one t))
          have hg : Continuous g := hk.continuous.comp
            (hq.comp continuous_projIcc)
          have hqeq (t : ℝ) (ht : t ∈ (Icc (0 : ℝ) 1)) :
              (q (projIcc 0 1 zero_le_one t) : Plane) = f t := by
            dsimp [q]
            rw [projIcc_of_mem zero_le_one ht]
          have hloop : IsLoop g := by
            refine ⟨hg.continuousOn, ?_, ?_⟩
            · apply congrArg k
              apply Subtype.ext
              rw [hqeq 0 (by norm_num),hqeq 1 (by norm_num)]
              exact hf.closes
            · intro s hs t ht he
              apply hf.injOn hs ht
              have hh := congrArg Subtype.val (hk.injective he)
              rw [hqeq s ⟨hs.1,hs.2.le⟩,hqeq t ⟨ht.1,ht.2.le⟩] at hh
              exact hh
          have him : g '' (Icc (0 : ℝ) 1) = Set.range k := by
            ext z
            constructor
            · rintro ⟨t,ht,rfl⟩
              exact Set.mem_range_self _
            · rintro ⟨v,rfl⟩
              have hvm : (v : Plane) ∈ f '' (Icc (0 : ℝ) 1) := hfim.symm ▸ v.property
              obtain ⟨t,ht,he⟩ := hvm
              refine ⟨t,ht,?_⟩
              apply congrArg k
              apply Subtype.ext
              exact (hqeq t ht).trans he
          have hJ : IsJordanCurve (Set.range k) := ⟨g,hloop,him⟩
          obtain ⟨F,hF⟩ := jordan_schoenflies_of_homeomorph
            isJordanCurve_modelCurve hJ hk.toHomeomorph
          exact ⟨hJ,F,fun z => hF z⟩
        
        have hinterior (e : ↥(Plane.closedSquare 0 1) → Plane) (he : IsEmbedding e) :
            IsPreconnected (interior (Set.range e)) ∧
              (interior (Set.range e)).Nonempty := by
        
          let K := Plane.closedSquare 0 1
          let A : Set ↥K := {z | (z : Plane) ∈ interior K}
          have hAimage : Subtype.val '' A = interior K := by
            ext z
            constructor
            · rintro ⟨w,hw,rfl⟩; exact hw
            · intro hz; exact ⟨⟨z,interior_subset hz⟩,hz,rfl⟩
          have hAconn : IsPreconnected A := by
            apply IsInducing.subtypeVal.isPreconnected_image.mp
            rw [hAimage]
            change IsPreconnected (interior (Plane.closedSquare 0 1))
            rw [Plane.interior_closedSquare]
            exact (Plane.convex_openSquare 0 1).isPreconnected
          have heA : e '' A = interior (Set.range e) := by
            ext y
            constructor
            · rintro ⟨z,hz,rfl⟩
              exact (embedded_planar_region_interior_iff_probe K e he z).mpr hz
            · intro hy
              obtain ⟨z,rfl⟩ := interior_subset hy
              exact ⟨z,(embedded_planar_region_interior_iff_probe K e he z).mp hy,rfl⟩
          have hzero : (0 : Plane) ∈ interior K := by
            change (0 : Plane) ∈ interior (Plane.closedSquare 0 1)
            rw [Plane.interior_closedSquare]
            simp [Plane.openSquare,Plane.supNorm]
          refine ⟨heA ▸ hAconn.image e he.continuous.continuousOn, ?_⟩
          exact ⟨e ⟨0,interior_subset hzero⟩,
            (embedded_planar_region_interior_iff_probe K e he _).mpr hzero⟩
        have hside (K : Set Plane) (hK : IsCompact K)
            (hconn : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
            (hJ : IsJordanCurve (frontier K)) :
            K = frontier K ∪ inside (frontier K) := by
        
          obtain ⟨x,hx⟩ := hne
          have hsub : interior K ⊆ (frontier K)ᶜ := by
            intro z hz hzfr
            exact hzfr.2 hz
          have hfr : frontier (interior K) ∩ (frontier K)ᶜ = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro z hz
            exact hz.2 (frontier_interior_subset hz.1)
          have hcomp : connectedComponentIn (frontier K)ᶜ x = interior K :=
            Plane.connectedComponentIn_eq_of_frontier_disjoint
              isOpen_interior hconn hsub hfr hx
          have hxin : x ∈ inside (frontier K) := by
            refine ⟨hsub hx, ?_⟩
            rw [hcomp]
            exact hK.isBounded.subset interior_subset
          have hi : interior K = inside (frontier K) :=
            hcomp.symm.trans ((jordan_curve_theorem hJ).connectedComponentIn_eq_inside hxin)
          calc
            K = interior K ∪ frontier K := by
              rw [← closure_eq_interior_union_frontier, hK.isClosed.closure_eq]
            _ = frontier K ∪ inside (frontier K) := by rw [hi,union_comm]
        
        let Q := Plane.closedSquare 0 1
        letI : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
        let b : ↥modelCurve → ↥Q := fun z => ⟨z,modelCurve_subset_closedSquare z.property⟩
        have hbc : Continuous b := continuous_subtype_val.subtype_mk _
        have hbi : Function.Injective b := by
          intro z w hh
          apply Subtype.ext
          have hh' := congrArg (fun v : Q => (v : Plane)) hh
          exact hh'
        letI : CompactSpace ↥modelCurve := isCompact_iff_compactSpace.mp isJordanCurve_modelCurve.isCompact
        have hb : IsEmbedding b := (hbc.isClosedEmbedding hbi).isEmbedding
        have front (g : Q → Plane) (hg : IsEmbedding g) : Set.range (g ∘ b)=frontier (Set.range g) := by
          rw [← embedded_compact_planar_region_frontier_probe Q (isCompact_closedSquare 0 1) g hg]
          ext z
          constructor
          · rintro ⟨w,rfl⟩
            refine ⟨b w,?_,rfl⟩
            rw [← modelCurve_eq_frontier]
            exact w.property
          · rintro ⟨w,hw,rfl⟩
            have hm : (w:Plane) ∈ modelCurve := by rw [modelCurve_eq_frontier]; exact hw
            refine ⟨⟨w,hm⟩,?_⟩
            change g (b _)=g w
            congr 1
        have hfront : frontier (Set.range e)=frontier (Set.range f) := by
          rw [← front e he,← front f hf]
          have heq : e ∘ b=f ∘ b := by funext z; exact hag (b z) z.property
          rw [heq]
        have hJe : IsJordanCurve (frontier (Set.range e)) :=
          (front e he) ▸ (hboundary (e ∘ b) (he.comp hb)).1
        have hJf : IsJordanCurve (frontier (Set.range f)) := hfront ▸ hJe
        have heq := hside (Set.range e) (isCompact_range he.continuous)
          (hinterior e he).1 (hinterior e he).2 hJe
        have hfq := hside (Set.range f) (isCompact_range hf.continuous)
          (hinterior f hf).1 (hinterior f hf).2 hJf
        rw [heq,hfq,hfront]
      have patch (A : Set Plane) (hA : IsClosed A) (e : A ≃ₜ A)
          (he : ∀ (x : A), (x : Plane) ∈ frontier A → (e x : Plane) = x) :
          ∃ H : Plane ≃ₜ Plane,
            (∀ x : A,H x = e x) ∧ (∀ x, x ∉ interior A → H x = x) := by
        classical
        obtain ⟨f,g,hfg,hfe⟩ := exists_isHomeoOn_of_homeomorph e
        let C := (interior A)ᶜ
        have hC : IsClosed C := isOpen_interior.isClosed_compl
        have hid : IsHomeoOn id id C C :=
          ⟨fun _ h => h,fun _ h => h,continuous_id.continuousOn,
            continuous_id.continuousOn,fun _ _ => rfl,fun _ _ => rfl⟩
        have hagree : ∀ x ∈ A ∩ C, f x = id x := by
          intro x hx
          rw [hfe x hx.1]
          apply he
          rw [frontier,hA.closure_eq]
          exact hx
        have him : f '' (A ∩ C) = A ∩ C := by
          ext x
          constructor
          · rintro ⟨y,hy,rfl⟩
            rw [hagree y hy]
            exact hy
          · intro hx
            exact ⟨x,hx,hagree x hx⟩
        obtain ⟨F,G,hFG,hF,hFC⟩ := glue_closed_homeoOn hA hC hA hC hfg hid hagree him
        have hcover : A ∪ C = univ := by
          apply Set.eq_univ_of_forall
          intro x
          by_cases hx : x ∈ interior A
          · exact Or.inl (interior_subset hx)
          · exact Or.inr hx
        rw [hcover] at hFG
        refine ⟨hFG.homeomorphOfUniv,?_,?_⟩
        · intro x
          exact (hF x x.property).trans (hfe x x.property)
        · intro x hx
          exact hFC x hx
      classical
      let Q := Plane.closedSquare 0 1
      letI : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
      have bounds (z : Q) : |z.val 0|≤1 ∧ |z.val 1|≤1 := by
        have hh : max |z.val 0| |z.val 1|≤1 := by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
        exact ⟨(le_max_left _ _).trans hh,(le_max_right _ _).trans hh⟩
      let J : Q → Q := fun z => ⟨Plane.mk (z.val 0) ((z.val 1+1)/2),by
        have hz := bounds z
        have hy : |(z.val 1+1)/2|≤1 := abs_le.mpr ⟨by nlinarith [(abs_le.mp hz.2).1],by nlinarith [(abs_le.mp hz.2).2]⟩
        simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using max_le hz.1 hy⟩
      have hJc : Continuous J := by dsimp [J]; fun_prop
      have hJi : Function.Injective J := by
        intro z w he
        have hx := congrArg (fun z : Q => z.val 0) he
        have hy := congrArg (fun z : Q => z.val 1) he
        apply Subtype.ext
        apply PiLp.ext
        intro i
        fin_cases i
        · exact hx
        · change (z.val 1+1)/2=(w.val 1+1)/2 at hy
          change z.val 1=w.val 1
          linarith
      have hJe : IsEmbedding J := (hJc.isClosedEmbedding hJi).isEmbedding
      have hJpos (z : Q) : 0≤(J z).val 1 := by
        change 0≤(z.val 1+1)/2
        nlinarith [(abs_le.mp (bounds z).2).1]
      have axisB (z : Q) (hz : z.val 1=0) : B z=z := by
        let t : Icc (-1 : ℝ) 1 := ⟨z.val 0,abs_le.mp (bounds z).1⟩
        have he : z=⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := by
          apply Subtype.ext
          apply PiLp.ext
          intro i
          fin_cases i
          · rfl
          · exact hz
        rw [he,hc]
      have hJboundary (z : Q) (hz : z.val ∈ modelCurve) :
          (J z).val 1=0 ∨ (J z).val ∈ modelCurve := by
        have hm : max |z.val 0| |z.val 1|=1 := hz
        by_cases hy : z.val 1= -1
        · left
          change (z.val 1+1)/2=0
          rw [hy]; norm_num
        · right
          have hb := bounds z
          by_cases hx : |z.val 0|=1
          · change max |z.val 0| |(z.val 1+1)/2|=1
            have hj : 0≤(z.val 1+1)/2 := hJpos z
            rw [hx,abs_of_nonneg hj,max_eq_left]
            nlinarith [(abs_le.mp hb.2).2]
          · have hxlt : |z.val 0|<1 := lt_of_le_of_ne hb.1 hx
            have hyabs : |z.val 1|=1 := by
              apply le_antisymm hb.2
              by_contra hh
              have hlt := max_lt hxlt (lt_of_not_ge hh)
              rw [hm] at hlt
              exact lt_irrefl _ hlt
            have hy1 : z.val 1=1 := by
              rcases le_total 0 (z.val 1) with hs | hs
              · rwa [abs_of_nonneg hs] at hyabs
              · rw [abs_of_nonpos hs] at hyabs
                have heq : z.val 1= -1 := by linarith
                exact False.elim (hy heq)
            change max |z.val 0| |(z.val 1+1)/2|=1
            rw [hy1]
            norm_num only
            exact max_eq_right hb.1
      obtain ⟨F,hFfix,hFneg,hFboundary⟩ := boundary R hR B hB hBU hc hside
      let e : Q → Plane := F ∘ Subtype.val ∘ J
      let f : Q → Plane := B ∘ J
      have hei : IsEmbedding e := F.isEmbedding.comp (IsEmbedding.subtypeVal.comp hJe)
      have hfi : IsEmbedding f := hB.comp hJe
      have hag : ∀ z : Q,z.val ∈ modelCurve → e z=f z := by
        intro z hz
        rcases hJboundary z hz with hzero | hcurve
        · exact (hFneg (J z) hzero.le).trans (axisB (J z) hzero).symm
        · exact hFboundary (J z) hcurve (hJpos z)
      have hrange : Set.range e=Set.range f := sameRange e f hei hfi hag
      let A := Set.range e
      let E := hei.toHomeomorph
      let D := hfi.toHomeomorph
      let C : A ≃ₜ A := E.symm.trans (D.trans (Homeomorph.setCongr hrange.symm))
      have hC (z : Q) : (C (E z) : Plane)=f z := by
        change (D (E.symm (E z)) : Plane)=f z
        rw [E.symm_apply_apply]
        rfl
      have hclosed : IsClosed A := (isCompact_range hei.continuous).isClosed
      have hCfront (x : A) (hx : (x:Plane) ∈ frontier A) : (C x : Plane)=x := by
        have hh : (x:Plane) ∈ e '' {z : Q | (z:Plane) ∈ frontier Q} := by
          rw [embedded_compact_planar_region_frontier_probe Q (isCompact_closedSquare 0 1) e hei]
          exact hx
        obtain ⟨z,hz,hzx⟩ := hh
        have hxE : E z=x := Subtype.ext hzx
        rw [← hxE,hC]
        have hzm : z.val ∈ modelCurve := by rw [modelCurve_eq_frontier]; exact hz
        exact (hag z hzm).symm
      obtain ⟨K,hKcore,hKfix⟩ := patch A hclosed C hCfront
      have hposA : interior A ⊆ {z : Plane | 0<z 1} := by
        intro z hz
        have hz' : z ∈ interior (Set.range f) := hrange ▸ hz
        obtain ⟨q,hq⟩ := interior_subset hz'
        have hi := (embedded_planar_region_interior_iff_probe Q f hfi q).mp (hq.symm ▸ hz')
        rw [Plane.interior_closedSquare] at hi
        have hiR : max |q.val 0| |q.val 1|<1 := by simpa [Plane.openSquare,Plane.supDist,Plane.supNorm] using hi
        have hy : -1<q.val 1 := (abs_lt.mp (lt_of_le_of_lt (le_max_right _ _) hiR)).1
        have hJgt : 0<(J q).val 1 := by change 0<(q.val 1+1)/2; linarith
        have hh := hside (J q) hJgt
        change 0<f q 1 at hh
        rwa [hq] at hh
      have hAU : A ⊆ Plane.openSquare 0 R := by
        intro z hz
        have hz' : z ∈ Set.range f := hrange ▸ hz
        obtain ⟨q,rfl⟩ := hz'
        exact hBU (Set.mem_range_self (J q))
      let H : Plane ≃ₜ Plane := F.trans K
      have hHJ (q : Q) : H (J q)=B (J q) := by
        change K (e q)=f q
        have hh := hKcore (E q)
        exact hh.trans (hC q)
      refine ⟨H,?_,?_,?_⟩
      · intro z hz
        change K (F z)=z
        rw [hFfix z hz]
        apply hKfix
        intro hi
        exact hz (hAU (interior_subset hi))
      · intro z hz
        change K (F z)=z
        rw [hFneg z hz]
        apply hKfix
        intro hi
        exact not_lt_of_ge hz (hposA hi)
      · intro z hz
        let q : Q := ⟨Plane.mk (z.val 0) (2*z.val 1-1),by
          have hb := bounds z
          have hy : |2*z.val 1-1|≤1 := abs_le.mpr ⟨by linarith,by nlinarith [(abs_le.mp hb.2).2]⟩
          simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using max_le hb.1 hy⟩
        have hq : J q=z := by
          apply Subtype.ext
          apply PiLp.ext
          intro i
          fin_cases i
          · rfl
          · change ((2*z.val 1-1)+1)/2=z.val 1; ring
        have hh := hHJ q
        rwa [hq] at hh
    classical
    let Q := Plane.closedSquare 0 1
    letI : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
    let Y : Plane ≃ₜ Plane := {
      toFun := fun z => Plane.mk (z 0) (-z 1)
      invFun := fun z => Plane.mk (z 0) (-z 1)
      left_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
      right_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop
    }
    have hYY (z : Plane) : Y (Y z)=z := Y.symm_apply_apply z
    have hYopen (z : Plane) : Y z ∈ Plane.openSquare 0 R ↔ z ∈ Plane.openSquare 0 R := by
      simp [Y,Plane.openSquare,Plane.supDist,Plane.supNorm,Plane.mk]
    let T : Q → Q := fun z => ⟨Y z,by simpa [Y,Q,Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk] using z.property⟩
    have hTc : Continuous T := (Y.continuous.comp continuous_subtype_val).subtype_mk _
    have hTi : Function.Injective T := by
      intro z w he
      apply Subtype.ext
      exact Y.injective (congrArg Subtype.val he)
    have hTe : IsEmbedding T := (hTc.isClosedEmbedding hTi).isEmbedding
    have hTT (z : Q) : T (T z)=z := Subtype.ext (hYY z)
    have hTaxis (t : Icc (-1 : ℝ) 1) :
        T ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ =
        ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := by
      apply Subtype.ext
      simp [T,Y,Plane.mk]
    let M : Q → Plane := Y ∘ B ∘ T
    have hM : IsEmbedding M := Y.isEmbedding.comp (hB.comp hTe)
    have hMU : Set.range M ⊆ Plane.openSquare 0 R := by
      rintro z ⟨q,rfl⟩
      exact (hYopen (B (T q))).mpr (hBU (Set.mem_range_self _))
    have hMc (t : Icc (-1 : ℝ) 1) :
        M ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩=Plane.mk t 0 := by
      change Y (B (T _))=Plane.mk t 0
      rw [hTaxis,hc]
      simp [Y,Plane.mk]
    have hMp (z : Q) (hz : 0<z.val 1) : 0<M z 1 := by
      have hn : (T z).val 1<0 := by change -z.val 1<0; linarith
      have hh := hminus (T z) hn
      change 0< -(B (T z) 1)
      linarith
    obtain ⟨P,hPfix,hPneg,hPcore⟩ := positive R hR B hB hBU hc hplus
    obtain ⟨N,hNfix,hNneg,hNcore⟩ := positive R hR M hM hMU hMc hMp
    let F : Plane ≃ₜ Plane := (Y.trans N).trans Y
    have hFfix (z : Plane) (hz : z ∉ Plane.openSquare 0 R) : F z=z := by
      change Y (N (Y z))=z
      have hy : Y z ∉ Plane.openSquare 0 R := fun h => hz ((hYopen z).mp h)
      rw [hNfix _ hy,hYY]
    have hFpos (z : Plane) (hz : 0≤z 1) : F z=z := by
      change Y (N (Y z))=z
      have hy : (Y z) 1≤0 := by change -z 1≤0; linarith
      rw [hNneg _ hy,hYY]
    have hFcore (z : Q) (hz : z.val 1≤0) : F z=B z := by
      change Y (N (T z).val)=B z
      have hy : 0≤(T z).val 1 := by change 0≤ -z.val 1; linarith
      rw [hNcore (T z) hy]
      change Y (Y (B (T (T z))))=B z
      rw [hTT,hYY]
    let H : Plane ≃ₜ Plane := P.trans F
    refine ⟨H,?_,?_,?_⟩
    · intro z hz
      change F (P z)=z
      rw [hPfix _ hz,hFfix _ hz]
    · intro t
      change F (P (Plane.mk t 0))=Plane.mk t 0
      rw [hPneg _ (by simp [Plane.mk]),hFpos _ (by simp [Plane.mk])]
    · intro z
      change F (P z.val)=B z
      rcases le_or_gt (z.val 1) 0 with hn | hp
      · rw [hPneg _ hn,hFcore z hn]
      · rw [hPcore z hp.le,hFpos _ (hplus z hp).le]
  classical
  let Q := Plane.closedSquare 0 1
  letI : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  let Y : Plane ≃ₜ Plane := {
    toFun := fun z => Plane.mk (z 0) (-z 1)
    invFun := fun z => Plane.mk (z 0) (-z 1)
    left_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
    right_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop
  }
  have hYY (z : Plane) : Y (Y z)=z := Y.symm_apply_apply z
  let T : Q → Q := fun z => ⟨Y z,by simpa [Y,Q,Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk] using z.property⟩
  have hTc : Continuous T := (Y.continuous.comp continuous_subtype_val).subtype_mk _
  have hTi : Function.Injective T := by
    intro z w he
    apply Subtype.ext
    exact Y.injective (congrArg Subtype.val he)
  have hTe : IsEmbedding T := (hTc.isClosedEmbedding hTi).isEmbedding
  have hTT (z : Q) : T (T z)=z := Subtype.ext (hYY z)
  have hTaxis (t : Icc (-1 : ℝ) 1) :
      T ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ =
      ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := by
    apply Subtype.ext
    simp [T,Y,Plane.mk]
  have haxis := recognize B hB hc hmeet
  have hB0 : B ⟨0,by simp [Plane.closedSquare,Plane.supDist,Plane.supNorm]⟩=0 := by
    have hh := hc ⟨0,by norm_num⟩
    have hz : Plane.mk 0 0=(0:Plane) := by apply PiLp.ext; intro i; fin_cases i <;> rfl
    simpa only [hz] using hh
  rcases sides B hB haxis hB0 with ⟨hp,hn⟩ | ⟨hp,hn⟩
  · obtain ⟨H,hHfix,hHaxis,hHcore⟩ := oriented R hR B hB hBU hc hp hn
    refine ⟨false,H,hHfix,hHaxis,?_⟩
    intro z
    have hz : Plane.mk (z.val 0) (z.val 1)=z.val := by
      apply PiLp.ext
      intro i
      fin_cases i <;> rfl
    change H (Plane.mk (z.val 0) (z.val 1))=B z
    rw [hz,hHcore]
  · let C : Q → Plane := B ∘ T
    have hC : IsEmbedding C := hB.comp hTe
    have hCU : Set.range C ⊆ Plane.openSquare 0 R := by
      rintro z ⟨q,rfl⟩
      exact hBU (Set.mem_range_self (T q))
    have hCc (t : Icc (-1 : ℝ) 1) :
        C ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩=Plane.mk t 0 := by
      change B (T _)=Plane.mk t 0
      rw [hTaxis,hc]
    have hCp (z : Q) (hz : 0<z.val 1) : 0<C z 1 := by
      have ht : (T z).val 1<0 := by change -z.val 1<0; linarith
      exact hn (T z) ht
    have hCn (z : Q) (hz : z.val 1<0) : C z 1<0 := by
      have ht : 0<(T z).val 1 := by change 0< -z.val 1; linarith
      exact hp (T z) ht
    obtain ⟨H,hHfix,hHaxis,hHcore⟩ := oriented R hR C hC hCU hCc hCp hCn
    refine ⟨true,H,hHfix,hHaxis,?_⟩
    intro z
    change H (T z).val=B z
    rw [hHcore]
    change B (T (T z))=B z
    rw [hTT]
end CurveComplex
