import CurveComplexGenusTwo.Topology.BandGlobalGluing.FullSquareExtensionHeader
import CurveComplexGenusTwo.Topology.BandGlobalGluing.ParametrizedCrosscutScaffold
import CurveComplexGenusTwo.Topology.Extraction
import CurveComplexGenusTwo.Topology.TopologicalArcJoin
import Schoenflies.JordanClosed
import Schoenflies.Subarc
import Schoenflies.Concatenate
set_option maxHeartbeats 2000000
open Set Topology unitInterval
namespace CurveComplex
open Schoenflies

/-- A collar of the whole actual exterior whisker, preserving its entire path
parametrization and a nonzero full-width attachment to the actual old square.
The requested open support contains the whole whisker. -/
theorem actual_whole_exterior_whisker_half_collar
    {z : Plane} (p : Path (Plane.mk 1 0) z) (hp : IsEmbedding p)
    (hmeet : Set.range p ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0})
    (U : Set Plane) (hU : IsOpen U) (hpU : Set.range p ⊆ U) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 ∧
      ∃ E : I × Icc (-1 : ℝ) 1 → Plane,
        IsEmbedding E ∧
        (∀ w : Icc (-1 : ℝ) 1, E (0,w) = Plane.mk 1 (rho*w)) ∧
        (∀ t : I, E (t,⟨0,by norm_num⟩) = p t) ∧
        Set.range E ⊆ U ∧
        Set.range E ∩ Plane.closedSquare 0 1 =
          (fun w : Icc (-1 : ℝ) 1 => Plane.mk 1 (rho*w)) '' Set.univ := by
  have complement (P : Set Plane) (z : Plane)
      (hP : IsArcBetween P (Plane.mk 1 0) z)
      (hmeet : P ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0}) :
      ∃ c : Path z (Plane.mk (-1) 0), IsEmbedding c ∧
        Set.range c ∩ P = {z} ∧
        Set.range c ∩ Plane.closedSquare 0 1 = {Plane.mk (-1) 0} := by
    have exterior (P : Set Plane) (z : Plane)
        (hP : IsArcBetween P (Plane.mk 1 0) z)
        (hmeet : P ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0})
        (u w : Plane) (hu : u ∉ Plane.closedSquare 0 1 ∪ P)
        (hw : w ∉ Plane.closedSquare 0 1 ∪ P) (huw : u ≠ w) :
        ∃ A ⊆ (Plane.closedSquare 0 1 ∪ P)ᶜ, IsPolygonal A ∧ IsArcBetween A u w := by
      have paths (P : Set Plane) (z : Plane)
          (hP : IsArcBetween P (Plane.mk 1 0) z)
          (hmeet : P ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0})
          (u w : Plane) (hu : u ∉ Plane.closedSquare 0 1 ∪ P)
          (hw : w ∉ Plane.closedSquare 0 1 ∪ P) :
          ∃ g : Path u w, ∀ t : I, g t ∉ Plane.closedSquare 0 1 ∪ P := by
        have radial (P : Set Plane)
            (hP : P ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0})
            (v : Plane) (hvP : v ∉ P)
            (hvD : ¬ (v 1 = 0 ∧ -1 ≤ v 0 ∧ v 0 ≤ 1)) :
            let R := (max 1 (Plane.supNorm v) / Plane.supNorm v) • v
            1 ≤ Plane.supNorm R ∧ R ∉ P := by
          dsimp only
          let s := Plane.supNorm v
          have hs : 0 < s := by
            have hs0 := Plane.supNorm_nonneg v
            have h0 := Plane.abs_zero_le_supNorm v
            have h1 := Plane.abs_one_le_supNorm v
            by_contra hn
            have hz : s = 0 := by dsimp [s] at *; linarith
            have hx : v 0 = 0 := by dsimp [s] at hz; rw [hz] at h0; exact abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
            have hy : v 1 = 0 := by dsimp [s] at hz; rw [hz] at h1; exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
            exact hvD ⟨hy, by rw [hx]; norm_num, by rw [hx]; norm_num⟩
          have ha : 0 < max 1 s / s := div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hs
          have hnorm : Plane.supNorm ((max 1 s / s) • v) = max 1 s := by
            rw [Plane.supNorm_smul, abs_of_pos ha]
            change max 1 s / s * s = max 1 s
            exact div_mul_cancel₀ _ (ne_of_gt hs)
          refine ⟨?_, ?_⟩
          · change 1 ≤ Plane.supNorm ((max 1 s / s) • v)
            rw [hnorm]; exact le_max_left _ _
          · change (max 1 s / s) • v ∉ P
            by_cases hbig : 1 ≤ s
            · simpa [max_eq_right hbig, div_self (ne_of_gt hs)] using hvP
            · have hsmall : s ≤ 1 := le_of_lt (lt_of_not_ge hbig)
              have heq : (max 1 s / s) • v ∈ P → (max 1 s / s) • v = Plane.mk 1 0 := by
                intro hmem
                have hh : (max 1 s / s) • v ∈ P ∩ Plane.closedSquare 0 1 :=
                  ⟨hmem, mem_closedSquare_zero_one.mpr (by rw [hnorm, max_eq_left hsmall])⟩
                rw [hP] at hh
                exact hh
              intro hmem
              have he := heq hmem
              have hx := congrArg (fun z : Plane => z 0) he
              have hy := congrArg (fun z : Plane => z 1) he
              simp only [PiLp.smul_apply, smul_eq_mul, Plane.mk_zero, Plane.mk_one,
                max_eq_left hsmall, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hx hy
              have hx' : v 0 = s := by field_simp at hx; nlinarith
              have hy' : v 1 = 0 := (mul_eq_zero.mp hy).resolve_left (ne_of_gt (div_pos zero_lt_one hs))
              exact hvD ⟨hy', by rw [hx']; linarith, by rw [hx']; exact hsmall⟩
        have perturb (f : I → Plane) (hf : Continuous f)
            (hpos : ∀ t, 0 < Plane.supNorm (f t))
            (P : Set Plane) (hP : IsClosed P)
            (havoid : ∀ t, (max 1 (Plane.supNorm (f t)) / Plane.supNorm (f t)) • f t ∉ P)
            (hleft : 1 < Plane.supNorm (f 0)) (hright : 1 < Plane.supNorm (f 1)) :
            ∃ delta : ℝ, 0 < delta ∧
              ∃ g : Path (f 0) (f 1), ∀ t : I,
                g t ∉ P ∧ g t ∉ Plane.closedSquare 0 1 := by
          let R : I × ℝ → Plane := fun z =>
            (max (1+z.2) (Plane.supNorm (f z.1)) / Plane.supNorm (f z.1)) • f z.1
          have hs : Continuous (fun z : I × ℝ => Plane.supNorm (f z.1)) := by
            unfold Plane.supNorm
            exact (show Continuous (fun z : I × ℝ => |f z.1 0|) from by fun_prop).max
              (show Continuous (fun z : I × ℝ => |f z.1 1|) from by fun_prop)
          have hRc : Continuous R := by
            have hc : Continuous (fun z : I × ℝ => max (1+z.2) (Plane.supNorm (f z.1)) / Plane.supNorm (f z.1)) :=
              ((continuous_const.add continuous_snd).max hs).div hs
                (fun z => ne_of_gt (hpos z.1))
            exact hc.smul (hf.comp continuous_fst)
          let O : Set (I × ℝ) := R ⁻¹' Pᶜ
          have hO : IsOpen O := hP.isOpen_compl.preimage hRc
          have hbase : Set.univ ×ˢ ({0} : Set ℝ) ⊆ O := by
            rintro ⟨t,r⟩ ⟨_,hr⟩
            have hr0 : r = 0 := hr
            subst r
            simpa [O,R] using havoid t
          obtain ⟨A,B,hA,hB,hUA,h0B,hAB⟩ := generalized_tube_lemma
            isCompact_univ isCompact_singleton hO hbase
          obtain ⟨eps,heps,hepsB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds (h0B (Set.mem_singleton (0 : ℝ))))
          let delta := min (eps/2) (min ((Plane.supNorm (f 0)-1)/2) ((Plane.supNorm (f 1)-1)/2))
          have hd : 0 < delta := by dsimp [delta]; positivity
          have hde : delta < eps := by
            have hh := min_le_left (eps/2) (min ((Plane.supNorm (f 0)-1)/2) ((Plane.supNorm (f 1)-1)/2))
            dsimp [delta]; linarith
          have hdl : 1+delta ≤ Plane.supNorm (f 0) := by
            have hh := (min_le_right (eps/2) (min ((Plane.supNorm (f 0)-1)/2) ((Plane.supNorm (f 1)-1)/2))).trans (min_le_left _ _)
            dsimp [delta]; linarith
          have hdr : 1+delta ≤ Plane.supNorm (f 1) := by
            have hh := (min_le_right (eps/2) (min ((Plane.supNorm (f 0)-1)/2) ((Plane.supNorm (f 1)-1)/2))).trans (min_le_right _ _)
            dsimp [delta]; linarith
          have hdB : delta ∈ B := hepsB (by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hd] using hde)
          let g : Path (f 0) (f 1) :=
            { toFun := fun t => R (t,delta)
              continuous_toFun := hRc.comp (continuous_id.prodMk continuous_const)
              source' := by dsimp [R]; simp [max_eq_right hdl, div_self (ne_of_gt (hpos 0))]
              target' := by dsimp [R]; simp [max_eq_right hdr, div_self (ne_of_gt (hpos 1))] }
          refine ⟨delta,hd,g,?_⟩
          intro t
          refine ⟨hAB ⟨hUA trivial,hdB⟩,?_⟩
          intro hmem
          have hb := mem_closedSquare_zero_one.mp hmem
          change Plane.supNorm ((max (1+delta) (Plane.supNorm (f t)) / Plane.supNorm (f t)) • f t) ≤ 1 at hb
          rw [Plane.supNorm_smul, abs_of_pos (div_pos (lt_of_lt_of_le (by linarith : 0 < 1+delta) (le_max_left _ _)) (hpos t)), div_mul_cancel₀ _ (ne_of_gt (hpos t))] at hb
          have hh := le_max_left (1+delta) (Plane.supNorm (f t))
          linarith
        let D : Set Plane := {v | v 1 = 0 ∧ -1 ≤ v 0 ∧ v 0 ≤ 1}
        have hD : IsArcBetween D (Plane.mk (-1) 0) (Plane.mk 1 0) := by
          refine ⟨fun t => Plane.mk (-1+2*t) 0, ?_, ?_, ?_, ?_, ?_⟩
          · fun_prop
          · intro t ht s hs he
            have hh := congrArg (fun q : Plane => q 0) he
            change -1+2*t = -1+2*s at hh
            linarith
          · ext v
            constructor
            · rintro ⟨t,ht,rfl⟩
              change 0 = 0 ∧ -1 ≤ -1+2*t ∧ -1+2*t ≤ 1
              exact ⟨rfl,by linarith [ht.1],by linarith [ht.2]⟩
            · intro hv
              refine ⟨(v 0+1)/2,⟨by linarith [hv.2.1],by linarith [hv.2.2]⟩,?_⟩
              ext i
              fin_cases i
              · change -1+2*((v 0+1)/2)=v 0; ring
              · change 0=v 1; exact hv.1.symm
          · norm_num
          · norm_num
        have hDQ : D ⊆ Plane.closedSquare 0 1 := by
          intro v hv
          rw [mem_closedSquare_zero_one]
          change max |v 0| |v 1| ≤ 1
          exact max_le (abs_le.mpr hv.2) (by rw [hv.1]; norm_num)
        have hDP : ∀ v ∈ D, v ∈ P → v = Plane.mk 1 0 := by
          intro v hv hp
          have hh : v ∈ P ∩ Plane.closedSquare 0 1 := ⟨hp,hDQ hv⟩
          rw [hmeet] at hh
          exact hh
        have hA : IsArc (D ∪ P) := (hD.concatenate hP hDP).isArc
        by_cases huw : u = w
        · subst w
          refine ⟨Path.refl u,?_⟩
          intro t
          exact hu
        obtain ⟨Q,_,hQ,hQA⟩ := arc_complement_poly hA huw
          (fun h => hu (h.elim (fun hv => Or.inl (hDQ hv)) Or.inr))
          (fun h => hw (h.elim (fun hv => Or.inl (hDQ hv)) Or.inr))
        obtain ⟨q,hqc,hqi,hqim,hq0,hq1⟩ := hQ
        let f : I → Plane := fun t => q t
        have hfc : Continuous f := hqc.comp_continuous continuous_subtype_val (fun t => t.property)
        have hfavoid (t : I) : f t ∉ D ∪ P := hQA (hqim ▸ Set.mem_image_of_mem q t.property)
        have hpos (t : I) : 0 < Plane.supNorm (f t) := by
          have hn := Plane.supNorm_nonneg (f t)
          by_contra hh
          have he : Plane.supNorm (f t) = 0 := by linarith
          have hx := Plane.abs_zero_le_supNorm (f t)
          have hy := Plane.abs_one_le_supNorm (f t)
          rw [he] at hx hy
          have hx0 : f t 0 = 0 := abs_eq_zero.mp (le_antisymm hx (abs_nonneg _))
          have hy0 : f t 1 = 0 := abs_eq_zero.mp (le_antisymm hy (abs_nonneg _))
          exact hfavoid t (Or.inl ⟨hy0,by rw [hx0]; norm_num,by rw [hx0]; norm_num⟩)
        have hrad (t : I) : (max 1 (Plane.supNorm (f t)) / Plane.supNorm (f t)) • f t ∉ P :=
          (radial P hmeet (f t) (fun hp => hfavoid t (Or.inr hp))
            (fun hd => hfavoid t (Or.inl hd))).2
        have hleft : 1 < Plane.supNorm (f 0) := by
          have hnot : u ∉ Plane.closedSquare 0 1 := fun hh => hu (Or.inl hh)
          rw [mem_closedSquare_zero_one] at hnot
          simpa [f,hq0] using lt_of_not_ge hnot
        have hright : 1 < Plane.supNorm (f 1) := by
          have hnot : w ∉ Plane.closedSquare 0 1 := fun hh => hw (Or.inl hh)
          rw [mem_closedSquare_zero_one] at hnot
          simpa [f,hq1] using lt_of_not_ge hnot
        obtain ⟨delta,hd,g,hg⟩ := perturb f hfc hpos P hP.isArc.isCompact.isClosed hrad hleft hright
        have h0 : f 0 = u := hq0
        have h1 : f 1 = w := hq1
        refine ⟨g.cast h0.symm h1.symm,?_⟩
        intro t hh
        exact hh.elim (hg t).2 (hg t).1
      let O := (Plane.closedSquare 0 1 ∪ P)ᶜ
      have hO : IsOpen O := ((Plane.isClosed_closedSquare 0 1).union hP.isArc.isCompact.isClosed).isOpen_compl
      have hconn : IsPathConnected O := by
        rw [isPathConnected_iff]
        refine ⟨⟨u,hu⟩,?_⟩
        intro a ha b hb
        exact paths P z hP hmeet a b ha hb
      exact exists_simple_arc_of_isPreconnected hO hconn.isConnected.isPreconnected hu hw huw
    have access (P : Set Plane) (z : Plane)
        (hP : IsArcBetween P (Plane.mk 1 0) z)
        (hmeet : P ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0}) :
        ∃ A : Set Plane, ∃ u : Plane,
          IsArcBetween A z u ∧ u ∉ P ∧
          A ⊆ (Plane.closedSquare 0 1)ᶜ ∧ A \ {z} ⊆ Pᶜ := by
      have hz : z ∉ Plane.closedSquare 0 1 := by
        intro hzQ
        have hh : z ∈ P ∩ Plane.closedSquare 0 1 := ⟨hP.right_mem,hzQ⟩
        rw [hmeet] at hh
        exact hP.ne (Set.mem_singleton_iff.mp hh).symm
      obtain ⟨E,v,hE,hv,havoid⟩ := endpoint_access_of_isArcBetween hP.reverse
      obtain ⟨f,hfc,hfi,hfim,hf0,hf1⟩ := hE
      let j : I → Plane := fun t => f t
      have hj : Continuous j := hfc.comp_continuous continuous_subtype_val (fun t => t.property)
      have hopen : IsOpen (j ⁻¹' (Plane.closedSquare 0 1)ᶜ) :=
        (Plane.isClosed_closedSquare 0 1).isOpen_compl.preimage hj
      have hzero : (0 : I) ∈ j ⁻¹' (Plane.closedSquare 0 1)ᶜ := by
        change f 0 ∉ Plane.closedSquare 0 1
        rw [hf0]; exact hz
      obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
      let d := min (eps/2) (1/2 : ℝ)
      have hd : 0 < d := by dsimp [d]; positivity
      have hd1 : d ≤ 1 := by have hh := min_le_right (eps/2) (1/2 : ℝ); dsimp [d]; linarith
      have hde : d < eps := by have hh := min_le_left (eps/2) (1/2 : ℝ); dsimp [d]; linarith
      let A := f '' uIcc 0 d
      have hA : IsArcBetween A z (f d) := by
        simpa only [hf0] using isArcBetween_subarc_of_injOn_I hfc hfi
          (by simp : (0 : ℝ) ∈ I) (show d ∈ I from ⟨hd.le,hd1⟩) hd.ne
      have hAE : A ⊆ E := by
        rw [← hfim]
        exact Set.image_mono (uIcc_subset_I (by simp) ⟨hd.le,hd1⟩)
      have hu : f d ≠ z := by
        intro hh
        have he := hfi ⟨hd.le,hd1⟩ (by simp) (hh.trans hf0.symm)
        exact hd.ne' he
      have huP : f d ∉ P := havoid ⟨hAE hA.right_mem,hu⟩
      refine ⟨A,f d,hA,huP,?_,?_⟩
      · rintro q ⟨t,ht,rfl⟩
        rw [uIcc_of_le hd.le] at ht
        let ti : I := ⟨t,⟨ht.1,ht.2.trans hd1⟩⟩
        have hdist : dist ti (0 : I) < eps := by
          change dist t (0 : ℝ) < eps
          rw [Real.dist_eq,sub_zero,abs_of_nonneg ht.1]
          exact ht.2.trans_lt hde
        exact hball hdist
      · intro q hq
        exact havoid ⟨hAE hq.1,hq.2⟩
    have opposite (P : Set Plane) (hP : IsClosed P)
        (hmeet : P ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0}) :
        ∃ A : Set Plane, ∃ u : Plane,
          IsArcBetween A (Plane.mk (-1) 0) u ∧
          A ⊆ Pᶜ ∧ u ∉ Plane.closedSquare 0 1 ∧
          A ∩ Plane.closedSquare 0 1 = {Plane.mk (-1) 0} := by
      let b := Plane.mk (-1) 0
      have hbQ : b ∈ Plane.closedSquare 0 1 := by
        rw [mem_closedSquare_zero_one]; norm_num [b,Plane.supNorm,Plane.mk]
      have hbP : b ∉ P := by
        intro hh
        have hmem : b ∈ P ∩ Plane.closedSquare 0 1 := ⟨hh,hbQ⟩
        rw [hmeet] at hmem
        have he := congrArg (fun q : Plane => q 0) (Set.mem_singleton_iff.mp hmem)
        norm_num [b,Plane.mk] at he
      let f : ℝ → Plane := fun t => Plane.mk (-1-t) 0
      have hfc : Continuous f := by fun_prop
      have hzero : (0 : ℝ) ∈ f ⁻¹' Pᶜ := by simpa [f,b] using hbP
      obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp
        ((hP.isOpen_compl.preimage hfc).mem_nhds hzero)
      let d := min (eps/2) (1/2 : ℝ)
      have hd : 0 < d := by dsimp [d]; positivity
      have hd1 : d ≤ 1 := by have hh := min_le_right (eps/2) (1/2 : ℝ); dsimp [d]; linarith
      have hde : d < eps := by have hh := min_le_left (eps/2) (1/2 : ℝ); dsimp [d]; linarith
      have hfi : InjOn f I := by
        intro t ht s hs he
        have hh := congrArg (fun q : Plane => q 0) he
        change -1-t = -1-s at hh
        linarith
      let A := f '' uIcc 0 d
      have hA : IsArcBetween A b (f d) := by
        simpa only [f,sub_zero] using isArcBetween_subarc_of_injOn_I hfc.continuousOn hfi
          (by simp : (0 : ℝ) ∈ I) (show d ∈ I from ⟨hd.le,hd1⟩) hd.ne
      have havoid : A ⊆ Pᶜ := by
        rintro q ⟨t,ht,rfl⟩
        rw [uIcc_of_le hd.le] at ht
        apply hball
        change dist t (0 : ℝ) < eps
        rw [Real.dist_eq,sub_zero,abs_of_nonneg ht.1]
        exact ht.2.trans_lt hde
      have hfar : f d ∉ Plane.closedSquare 0 1 := by
        intro hh
        have hx := abs_le.mp ((Plane.abs_zero_le_supNorm (f d)).trans (mem_closedSquare_zero_one.mp hh))
        change -1 ≤ -1-d ∧ -1-d ≤ 1 at hx
        linarith [hx.1]
      refine ⟨A,f d,hA,havoid,hfar,?_⟩
      ext q
      constructor
      · rintro ⟨⟨t,ht,rfl⟩,hQ⟩
        rw [uIcc_of_le hd.le] at ht
        have hx := abs_le.mp ((Plane.abs_zero_le_supNorm (f t)).trans (mem_closedSquare_zero_one.mp hQ))
        have ht0 : t = 0 := by change -1 ≤ -1-t ∧ -1-t ≤ 1 at hx; linarith [hx.1,ht.1]
        rw [ht0]
        simp [f,b]
      · intro hq
        have he : q = b := hq
        rw [he]
        exact ⟨hA.left_mem,hbQ⟩
    let b := Plane.mk (-1) 0
    obtain ⟨E,u,hE,huP,hEQ,hEP⟩ := access P z hP hmeet
    obtain ⟨B,v,hB,hBP,hvQ,hBQ⟩ := opposite P hP.isArc.isCompact.isClosed hmeet
    have huO : u ∉ Plane.closedSquare 0 1 ∪ P := by
      intro hh
      exact hh.elim (hEQ hE.right_mem) huP
    have hvO : v ∉ Plane.closedSquare 0 1 ∪ P := by
      intro hh
      exact hh.elim hvQ (hBP hB.right_mem)
    have hzQ : z ∉ Plane.closedSquare 0 1 := hEQ hE.left_mem
    have hzb : z ≠ b := by
      intro he
      apply hzQ
      rw [he,mem_closedSquare_zero_one]
      norm_num [b,Plane.supNorm,Plane.mk]
    have hjoin : ∃ C ⊆ E ∪ B ∪ (Plane.closedSquare 0 1 ∪ P)ᶜ,
        IsArcBetween C z b := by
      by_cases huv : u = v
      · obtain ⟨C,hsub,hC⟩ := exists_arc_in_union_of_arcs hE (huv ▸ hB.reverse) hzb
        exact ⟨C,hsub.trans (Set.subset_union_left),hC⟩
      · obtain ⟨Q,hQO,_,hQ⟩ := exterior P z hP hmeet u v huO hvO huv
        have hzv : z ≠ v := by intro hh; exact hvO (Or.inr (hh ▸ hP.right_mem))
        obtain ⟨D,hDEQ,hD⟩ := exists_arc_in_union_of_arcs hE hQ hzv
        obtain ⟨C,hCDB,hC⟩ := exists_arc_in_union_of_arcs hD hB.reverse hzb
        refine ⟨C,?_,hC⟩
        intro q hq
        rcases hCDB hq with hqD | hqB
        · rcases hDEQ hqD with hqE | hqQ
          · exact Or.inl (Or.inl hqE)
          · exact Or.inr (hQO hqQ)
        · exact Or.inl (Or.inr hqB)
    obtain ⟨C,hCsub,hC⟩ := hjoin
    have hCP : ∀ q ∈ C, q ∈ P → q = z := by
      intro q hq hp
      rcases hCsub hq with (hqE | hqB) | hqO
      · by_contra hn
        exact hEP ⟨hqE,hn⟩ hp
      · exact False.elim (hBP hqB hp)
      · exact False.elim (hqO (Or.inr hp))
    have hCQ : ∀ q ∈ C, q ∈ Plane.closedSquare 0 1 → q = b := by
      intro q hq hqQ
      rcases hCsub hq with (hqE | hqB) | hqO
      · exact False.elim (hEQ hqE hqQ)
      · have hh : q ∈ B ∩ Plane.closedSquare 0 1 := ⟨hqB,hqQ⟩
        rw [hBQ] at hh
        exact hh
      · exact False.elim (hqO (Or.inl hqQ))
    have hCleft := hC.left_mem
    have hCright := hC.right_mem
    obtain ⟨f,hfc,hfi,hfim,hf0,hf1⟩ := hC
    let c : Path z b := {
      toFun := fun t => f t
      continuous_toFun := hfc.comp_continuous continuous_subtype_val (fun t => t.property)
      source' := hf0
      target' := hf1 }
    have hci : Function.Injective c := by
      intro t u he
      apply Subtype.ext
      exact hfi t.property u.property he
    have hc : IsEmbedding c := (c.continuous.isClosedEmbedding hci).isEmbedding
    have hcRange : Set.range c = C := by
      rw [← hfim]
      ext q
      constructor
      · rintro ⟨t,rfl⟩; exact ⟨t,t.property,rfl⟩
      · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,rfl⟩
    refine ⟨c,hc,?_,?_⟩
    · rw [hcRange]
      ext q
      constructor
      · rintro ⟨hq,hqP⟩; exact hCP q hq hqP
      · intro hq
        have he : q = z := hq
        rw [he]
        exact ⟨hCleft,hP.right_mem⟩
    · rw [hcRange]
      ext q
      constructor
      · rintro ⟨hq,hqQ⟩; exact hCQ q hq hqQ
      · intro hq
        have he : q = b := hq
        rw [he]
        refine ⟨hCright,?_⟩
        rw [mem_closedSquare_zero_one]
        norm_num [b,Plane.supNorm,Plane.mk]
  have concatenate_path {z : Plane} (p : Path (Plane.mk 1 0) z) (hp : IsEmbedding p)
      (hmeet : Set.range p ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0})
      (c : Path z (Plane.mk (-1) 0)) (hc : IsEmbedding c)
      (hcP : Set.range c ∩ Set.range p = {z})
      (hcQ : Set.range c ∩ Plane.closedSquare 0 1 = {Plane.mk (-1) 0}) :
      ∃ f : I → Plane, IsEmbedding f ∧ f 0 = Plane.mk 1 0 ∧ f 1 = Plane.mk (-1) 0 ∧
        (∀ t : I, f ⟨(t : ℝ)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩ = p t) ∧
        Set.range f ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0,Plane.mk (-1) 0} := by
    have inj (a b : Plane) (r : Path a b) (hr : IsEmbedding r) : InjOn r.extend I := by
      intro t ht s hs he
      rw [r.extend_apply ht,r.extend_apply hs] at he
      exact congrArg Subtype.val (hr.injective he)
    have image (a b : Plane) (r : Path a b) : r.extend '' I = Set.range r := by
      ext q
      constructor
      · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,(r.extend_apply ht).symm⟩
      · rintro ⟨t,rfl⟩; exact ⟨t,t.property,r.extend_apply t.property⟩
    have hmid : p.extend 1 = c.extend 0 := by simp
    have hseam : ∀ q ∈ p.extend '' I, q ∈ c.extend '' I → q = p.extend 1 := by
      rw [image _ _ p,image _ _ c]
      intro q hqP hqC
      have hh : q ∈ Set.range c ∩ Set.range p := ⟨hqC,hqP⟩
      rw [hcP] at hh
      simpa using hh
    let r : ℝ → Plane := concatenate p.extend c.extend
    have hrc : ContinuousOn r I := continuousOn_concatenate p.continuous_extend.continuousOn c.continuous_extend.continuousOn hmid
    have hri : InjOn r I := injOn_concatenate (inj _ _ p hp) (inj _ _ c hc) hmid hseam
    let f : I → Plane := fun t => r t
    have hfc : Continuous f := hrc.comp_continuous continuous_subtype_val (fun t => t.property)
    have hfi : Function.Injective f := by intro t s he; apply Subtype.ext; exact hri t.property s.property he
    have hf0 : f 0 = Plane.mk 1 0 := by dsimp [f,r]; rw [concatenate_zero]; simp
    have hf1 : f 1 = Plane.mk (-1) 0 := by dsimp [f,r]; rw [concatenate_one]; simp
    have hfRange : Set.range f = Set.range p ∪ Set.range c := by
      have hrim := image_concatenate hmid
      rw [image _ _ p,image _ _ c] at hrim
      change Set.range (fun t : I => r t) = _
      rw [← hrim]
      ext q
      constructor
      · rintro ⟨t,rfl⟩; exact ⟨t,t.property,rfl⟩
      · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,rfl⟩
    refine ⟨f,(hfc.isClosedEmbedding hfi).isEmbedding,hf0,hf1,?_,?_⟩
    · intro t
      change concatenate p.extend c.extend ((t : ℝ)/2) = p t
      rw [concatenate_of_le (by linarith [t.property.2]),show 2*((t : ℝ)/2) = t by ring,p.extend_apply t.property]
    · rw [hfRange,union_inter_distrib_right,hmeet,hcQ]
      ext q
      simp [or_comm]
  have model : ∃ g : I → Plane, IsEmbedding g ∧
      g 0 = Plane.mk 1 0 ∧ g 1 = Plane.mk (-1) 0 ∧
      (∀ t : I, g ⟨(t : ℝ)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩ = Plane.mk (1/(1+t)) 0) ∧
      (∀ t : I, 0 < t → t < 1 → g t ∈ Plane.openSquare 0 1) := by
    let l : ℝ → Plane := fun t => Plane.mk (1/(1+t)) 0
    let r : ℝ → Plane := fun t => Plane.mk (1/2-(3/2)*t) 0
    have hden (t : ℝ) (ht : t ∈ I) : 0 < 1+t := by linarith [ht.1]
    have hlscalar : ContinuousOn (fun t : ℝ => 1/(1+t)) I :=
      continuousOn_const.div (continuousOn_const.add continuousOn_id) (fun t ht => ne_of_gt (hden t ht))
    have hlc : ContinuousOn l I := by dsimp [l]; fun_prop
    have hrc : ContinuousOn r I := by dsimp [r]; fun_prop
    have hli : InjOn l I := by
      intro t ht s hs he
      have hh := congrArg (fun v : Plane => v 0) he
      change 1/(1+t)=1/(1+s) at hh
      simp only [one_div,inv_inj] at hh
      linarith
    have hri : InjOn r I := by
      intro t ht s hs he
      have hh := congrArg (fun v : Plane => v 0) he
      change 1/2-(3/2)*t=1/2-(3/2)*s at hh
      linarith
    have hlb (t : ℝ) (ht : t ∈ I) : 1/2 ≤ (l t) 0 ∧ (l t) 0 ≤ 1 := by
      change 1/2 ≤ 1/(1+t) ∧ 1/(1+t) ≤ 1
      constructor
      · apply (le_div_iff₀ (hden t ht)).mpr; linarith [ht.2]
      · apply (div_le_one (hden t ht)).mpr; linarith [ht.1]
    have hrb (t : ℝ) (ht : t ∈ I) : -1 ≤ (r t) 0 ∧ (r t) 0 ≤ 1/2 := by
      change -1 ≤ 1/2-(3/2)*t ∧ 1/2-(3/2)*t ≤ 1/2
      constructor <;> linarith [ht.1,ht.2]
    have hmid : l 1 = r 0 := by norm_num [l,r]
    have hseam : ∀ q ∈ l '' I, q ∈ r '' I → q = l 1 := by
      rintro q ⟨t,ht,rfl⟩ ⟨s,hs,he⟩
      have hx := congrArg (fun v : Plane => v 0) he
      have hb := hlb t ht
      have hb' := hrb s hs
      have heq : (l t) 0 = 1/2 := by linarith
      ext i
      fin_cases i
      · change 1/(1+t)=1/(1+(1 : ℝ)); change 1/(1+t)=1/2 at heq; norm_num only [one_add_one_eq_two] ; exact heq
      · rfl
    let f := concatenate l r
    have hfc : ContinuousOn f I := continuousOn_concatenate hlc hrc hmid
    have hfi : InjOn f I := injOn_concatenate hli hri hmid hseam
    let g : I → Plane := fun t => f t
    have hgc : Continuous g := hfc.comp_continuous continuous_subtype_val (fun t => t.property)
    have hgi : Function.Injective g := by intro t s he; apply Subtype.ext; exact hfi t.property s.property he
    have hg0 : g 0 = Plane.mk 1 0 := by dsimp [g,f]; rw [concatenate_zero]; norm_num [l]
    have hg1 : g 1 = Plane.mk (-1) 0 := by dsimp [g,f]; rw [concatenate_one]; norm_num [r]
    have hgb (t : I) : -1 ≤ g t 0 ∧ g t 0 ≤ 1 ∧ g t 1 = 0 := by
      by_cases ht : (t : ℝ) ≤ 1/2
      · have ht' : 2*(t : ℝ) ∈ I := ⟨by linarith [t.property.1],by linarith⟩
        change -1 ≤ concatenate l r t 0 ∧ concatenate l r t 0 ≤ 1 ∧ concatenate l r t 1 = 0
        rw [concatenate_of_le ht]
        exact ⟨by linarith [(hlb _ ht').1],(hlb _ ht').2,rfl⟩
      · have ht' : 2*(t : ℝ)-1 ∈ I := ⟨by linarith [lt_of_not_ge ht],by linarith [t.property.2]⟩
        change -1 ≤ concatenate l r t 0 ∧ concatenate l r t 0 ≤ 1 ∧ concatenate l r t 1 = 0
        rw [concatenate_of_not_le ht]
        exact ⟨(hrb _ ht').1,by linarith [(hrb _ ht').2],rfl⟩
    refine ⟨g,(hgc.isClosedEmbedding hgi).isEmbedding,hg0,hg1,?_,?_⟩
    · intro t
      change concatenate l r ((t : ℝ)/2) = _
      rw [concatenate_of_le (by linarith [t.property.2]),show 2*((t : ℝ)/2)=t by ring]
    · intro t ht0 ht1
      have hb := hgb t
      have hx0 : -1 < g t 0 := by
        apply lt_of_le_of_ne hb.1
        intro hh
        have he : g t = Plane.mk (-1) 0 := by ext i; fin_cases i; exact hh.symm; exact hb.2.2
        have ht := hgi (he.trans hg1.symm)
        exact ht1.ne ht
      have hx1 : g t 0 < 1 := by
        apply lt_of_le_of_ne hb.2.1
        intro hh
        have he : g t = Plane.mk 1 0 := by ext i; fin_cases i; exact hh; exact hb.2.2
        have ht := hgi (he.trans hg0.symm)
        exact ht0.ne' ht
      rw [mem_openSquare_zero_one]
      change max |g t 0| |g t 1| < 1
      rw [hb.2.2,abs_zero]
      exact max_lt (abs_lt.mpr ⟨hx0,hx1⟩) (by norm_num)
  have inverted (f : I → Plane) (hf : IsEmbedding f)
      (hf0 : f 0 = Plane.mk 1 0) (hf1 : f 1 = Plane.mk (-1) 0)
      (hmeet : Set.range f ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0,Plane.mk (-1) 0}) :
      let J : Plane → Plane := fun v => (Plane.supNorm v)⁻¹^2 • v
      IsEmbedding (J ∘ f) ∧
        (J ∘ f) 0 = Plane.mk 1 0 ∧ (J ∘ f) 1 = Plane.mk (-1) 0 ∧
        (∀ t : I, 0 < t → t < 1 → (J ∘ f) t ∈ Plane.openSquare 0 1) ∧
        (0 : Plane) ∉ Set.range (J ∘ f) := by
    have invert (v : Plane) (hs : 0 < Plane.supNorm v) :
        let J : Plane → Plane := fun x => (Plane.supNorm x)⁻¹^2 • x
        Plane.supNorm (J v) = (Plane.supNorm v)⁻¹ ∧ J (J v) = v := by
      let J : Plane → Plane := fun x => (Plane.supNorm x)⁻¹^2 • x
      have hnorm : Plane.supNorm (J v) = (Plane.supNorm v)⁻¹ := by
        dsimp [J]
        rw [Plane.supNorm_smul,abs_of_nonneg (sq_nonneg _)]
        field_simp
      change Plane.supNorm (J v) = (Plane.supNorm v)⁻¹ ∧ J (J v) = v
      refine ⟨hnorm,?_⟩
      dsimp [J] at hnorm ⊢
      rw [hnorm,inv_inv,smul_smul]
      have he : Plane.supNorm v ^ 2 * (Plane.supNorm v)⁻¹ ^ 2 = 1 := by
        field_simp
      rw [he,one_smul]
    dsimp only
    let J : Plane → Plane := fun v => (Plane.supNorm v)⁻¹^2 • v
    have hge (t : I) : 1 ≤ Plane.supNorm (f t) := by
      by_contra hn
      have hQ : f t ∈ Plane.closedSquare 0 1 := mem_closedSquare_zero_one.mpr (le_of_lt (lt_of_not_ge hn))
      have hh : f t ∈ Set.range f ∩ Plane.closedSquare 0 1 := ⟨Set.mem_range_self _,hQ⟩
      rw [hmeet] at hh
      rcases Set.mem_insert_iff.mp hh with he | he
      · rw [he] at hn; norm_num [Plane.supNorm,Plane.mk] at hn
      · have he' : f t = Plane.mk (-1) 0 := he
        rw [he'] at hn; norm_num [Plane.supNorm,Plane.mk] at hn
    have hpos (t : I) : 0 < Plane.supNorm (f t) := lt_of_lt_of_le zero_lt_one (hge t)
    have hs : Continuous (fun t : I => Plane.supNorm (f t)) := by unfold Plane.supNorm; fun_prop
    have hc : Continuous (J ∘ f) := ((hs.inv₀ (fun t => ne_of_gt (hpos t))).pow 2).smul hf.continuous
    have hi : Function.Injective (J ∘ f) := by
      intro t u he
      apply hf.injective
      have ht := (invert (f t) (hpos t)).2
      have hu := (invert (f u) (hpos u)).2
      change J (J (f t)) = f t at ht
      change J (J (f u)) = f u at hu
      change J (f t) = J (f u) at he
      rw [← ht,← hu,he]
    have hJa : J (Plane.mk 1 0) = Plane.mk 1 0 := by norm_num [J,Plane.supNorm,Plane.mk]
    have hJb : J (Plane.mk (-1) 0) = Plane.mk (-1) 0 := by norm_num [J,Plane.supNorm,Plane.mk]
    refine ⟨(hc.isClosedEmbedding hi).isEmbedding,?_,?_,?_,?_⟩
    · change J (f 0) = _; rw [hf0,hJa]
    · change J (f 1) = _; rw [hf1,hJb]
    · intro t ht0 ht1
      have hgt : 1 < Plane.supNorm (f t) := by
        apply lt_of_le_of_ne (hge t)
        intro he
        have hQ : f t ∈ Plane.closedSquare 0 1 := mem_closedSquare_zero_one.mpr he.symm.le
        have hh : f t ∈ Set.range f ∩ Plane.closedSquare 0 1 := ⟨Set.mem_range_self _,hQ⟩
        rw [hmeet] at hh
        rcases Set.mem_insert_iff.mp hh with heA | heB
        · exact ht0.ne' (hf.injective (heA.trans hf0.symm))
        · have heB' : f t = Plane.mk (-1) 0 := heB
          exact ht1.ne (hf.injective (heB'.trans hf1.symm))
      rw [mem_openSquare_zero_one]
      change Plane.supNorm (J (f t)) < 1
      rw [(invert (f t) (hpos t)).1]
      exact (inv_lt_one₀ (hpos t)).mpr hgt
    · rintro ⟨t,he⟩
      have hh := (invert (f t) (hpos t)).1
      change Plane.supNorm (J (f t)) = (Plane.supNorm (f t))⁻¹ at hh
      change J (f t) = 0 at he
      rw [he] at hh
      have hz : Plane.supNorm (0 : Plane) = 0 := by simp [Plane.supNorm]
      rw [hz] at hh
      exact (inv_pos.mpr (hpos t)).ne' hh.symm
  have invert (v : Plane) (hs : 0 < Plane.supNorm v) :
      let J : Plane → Plane := fun x => (Plane.supNorm x)⁻¹^2 • x
      Plane.supNorm (J v) = (Plane.supNorm v)⁻¹ ∧ J (J v) = v := by
    let J : Plane → Plane := fun x => (Plane.supNorm x)⁻¹^2 • x
    have hnorm : Plane.supNorm (J v) = (Plane.supNorm v)⁻¹ := by
      dsimp [J]
      rw [Plane.supNorm_smul,abs_of_nonneg (sq_nonneg _)]
      field_simp
    change Plane.supNorm (J v) = (Plane.supNorm v)⁻¹ ∧ J (J v) = v
    refine ⟨hnorm,?_⟩
    dsimp [J] at hnorm ⊢
    rw [hnorm,inv_inv,smul_smul]
    have he : Plane.supNorm v ^ 2 * (Plane.supNorm v)⁻¹ ^ 2 = 1 := by
      field_simp
    rw [he,one_smul]
  classical
  let J : Plane → Plane := fun v => (Plane.supNorm v)⁻¹^2 • v
  have hJ0 : J 0 = 0 := by simp [J]
  have hpos : ∀ v : Plane, v ≠ 0 → 0 < Plane.supNorm v := by
    intro v hv
    have hn := Plane.supNorm_nonneg v
    by_contra hh
    have he : Plane.supNorm v = 0 := by linarith
    have hx := Plane.abs_zero_le_supNorm v
    have hy := Plane.abs_one_le_supNorm v
    rw [he] at hx hy
    apply hv
    ext i
    fin_cases i
    · exact abs_eq_zero.mp (le_antisymm hx (abs_nonneg _))
    · exact abs_eq_zero.mp (le_antisymm hy (abs_nonneg _))
  have hJJ : ∀ v, J (J v) = v := by
    intro v
    by_cases hv : v = 0
    · simp [hv,hJ0]
    · exact (invert v (hpos v hv)).2
  have hJi : Function.Injective J := by intro v w he; rw [← hJJ v,← hJJ w,he]
  have hJc : ContinuousOn J {v | 0 < Plane.supNorm v} := by
    have hs : Continuous (fun v : Plane => Plane.supNorm v) := by unfold Plane.supNorm; fun_prop
    exact ((hs.continuousOn.inv₀ (fun v hv => ne_of_gt hv)).pow 2).smul continuousOn_id
  have hpa : IsArcBetween (Set.range p) (Plane.mk 1 0) z := by
    have him : p.extend '' I = Set.range p := by
      ext q
      constructor
      · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,(p.extend_apply ht).symm⟩
      · rintro ⟨t,rfl⟩; exact ⟨t,t.property,p.extend_apply t.property⟩
    refine ⟨p.extend,p.continuous_extend.continuousOn,?_,him,by simp,by simp⟩
    intro t ht s hs he
    rw [p.extend_apply ht,p.extend_apply hs] at he
    exact congrArg Subtype.val (hp.injective he)
  obtain ⟨c,hc,hcP,hcQ⟩ := complement (Set.range p) z hpa hmeet
  obtain ⟨f,hf,hf0,hf1,hfp,hfQ⟩ := concatenate_path p hp hmeet c hc hcP hcQ
  obtain ⟨hg,hg0,hg1,hgi,hgZ⟩ := inverted f hf hf0 hf1 hfQ
  obtain ⟨g,hgE,hgleft,hgright,hgp,hginterior⟩ := model
  have h0 : (J ∘ f) 0 = g 0 := hg0.trans hgleft.symm
  have h1 : (J ∘ f) 1 = g 1 := hg1.trans hgright.symm
  obtain ⟨F,hF,hFfix⟩ := parametrized_relative_crosscut_replacement (J ∘ f) g hg hgE h0 h1
    (by rw [hg0]; norm_num [modelCurve,Plane.supNorm,Plane.mk])
    (by rw [hg1]; norm_num [modelCurve,Plane.supNorm,Plane.mk]) hgi hginterior
  have hFsymfix (v : Plane) (hv : v ∉ Plane.openSquare 0 1) : F.symm v = v :=
    (congrArg F.symm (hFfix v hv)).symm.trans (F.symm_apply_apply v)
  let D := I × Icc (-1 : ℝ) 1
  let v : D → Plane := fun z => Plane.mk (1+z.1) z.2
  have hvc : Continuous v := by dsimp [v,D]; fun_prop
  have hvi : Function.Injective v := by
    intro a b he
    apply Prod.ext <;> apply Subtype.ext
    · have hh := congrArg (fun q : Plane => q 0) he
      change 1+(a.1 : ℝ)=1+b.1 at hh; linarith
    · exact congrArg (fun q : Plane => q 1) he
  have hvs (z : D) : 1 ≤ Plane.supNorm (v z) := by
    have hh := Plane.abs_zero_le_supNorm (v z)
    change |1+(z.1 : ℝ)| ≤ Plane.supNorm (v z) at hh
    rw [abs_of_pos (by linarith [z.1.property.1] : 0 < 1+(z.1 : ℝ))] at hh
    linarith [z.1.property.1]
  have hJvc : Continuous (J ∘ v) := by
    apply hJc.comp_continuous hvc
    intro z
    exact lt_of_lt_of_le zero_lt_one (hvs z)
  let B : D → Plane := F.symm ∘ J ∘ v
  have hBc : Continuous B := F.symm.continuous.comp hJvc
  let raw : D → Plane := J ∘ B
  have hpn (t : I) : p t ≠ 0 := by
    intro he
    have hzeroQ : (0 : Plane) ∈ Plane.closedSquare 0 1 := by
      rw [mem_closedSquare_zero_one]; simp [Plane.supNorm]
    have hh : (0 : Plane) ∈ Set.range p ∩ Plane.closedSquare 0 1 := ⟨⟨t,he⟩,hzeroQ⟩
    rw [hmeet] at hh
    have he' := congrArg (fun q : Plane => q 0) (Set.mem_singleton_iff.mp hh)
    norm_num [Plane.mk] at he'
  have hJcenter (t : I) : J (v (t,⟨0,by norm_num⟩)) = Plane.mk (1/(1+t)) 0 := by
    have ht : 0 < 1+(t : ℝ) := by linarith [t.property.1]
    have hs : Plane.supNorm (v (t,⟨0,by norm_num⟩)) = 1+t := by
      simp [v,Plane.supNorm,Plane.mk,abs_of_pos ht,max_eq_left ht.le]
    dsimp [J]
    rw [hs]
    ext i
    fin_cases i
    · change (1+(t : ℝ))⁻¹^2 * (1+t)=1/(1+t)
      field_simp
    · change (1+(t : ℝ))⁻¹^2 * 0=0; simp
  have hBcenter (t : I) : B (t,⟨0,by norm_num⟩) = J (p t) := by
    have hh := hF ⟨(t : ℝ)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
    change F (J (f _)) = _ at hh
    rw [hfp,hgp] at hh
    change F.symm (J (v (t,⟨0,by norm_num⟩))) = J (p t)
    rw [hJcenter,← hh,F.symm_apply_apply]
  have hrawcenter (t : I) : raw (t,⟨0,by norm_num⟩) = p t := by
    change J (B _) = _
    rw [hBcenter,hJJ]
  let V : Set D := {z | B z ≠ 0}
  have hV : IsOpen V := isOpen_ne.preimage hBc
  have hrawc : ContinuousOn raw V := hJc.comp hBc.continuousOn (fun z hz => hpos _ hz)
  let O : Set D := V ∩ raw ⁻¹' U
  have hO : IsOpen O := hrawc.isOpen_inter_preimage hV hU
  have hbase : Set.univ ×ˢ ({⟨0,by norm_num⟩} : Set (Icc (-1 : ℝ) 1)) ⊆ O := by
    rintro ⟨t,w⟩ ⟨_,hw⟩
    have he : w = ⟨0,by norm_num⟩ := hw
    subst w
    refine ⟨?_,?_⟩
    · change B _ ≠ 0
      rw [hBcenter]
      intro hh
      exact hpn t (hJi (hh.trans hJ0.symm))
    · change raw _ ∈ U
      rw [hrawcenter]
      exact hpU (Set.mem_range_self _)
  obtain ⟨A,W,hA,hW,hUA,h0W,hAW⟩ := generalized_tube_lemma isCompact_univ isCompact_singleton hO hbase
  let clip : ℝ → Icc (-1 : ℝ) 1 := projIcc (-1) 1 (by norm_num)
  have h0pre : (0 : ℝ) ∈ clip ⁻¹' W := by
    simpa [clip,projIcc_of_mem] using h0W (Set.mem_singleton (⟨0,by norm_num⟩ : Icc (-1 : ℝ) 1))
  obtain ⟨d,hd,hdW⟩ := Metric.mem_nhds_iff.mp ((hW.preimage continuous_projIcc).mem_nhds h0pre)
  let rho := min (d/2) (1/2 : ℝ)
  have hrho : 0 < rho ∧ rho ≤ 1 := by
    constructor
    · dsimp [rho]; positivity
    · have hh := min_le_right (d/2) (1/2 : ℝ); dsimp [rho]; linarith
  have hrd : rho < d := by have hh := min_le_left (d/2) (1/2 : ℝ); dsimp [rho]; linarith
  let k : D → D := fun z => (z.1,⟨rho*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hrho.1,hrho.2]⟩)
  have hkc : Continuous k := by dsimp [k,D]; fun_prop
  have hki : Function.Injective k := by
    intro z w he
    apply Prod.ext
    · simpa [k] using congrArg Prod.fst he
    · apply Subtype.ext
      exact mul_left_cancel₀ hrho.1.ne' (congrArg (fun z : D => (z.2 : ℝ)) he)
  have hkO (z : D) : k z ∈ O := by
    apply hAW ⟨hUA trivial,?_⟩
    have hw : rho*(z.2 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hrho.1,hrho.2]
    have habs : |rho*(z.2 : ℝ)| < d := by
      rw [abs_mul,abs_of_pos hrho.1]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr z.2.property) hrho.1.le).trans_lt (by simpa using hrd)
    have hh := hdW (show rho*(z.2 : ℝ) ∈ Metric.ball (0 : ℝ) d by simpa [Metric.mem_ball,Real.dist_eq] using habs)
    simpa [clip,projIcc_of_mem _ hw] using hh
  let E : D → Plane := raw ∘ k
  have hEc : Continuous E := hrawc.comp_continuous hkc (fun z => (hkO z).1)
  have hEi : Function.Injective E := by
    intro z w he
    apply hki
    apply hvi
    apply hJi
    apply F.symm.injective
    apply hJi
    exact he
  have hE : IsEmbedding E := (hEc.isClosedEmbedding hEi).isEmbedding
  have hEport (w : Icc (-1 : ℝ) 1) : E (0,w) = Plane.mk 1 (rho*w) := by
    have hcoord : v (k (0,w)) = Plane.mk 1 (rho*w) := by
      ext i; fin_cases i <;> simp [v,k]
    have hn : Plane.supNorm (Plane.mk 1 (rho*w)) = 1 := by
      change max |(1 : ℝ)| |rho*(w : ℝ)| = 1
      rw [abs_one]
      apply max_eq_left
      rw [abs_mul,abs_of_pos hrho.1]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr w.property) hrho.1.le).trans (by simpa using hrho.2)
    have hJp : J (Plane.mk 1 (rho*w)) = Plane.mk 1 (rho*w) := by simp [J,hn]
    have hnot : Plane.mk 1 (rho*w) ∉ Plane.openSquare 0 1 := by
      intro hh
      have hh' := mem_openSquare_zero_one.mp hh
      rw [hn] at hh'; exact lt_irrefl _ hh'
    change J (F.symm (J (v (k (0,w))))) = _
    rw [hcoord,hJp,hFsymfix _ hnot,hJp]
  have hEcenter (t : I) : E (t,⟨0,by norm_num⟩) = p t := by
    have he : k (t,⟨0,by norm_num⟩) = (t,⟨0,by norm_num⟩) := by dsimp [k]; congr 1; apply Subtype.ext; simp
    change raw (k _) = _
    rw [he,hrawcenter]
  have hEU : Set.range E ⊆ U := by rintro q ⟨z,rfl⟩; exact (hkO z).2
  have honly (z : D) (hz : E z ∈ Plane.closedSquare 0 1) : z.1 = 0 := by
    have hBn : B (k z) ≠ 0 := (hkO z).1
    have hrawpos : 0 < Plane.supNorm (E z) := by
      change 0 < Plane.supNorm (J (B (k z)))
      rw [(invert _ (hpos _ hBn)).1]
      exact inv_pos.mpr (hpos _ hBn)
    have hEbound := mem_closedSquare_zero_one.mp hz
    have hJEn : J (E z) ∉ Plane.openSquare 0 1 := by
      intro hh
      have hh' := mem_openSquare_zero_one.mp hh
      rw [(invert _ hrawpos).1] at hh'
      exact not_lt_of_ge ((one_le_inv₀ hrawpos).mpr hEbound) hh'
    have hJE : J (E z) = B (k z) := hJJ _
    have hBJ : B (k z) = J (v (k z)) := by
      have hnot : B (k z) ∉ Plane.openSquare 0 1 := hJE ▸ hJEn
      have hh := hFfix (B (k z)) hnot
      change F (F.symm (J (v (k z)))) = B (k z) at hh
      rw [F.apply_symm_apply] at hh
      exact hh.symm
    have hEq : E z = v (k z) := by change J (B (k z)) = _; rw [hBJ,hJJ]
    rw [hEq] at hz
    have hx := abs_le.mp ((Plane.abs_zero_le_supNorm (v (k z))).trans (mem_closedSquare_zero_one.mp hz))
    apply Subtype.ext
    change (z.1 : ℝ) = 0
    have hx' : 1+(z.1 : ℝ) ≤ 1 := by simpa [v,k] using hx.2
    linarith [z.1.property.1]
  refine ⟨rho,hrho.1,hrho.2,E,hE,hEport,hEcenter,hEU,?_⟩
  ext q
  constructor
  · rintro ⟨⟨z,rfl⟩,hz⟩
    have ht := honly z hz
    refine ⟨z.2,trivial,?_⟩
    have he : z = (0,z.2) := Prod.ext ht rfl
    rw [he,hEport]
  · rintro ⟨w,_,rfl⟩
    refine ⟨⟨(0,w),hEport w⟩,?_⟩
    rw [mem_closedSquare_zero_one]
    change max |(1 : ℝ)| |rho*(w : ℝ)| ≤ 1
    rw [abs_one,abs_mul,abs_of_pos hrho.1]
    exact max_le le_rfl ((mul_le_mul_of_nonneg_left (abs_le.mpr w.property) hrho.1.le).trans (by simpa using hrho.2))

end CurveComplex
