import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
open Set Topology Schoenflies
open scoped Manifold
universe u
namespace CurveComplex.PositionUniverseV2
/-- A prescribed compact parameter subarc has an adapted square chart, inside
any chosen neighborhood and the supplied old-family chart. The square isolates
EXACTLY that subarc from the whole original embedded circle. -/
theorem position_subarc_crosscut_chart
    (S : Type u) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (c : Curve S) (a b : ℝ) (hab : a < b) (hlen : b - a < 2 * Real.pi)
    (e : OpenPartialHomeomorph S Schoenflies.Plane)
    (W : Set S) (hW : IsOpen W)
    (hsub : (fun t => c.map (Circle.exp t)) '' Set.Icc a b ⊆ W ∩ e.source) :
    ∃ E : OpenPartialHomeomorph S Schoenflies.Plane,
      E.source ⊆ W ∩ e.source ∧
      Schoenflies.Plane.closedSquare 0 1 ⊆ E.target ∧
      (fun t => c.map (Circle.exp t)) '' Set.Icc a b ⊆ E.source ∧
      E (c.map (Circle.exp a)) = Schoenflies.Plane.mk (-1) 0 ∧
      E (c.map (Circle.exp b)) = Schoenflies.Plane.mk 1 0 ∧
      (∀ x ∈ E.source, x ∈ c.image ↔ E x 1 = 0) ∧
      {x : S | x ∈ E.source ∧ E x ∈ Schoenflies.Plane.closedSquare 0 1} ∩ c.image =
        (fun t => c.map (Circle.exp t)) '' Set.Icc a b := by
  classical
  haveI : T2Space S := inferInstance
  have hThreeArc :
      IsArcBetween (sideLeft ∪ (sideBottom ∪ sideRight)) cornerNW cornerNE := by
    apply isArcBetween_sideLeft.concatenate isArcBetween_lowerSides
    rintro z hz (hb | hr)
    · have hx := (mem_sideLeft.mp hz).1
      have hy := (mem_sideBottom.mp hb).1
      ext i
      fin_cases i
      · simpa [cornerSW] using hx
      · simpa [cornerSW] using hy
    · have hx := (mem_sideLeft.mp hz).1
      have hx' := (mem_sideRight.mp hr).1
      linarith
  
  have hThreeMeet :
      (sideLeft ∪ (sideBottom ∪ sideRight)) ∩ sideTop = {cornerNE,cornerNW} := by
    ext z
    constructor
    · rintro ⟨hl | hb | hr,ht⟩
      · right
        exact sideTop_meet_sideLeft z ht hl
      · have h1 := (mem_sideBottom.mp hb).1
        have h2 := (mem_sideTop.mp ht).1
        linarith
      · left
        have hx := (mem_sideRight.mp hr).1
        have hy := (mem_sideTop.mp ht).1
        ext i
        fin_cases i
        · simpa [cornerNE] using hx
        · simpa [cornerNE] using hy
    · rintro (rfl | rfl)
      · exact ⟨hThreeArc.right_mem,isArcBetween_sideTop.left_mem⟩
      · exact ⟨hThreeArc.left_mem,isArcBetween_sideTop.right_mem⟩
  have hplanarMatched {P : Set Schoenflies.Plane} {a b : Schoenflies.Plane}
      (hP : Schoenflies.IsArcBetween P a b) :
      ∃ F : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
        F '' P = Schoenflies.sideTop ∧ F a = Schoenflies.cornerNE ∧ F b = Schoenflies.cornerNW := by
    obtain ⟨A, hA, hmeet, hJ⟩ := Schoenflies.exists_jordan_completion_of_isArcBetween hP
    let B := Schoenflies.sideLeft ∪ (Schoenflies.sideBottom ∪ Schoenflies.sideRight)
    obtain ⟨e, heimage, hea, heb⟩ :=
      Schoenflies.exists_homeomorph_union_arcs_preserving_second hA hP
        hThreeArc.reverse Schoenflies.isArcBetween_sideTop
        hmeet hThreeMeet
    have hmodel : B ∪ Schoenflies.sideTop = Schoenflies.modelCurve := by
      rw [Schoenflies.modelCurve_eq_sides]
      dsimp [B]
      ext z
      simp only [Set.mem_union]
      tauto
    let eModel := e.trans (Homeomorph.setCongr hmodel)
    obtain ⟨F, hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph hJ
      Schoenflies.isJordanCurve_modelCurve eModel
    have hval (z : ↥(A ∪ P)) : F z.val = (e z).val := hF z
    refine ⟨F, ?_, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩
        rw [hval ⟨x, Or.inr hx⟩]
        have hm : (e ⟨x, Or.inr hx⟩).val ∈ Subtype.val ''
            (e '' {z : ↥(A ∪ P) | z.val ∈ P}) :=
          ⟨e ⟨x, Or.inr hx⟩, ⟨⟨x, Or.inr hx⟩, hx, rfl⟩, rfl⟩
        exact heimage.le hm
      · intro y hy
        rw [← heimage] at hy
        obtain ⟨z, ⟨x, hx, rfl⟩, hxy⟩ := hy
        exact ⟨x.val, hx, (hval x).trans hxy⟩
    · exact (hval ⟨a, Or.inl hA.left_mem⟩).trans (congrArg Subtype.val hea)
    · exact (hval ⟨b, Or.inl hA.right_mem⟩).trans (congrArg Subtype.val heb)
  let g : ℝ → S := fun t => c.map (Circle.exp t)
  have hg : Continuous g := c.embedded.continuous.comp Circle.exp.continuous
  let O := g ⁻¹' (W ∩ e.source)
  have hO : IsOpen O := (hW.inter e.open_source).preimage hg
  obtain ⟨δ, hδ, hδO⟩ := isCompact_Icc.exists_cthickening_subset_open hO (fun t ht => hsub ⟨t,ht,rfl⟩)
  let ε := min δ (2 * Real.pi - (b-a)) / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε ≤ δ := by dsimp [ε]; linarith [min_le_left δ (2 * Real.pi - (b-a))]
  let A := a-ε
  let B := b+ε
  have hAB : A < B := by dsimp [A,B]; linarith
  have hABlen : B-A < 2*Real.pi := by
    dsimp [A,B,ε]
    linarith [min_le_right δ (2 * Real.pi - (b-a))]
  have hgs (t : ℝ) (ht : t ∈ Set.Icc A B) : g t ∈ W ∩ e.source := by
    apply hδO
    by_cases hta : t < a
    · apply Metric.mem_cthickening_of_dist_le t a δ (Set.Icc a b) ⟨le_rfl,hab.le⟩
      rw [Real.dist_eq,abs_of_nonpos (by linarith)]
      dsimp [A] at ht
      linarith [ht.1]
    · by_cases htb : b < t
      · apply Metric.mem_cthickening_of_dist_le t b δ (Set.Icc a b) ⟨hab.le,le_rfl⟩
        rw [Real.dist_eq,abs_of_nonneg (by linarith)]
        dsimp [B] at ht
        linarith [ht.2]
      · exact Metric.self_subset_cthickening (Set.Icc a b) ⟨not_lt.mp hta,not_lt.mp htb⟩
  have hgi : Set.InjOn g (Set.Icc A B) := by
    intro t ht u hu he
    exact Circle.exp_injOn_Icc hABlen ht hu (c.embedded.injective he)
  let f : ℝ → Schoenflies.Plane := fun t => e (g (A+(B-A)*t))
  have hparam (t : ℝ) (ht : t ∈ unitInterval) : A+(B-A)*t ∈ Set.Icc A B := by
    constructor <;> nlinarith [ht.1,ht.2]
  have hf : ContinuousOn f unitInterval :=
    e.continuousOn.comp (hg.comp (by fun_prop)).continuousOn (fun t ht => (hgs _ (hparam t ht)).2)
  have hfi : Set.InjOn f unitInterval := by
    intro t ht u hu he
    have hh := hgi (hparam t ht) (hparam u hu)
      (e.injOn (hgs _ (hparam t ht)).2 (hgs _ (hparam u hu)).2 he)
    nlinarith
  have hf0 : f 0 = e (g A) := by simp [f]
  have hf1 : f 1 = e (g B) := by simp [f]
  have himage : f '' unitInterval = (fun t => e (g t)) '' Set.Icc A B := by
    apply Set.Subset.antisymm
    · rintro z ⟨t,ht,rfl⟩; exact ⟨_,hparam t ht,rfl⟩
    · rintro z ⟨t,ht,rfl⟩
      let u := (t-A)/(B-A)
      have hu : u ∈ unitInterval := by
        constructor
        · exact div_nonneg (sub_nonneg.mpr ht.1) (by linarith)
        · exact (div_le_one (by linarith : 0 < B-A)).mpr (by linarith [ht.2])
      refine ⟨u,hu,?_⟩
      have hpu : A+(B-A)*u = t := by dsimp [u]; field_simp [ne_of_gt (sub_pos.mpr hAB)] <;> ring
      simp only [f,hpu]
  have hArc : Schoenflies.IsArcBetween (f '' unitInterval) (e (g A)) (e (g B)) :=
    ⟨f,hf,hfi,rfl,hf0,hf1⟩
  obtain ⟨F,hFP,hFA,hFB⟩ := hplanarMatched hArc
  have hFT : F '' ((fun t => e (g t)) '' Set.Icc A B) = Schoenflies.sideTop := by
    rwa [himage] at hFP
  have hcoord (t : ℝ) (ht : t ∈ Set.Icc A B) : F (e (g t)) 1 = 1 :=
    (Schoenflies.mem_sideTop.mp (hFT ▸ ⟨_,⟨t,ht,rfl⟩,rfl⟩)).1
  let q : ℝ → ℝ := fun t => F (e (g t)) 0
  have hqc : ContinuousOn q (Set.Icc A B) :=
    (EuclideanSpace.proj 0).continuous.continuousOn.comp
      (F.continuous.continuousOn.comp (e.continuousOn.comp hg.continuousOn
        (fun t ht => (hgs t ht).2)) (Set.mapsTo_univ _ _)) (Set.mapsTo_univ _ _)
  have hqi : Set.InjOn q (Set.Icc A B) := by
    intro t ht u hu he
    apply hgi ht hu
    apply e.injOn (hgs t ht).2 (hgs u hu).2
    apply F.injective
    ext i
    fin_cases i
    · exact he
    · exact (hcoord t ht).trans (hcoord u hu).symm
  have hqA : q A = 1 := by change F (e (g A)) 0 = 1; rw [hFA]; rfl
  have hqB : q B = -1 := by change F (e (g B)) 0 = -1; rw [hFB]; rfl
  have hanti : StrictAntiOn q (Set.Icc A B) :=
    ContinuousOn.strictAntiOn_of_injOn_Icc hAB.le (by rw [hqA,hqB]; norm_num) hqc hqi
  have haAB : a ∈ Set.Icc A B := by dsimp [A,B]; constructor <;> linarith
  have hbAB : b ∈ Set.Icc A B := by dsimp [A,B]; constructor <;> linarith
  have hqab : q b < q a := hanti haAB hbAB hab
  have hqa : q a < 1 := by rw [← hqA]; exact hanti ⟨le_rfl,hAB.le⟩ haAB (by dsimp [A]; linarith)
  have hqb : -1 < q b := by rw [← hqB]; exact hanti hbAB ⟨hAB.le,le_rfl⟩ (by dsimp [B]; linarith)
  let J : Set Circle := Circle.exp '' Set.Ioo A B
  have hJ : IsOpen J := isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo
  let bad := c.map '' Jᶜ
  have hbad : IsClosed bad := ((isCompact_univ : IsCompact (Set.univ : Set Circle)).of_isClosed_subset
    hJ.isClosed_compl (Set.subset_univ _)).image c.embedded.continuous |>.isClosed
  let N := (W ∩ e.source) ∩ badᶜ
  have hN : IsOpen N := (hW.inter e.open_source).inter hbad.isOpen_compl
  have hcoreN : g '' Set.Icc a b ⊆ N := by
    rintro x ⟨t,ht,rfl⟩
    refine ⟨hsub ⟨t,ht,rfl⟩,?_⟩
    rintro ⟨z,hz,he⟩
    have hzexp : z = Circle.exp t := c.embedded.injective he
    apply hz
    refine ⟨t,?_,hzexp.symm⟩
    dsimp [A,B]
    constructor <;> linarith [ht.1,ht.2]
  have hNcurve (x : S) (hx : x ∈ N) : x ∈ c.image ↔ x ∈ g '' Set.Icc A B := by
    constructor
    · rintro ⟨z,hz⟩
      have hzJ : z ∈ J := by by_contra hn; exact hx.2 ⟨z,hn,hz⟩
      obtain ⟨t,ht,rfl⟩ := hzJ
      exact ⟨t,⟨ht.1.le,ht.2.le⟩,hz⟩
    · rintro ⟨t,ht,rfl⟩; exact ⟨Circle.exp t,rfl⟩
  let V : Set Plane := {z | |z 0| < 1}
  have hV : IsOpen V := isOpen_lt ((EuclideanSpace.proj 0).continuous.abs) continuous_const
  let R := N ∩ (e.source ∩ e ⁻¹' (F ⁻¹' V))
  have hR : IsOpen R := hN.inter (e.isOpen_inter_preimage (hV.preimage F.continuous))
  let E₀ := (e.trans F.toOpenPartialHomeomorph).restr R
  have hE₀s : E₀.source = e.source ∩ R := by
    simp only [E₀, OpenPartialHomeomorph.restr_source, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ, hR.interior_eq]
  have hE₀val (x : S) : E₀ x = F (e x) := rfl
  have hcoreE₀ (t : ℝ) (ht : t ∈ Icc a b) : g t ∈ E₀.source := by
    have htAB : t ∈ Icc A B := Icc_subset_Icc haAB.1 hbAB.2 ht
    have hqt : q t ∈ Icc (q b) (q a) :=
      ⟨hanti.antitoneOn htAB hbAB ht.2,hanti.antitoneOn haAB htAB ht.1⟩
    rw [hE₀s]
    exact ⟨(hgs t htAB).2,hcoreN ⟨t,ht,rfl⟩,(hgs t htAB).2,
      abs_lt.mpr ⟨hqb.trans_le hqt.1,hqt.2.trans_lt hqa⟩⟩
  have hflat (x : S) (hx : x ∈ E₀.source) : x ∈ c.image ↔ E₀ x 1 = 1 := by
    rw [hE₀s] at hx
    rw [hNcurve x hx.2.1,hE₀val]
    constructor
    · rintro ⟨t,ht,rfl⟩; exact hcoord t ht
    · intro hy
      have htop : F (e x) ∈ sideTop := mem_sideTop.mpr ⟨hy,hx.2.2.2.le⟩
      rw [← hFT] at htop
      obtain ⟨z,⟨t,ht,rfl⟩,he⟩ := htop
      exact ⟨t,ht,e.injOn (hgs t ht).2 hx.1 (F.injective he)⟩
  let K := (fun t => E₀ (g t)) '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    (E₀.continuousOn.comp hg.continuousOn hcoreE₀)
  have hKt : K ⊆ E₀.target := by
    rintro z ⟨t,ht,rfl⟩; exact E₀.map_source (hcoreE₀ t ht)
  obtain ⟨d,hd,hdK⟩ := hK.exists_cthickening_subset_open E₀.open_target hKt
  let r := (q a-q b)/2
  let m := (q a+q b)/2
  have hr : 0 < r := by dsimp [r]; linarith
  let H : Plane ≃ₜ Plane := {
    toFun := fun z => Plane.mk ((m-z 0)/r) ((z 1-1)/d)
    invFun := fun z => Plane.mk (m-r*z 0) (1+d*z 1)
    left_inv := by
      intro z
      ext i
      fin_cases i <;> simp [Plane.mk]
      · field_simp [hr.ne'] <;> ring
      · field_simp [hd.ne'] <;> ring
    right_inv := by
      intro z
      ext i
      fin_cases i <;> simp [Plane.mk]
      · field_simp [hr.ne'] <;> ring
      · field_simp [hd.ne'] <;> ring
    continuous_toFun := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> dsimp [Plane.mk] <;> fun_prop
    continuous_invFun := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> dsimp [Plane.mk] <;> fun_prop }
  have hH0 (z : Plane) : H z 0 = (m-z 0)/r := rfl
  have hH1 (z : Plane) : H z 1 = (z 1-1)/d := rfl
  have hHi (z : Plane) : H.symm z = Plane.mk (m-r*z 0) (1+d*z 1) := rfl
  let E := E₀.trans H.toOpenPartialHomeomorph
  have hEs : E.source = E₀.source := by simp [E,OpenPartialHomeomorph.trans_source]
  have hEval (x : S) : E x = H (E₀ x) := rfl
  have hEa : E (g a) = Plane.mk (-1) 0 := by
    rw [hEval]
    ext i
    fin_cases i
    · change H (E₀ (g a)) 0 = -1
      rw [hH0]; change (m-q a)/r = -1
      dsimp [m,r]; field_simp [ne_of_gt (sub_pos.mpr hqab)] <;> ring
    · change H (E₀ (g a)) 1 = 0
      rw [hH1,hE₀val,hcoord a haAB]
      simp
  have hEb : E (g b) = Plane.mk 1 0 := by
    rw [hEval]
    ext i
    fin_cases i
    · change H (E₀ (g b)) 0 = 1
      rw [hH0]; change (m-q b)/r = 1
      dsimp [m,r]; field_simp [ne_of_gt (sub_pos.mpr hqab)] <;> ring
    · change H (E₀ (g b)) 1 = 0
      rw [hH1,hE₀val,hcoord b hbAB]
      simp
  have hqimage : q '' Icc a b = Icc (q b) (q a) :=
    ContinuousOn.image_Icc_of_antitoneOn hab.le (hqc.mono (Icc_subset_Icc haAB.1 hbAB.2))
      (hanti.antitoneOn.mono (Icc_subset_Icc haAB.1 hbAB.2))
  have hEt : E.target = H '' E₀.target := by simp [E, Homeomorph.image_eq_preimage_symm]
  have hsquare : Plane.closedSquare 0 1 ⊆ E.target := by
    intro z hz
    have hzsup : Plane.supNorm z ≤ 1 := mem_closedSquare_zero_one.mp hz
    have hz0 := abs_le.mp ((Plane.abs_zero_le_supNorm z).trans hzsup)
    have hz1 := abs_le.mp ((Plane.abs_one_le_supNorm z).trans hzsup)
    have hx : m-r*z 0 ∈ Icc (q b) (q a) := by
      dsimp [m,r]; constructor <;> nlinarith [hz0.1,hz0.2]
    rw [← hqimage] at hx
    obtain ⟨t,ht,hqt⟩ := hx
    have htK : E₀ (g t) ∈ K := ⟨t,ht,rfl⟩
    have hnear : dist (H.symm z) (E₀ (g t)) ≤ d := by
      have hplane : H.symm z-E₀ (g t) = (d*z 1) • Plane.mk 0 1 := by
        ext i
        fin_cases i
        · simp only [hHi,Plane.mk,PiLp.sub_apply,PiLp.smul_apply]
          change m-r*z 0-q t = (d*z 1)*0
          rw [hqt]; ring
        · simp only [hHi,Plane.mk,PiLp.sub_apply,PiLp.smul_apply]
          change 1+d*z 1-E₀ (g t) 1 = (d*z 1)*1
          rw [hE₀val,hcoord t (Icc_subset_Icc haAB.1 hbAB.2 ht)]
          ring
      rw [dist_eq_norm,hplane]
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos hd]
      have hn : ‖Plane.mk 0 1‖ = 1 := by
        simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk]
      rw [hn,mul_one]
      nlinarith [(abs_le.mpr hz1 : |z 1| ≤ 1)]
    have htgt : H.symm z ∈ E₀.target := hdK
      (Metric.mem_cthickening_of_dist_le _ _ d K htK hnear)
    rw [hEt]
    exact ⟨H.symm z,htgt,H.apply_symm_apply z⟩
  refine ⟨E,?_,hsquare,?_,hEa,hEb,?_,?_⟩
  · intro x hx
    rw [hEs,hE₀s] at hx
    exact hx.2.1.1
  · rintro x ⟨t,ht,rfl⟩; rw [hEs]; exact hcoreE₀ t ht
  · intro x hx
    rw [hEs] at hx
    rw [hEval,hH1,hflat x hx]
    exact ⟨fun h => by rw [h]; simp,fun h => by
      have hh := (div_eq_zero_iff).mp h
      exact sub_eq_zero.mp (hh.resolve_right hd.ne')⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨hx,hxs⟩,hxc⟩
      have hx₀ : x ∈ E₀.source := hEs ▸ hx
      have hxR := hE₀s ▸ hx₀
      obtain ⟨t,ht,hxt⟩ := (hNcurve x hxR.2.1).mp hxc
      have hxsup := mem_closedSquare_zero_one.mp hxs
      have hxx := abs_le.mp ((Plane.abs_zero_le_supNorm (E x)).trans hxsup)
      rw [hEval,hH0] at hxx
      have hqtx : E₀ x 0 = q t := by rw [← hxt]; rfl
      rw [hqtx] at hxx
      have hqt : q t ∈ Icc (q b) (q a) := by
        have hl := (le_div_iff₀ hr).mp hxx.1
        have hu := (div_le_iff₀ hr).mp hxx.2
        dsimp [m,r] at hl hu
        constructor <;> linarith
      have hta : a ≤ t := by
        by_contra hn
        have := hanti ht haAB (not_le.mp hn)
        linarith [hqt.2]
      have htb : t ≤ b := by
        by_contra hn
        have := hanti hbAB ht (not_le.mp hn)
        linarith [hqt.1]
      exact ⟨t,⟨hta,htb⟩,hxt⟩
    · rintro x ⟨t,ht,rfl⟩
      have htAB := Icc_subset_Icc haAB.1 hbAB.2 ht
      have hqt : q t ∈ Icc (q b) (q a) :=
        ⟨hanti.antitoneOn htAB hbAB ht.2,hanti.antitoneOn haAB htAB ht.1⟩
      refine ⟨⟨hEs.symm ▸ hcoreE₀ t ht,?_⟩,Circle.exp t,rfl⟩
      rw [mem_closedSquare_zero_one]
      change max |E (g t) 0| |E (g t) 1| ≤ 1
      apply max_le
      · rw [hEval,hH0]
        change |(m-q t)/r| ≤ 1
        apply abs_le.mpr
        constructor
        · apply (le_div_iff₀ hr).mpr
          dsimp [m,r]; linarith [hqt.2]
        · apply (div_le_iff₀ hr).mpr
          dsimp [m,r]; linarith [hqt.1]
      · rw [hEval,hH1,hE₀val,hcoord t htAB]
        norm_num


end CurveComplex.PositionUniverseV2
