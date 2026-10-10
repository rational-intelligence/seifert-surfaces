import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTransportedWhiskerCollar
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualStripNarrowing

open Set Topology Schoenflies CurveComplex unitInterval

/-- The actual proper normalized family, not a family-isolation certificate,
allows an exterior endpoint half-collar to be truncated and narrowed. Outside
the old closed disk its only family contacts are its exact center whisker. -/
theorem actual_left_whisker_family_collar_of_closed_rows
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T a r s : ℝ)
    (har : a<r) (hrs : r<s)
    (hclosed : ∀ j : ℤ, IsClosed (range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))))
    (hpair : Pairwise (fun i j : ℤ => Disjoint
      (range (fun x : ℝ => G x+Plane.mk 0 ((i:ℝ)*T)))
      (range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))))
    (hlf : LocallyFinite (fun j : ℤ => range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))))
    (K : Set Plane) (hcore : G '' Icc r s⊆K)
    (F : Plane ≃ₜ Plane) (hFK : F '' K=Plane.closedSquare 0 1) (hrF : F (G r)=Plane.mk 1 0)
    (p : Path (G r) (G a)) (hpE : IsEmbedding p)
    (hpt : ∀ t : I, p t=G (reparam r a t))
    (hpR : range p=G '' Icc a r) (hpK : range p∩K={G r})
    (W : Set Plane) (hW : IsOpen W) (hpW : range p⊆W) :
    ∃ rho : ℝ, 0<rho ∧ rho≤1 ∧ ∃ E : I×Icc (-1:ℝ) 1 → Plane,
      IsEmbedding E ∧ range E⊆W ∧
      (∀ w : Icc (-1:ℝ) 1, E (0,w)=F.symm (Plane.mk 1 (rho*w))) ∧
      (∀ t : I, E (t,⟨0,by norm_num⟩)=G (reparam r ((a+r)/2) t)) ∧
      range E∩K=(fun w : Icc (-1:ℝ) 1 => F.symm (Plane.mk 1 (rho*w))) '' univ ∧
      (range E\K)∩(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=
        (G '' Icc ((a+r)/2) r)\K := by
  obtain ⟨rho,hrho,hrho1,B,hB,hport,hcenter,hBW,hBK⟩ :=
    actual_charted_exterior_whisker_half_collar K F hFK (G r) (G a) hrF p hpE hpK W hW hpW
  let L : ℤ → Set Plane := fun j => range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
  change Pairwise (fun i j => Disjoint (L i) (L j)) at hpair
  have hL0 : L 0=range G := by
    have hh : (fun x : ℝ => G x+Plane.mk 0 (((0:ℤ):ℝ)*T))=G := by
      funext x
      ext i
      fin_cases i <;> simp [Plane.mk]
    change range (fun x : ℝ => G x+Plane.mk 0 (((0:ℤ):ℝ)*T))=range G
    rw [hh]
  let J := ⋃ j : {j : ℤ // j≠0}, L j.val
  have hJ : IsClosed J := (hlf.comp_injective Subtype.val_injective).isClosed_iUnion (fun j => hclosed j.val)
  have hGJ : Disjoint (range G) J := by
    apply disjoint_left.mpr
    intro z hz hzz
    obtain ⟨j,hj⟩ := mem_iUnion.mp hzz
    exact disjoint_left.mp (hpair (Ne.symm j.property)) (hL0.symm ▸ hz) hj
  let bad := G '' (Ioo a ((r+s)/2))ᶜ ∪ J
  have hbad : IsClosed bad := (hG.isClosedMap _ isOpen_Ioo.isClosed_compl).union hJ
  let k : I×Icc (-1:ℝ) 1 → I×Icc (-1:ℝ) 1 := fun z =>
    (⟨(z.1:ℝ)/2,by constructor <;> linarith [z.1.property.1,z.1.property.2]⟩,z.2)
  have hk : IsEmbedding k := by
    have hkc : Continuous k := by dsimp [k]; fun_prop
    apply (hkc.isClosedEmbedding ?_).isEmbedding
    intro z w he
    apply Prod.ext
    · apply Subtype.ext
      have hh := congrArg (fun z : I×Icc (-1:ℝ) 1 => (z.1:ℝ)) he
      change (z.1:ℝ)/2=(w.1:ℝ)/2 at hh
      linarith
    · simpa [k] using congrArg Prod.snd he
  have hBcenter (t : I) : (B∘k) (t,⟨0,by norm_num⟩)=G (reparam r ((a+r)/2) t) := by
    rw [Function.comp_apply,hcenter,hpt]
    congr 1
    simp only [reparam]
    ring
  have hcenterU (t : I) : (B∘k) (t,⟨0,by norm_num⟩)∈badᶜ := by
    rw [hBcenter]
    let u := reparam r ((a+r)/2) t
    have hu : u∈Ioo a ((r+s)/2) := by
      dsimp [u,reparam]
      constructor <;> nlinarith [t.property.1,t.property.2]
    rintro (⟨v,hv,he⟩|hzJ)
    · exact hv (hG.injective he ▸ hu)
    · exact disjoint_left.mp hGJ (mem_range_self _) hzJ
  obtain ⟨eta,heta,N,hN,hNU,hNval,hNcenter⟩ := source_shrink_embedded_strip_in_open
    (B∘k) (hB.comp hk) badᶜ hbad.isOpen_compl hcenterU
  have hNsub : range N⊆range B := by
    rintro z ⟨w,rfl⟩
    rw [hNval]
    exact mem_range_self _
  have hNcenter' (t : I) : N (t,⟨0,by norm_num⟩)=G (reparam r ((a+r)/2) t) :=
    (hNcenter t).trans (hBcenter t)
  have hk0 (w : Icc (-1:ℝ) 1) : k (0,w)=(0,w) := by
    apply Prod.ext
    · apply Subtype.ext; norm_num [k]
    · rfl
  have hNport (w : Icc (-1:ℝ) 1) : N (0,w)=F.symm (Plane.mk 1 ((rho*eta)*w)) := by
    rw [hNval]
    rw [Function.comp_apply,hk0,hport]
    congr 2
    ring
  have hNK : range N∩K=(fun w : Icc (-1:ℝ) 1 => F.symm (Plane.mk 1 ((rho*eta)*w))) '' univ := by
    ext z
    constructor
    · rintro ⟨⟨w,rfl⟩,hzK⟩
      have hh : N w∈range B∩K := ⟨hNsub (mem_range_self _),hzK⟩
      rw [hBK] at hh
      obtain ⟨v,_,he⟩ := hh
      have hev : B (0,v)=N w := (hport v).trans he
      rw [hNval] at hev
      have ht := congrArg (fun z : I×Icc (-1:ℝ) 1 => (z.1:ℝ)) (hB.injective hev)
      have hw0 : w.1=0 := by apply Subtype.ext; change (w.1:ℝ)=0; change 0=(w.1:ℝ)/2 at ht; linarith
      exact ⟨w.2,trivial,by rw [show w=(0,w.2) from Prod.ext hw0 rfl,hNport]⟩
    · rintro ⟨w,_,rfl⟩
      refine ⟨⟨(0,w),hNport w⟩,?_⟩
      let v : Icc (-1:ℝ) 1 := ⟨eta*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,heta.1,heta.2]⟩
      have hh : N (0,w)∈range B∩K := by
        rw [hNval,Function.comp_apply,hk0]
        change B (0,v)∈range B∩K
        rw [hBK]
        exact ⟨v,trivial,(hport v).symm⟩
      change F.symm (Plane.mk 1 ((rho*eta)*w))∈K
      rw [←hNport]
      exact hh.2
  refine ⟨rho*eta,mul_pos hrho heta.1,by nlinarith [heta.2],N,hN,hNsub.trans hBW, hNport,hNcenter',hNK,?_⟩
  ext z
  constructor
  · rintro ⟨⟨⟨w,rfl⟩,hzK⟩,hzL⟩
    have hnBad := hNU (mem_range_self w)
    obtain ⟨j,hj⟩ := mem_iUnion.mp hzL
    have hj0 : j=0 := by
      by_contra hn
      exact hnBad (Or.inr (mem_iUnion.mpr ⟨⟨j,hn⟩,hj⟩))
    subst j
    change N w∈L 0 at hj
    rw [hL0] at hj
    obtain ⟨u,hu⟩ := hj
    have huI : u∈Ioo a ((r+s)/2) := by
      by_contra hn
      exact hnBad (Or.inl ⟨u,hn,hu⟩)
    have hur : u<r := by
      by_contra hn
      exact hzK (hu ▸ hcore ⟨u,⟨le_of_not_gt hn,by linarith [huI.2]⟩,rfl⟩)
    have huP : G u∈range p := hpR.symm ▸ (show G u∈G '' Icc a r from ⟨u,⟨huI.1.le,hur.le⟩,rfl⟩)
    obtain ⟨v,hv⟩ := huP
    have hev : B (v,⟨0,by norm_num⟩)=N w := (hcenter v).trans (hv.trans hu)
    rw [hNval] at hev
    have hw := congrArg (fun z : I×Icc (-1:ℝ) 1 => (z.2:ℝ)) (hB.injective hev)
    have hw0 : w.2=⟨0,by norm_num⟩ := by
      apply Subtype.ext
      change (w.2:ℝ)=0
      change 0=eta*(w.2:ℝ) at hw
      exact (mul_eq_zero.mp hw.symm).resolve_left heta.1.ne'
    have hzcenter : N w=G (reparam r ((a+r)/2) w.1) := by
      rw [show w=(w.1,⟨0,by norm_num⟩) from Prod.ext rfl hw0,hNcenter']
    refine ⟨⟨reparam r ((a+r)/2) w.1,?_,hzcenter.symm⟩,hzK⟩
    dsimp [reparam]
    constructor <;> nlinarith [w.1.property.1,w.1.property.2]
  · rintro ⟨hz,hzK⟩
    have him : range (fun t : I => G (reparam r ((a+r)/2) t))=G '' Icc ((a+r)/2) r := by
      obtain ⟨q,_,hqt,hqr⟩ := actual_embedded_line_interval_path G hG.injective r ((a+r)/2) (by linarith)
      rw [uIcc_of_ge (by linarith : (a+r)/2≤r)] at hqr
      have hqeq : q=(fun t : I => G (reparam r ((a+r)/2) t)) := funext hqt
      rwa [hqeq] at hqr
    rw [←him] at hz
    obtain ⟨t,rfl⟩ := hz
    refine ⟨⟨⟨(t,⟨0,by norm_num⟩),hNcenter' t⟩,hzK⟩,?_⟩
    change G (reparam r ((a+r)/2) t)∈⋃ j : ℤ,L j
    exact mem_iUnion.mpr ⟨0,hL0.symm ▸ mem_range_self _⟩

#print axioms actual_left_whisker_family_collar_of_closed_rows
