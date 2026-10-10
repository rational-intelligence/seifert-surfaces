import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualLeftWhiskerFamilyCollar

open Set Topology Schoenflies CurveComplex unitInterval

/-- Reversing the actual line parameter gives the second, independently
constructed family-isolated endpoint half-collar. -/
theorem normalized_actual_right_whisker_family_collar
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s b : ℝ)
    (hT : 0<T) (hrs : r<s) (hsb : s<b)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (i j : ℤ), G x=G y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0)
    (K : Set Plane) (hcore : G '' Icc r s⊆K)
    (F : Plane ≃ₜ Plane) (hFK : F '' K=Plane.closedSquare 0 1) (hsF : F (G s)=Plane.mk (-1) 0)
    (p : Path (G s) (G b)) (hpE : IsEmbedding p)
    (hpt : ∀ t : I, p t=G (reparam s b t))
    (hpR : range p=G '' Icc s b) (hpK : range p∩K={G s})
    (W : Set Plane) (hW : IsOpen W) (hpW : range p⊆W) :
    ∃ rho : ℝ, 0<rho ∧ rho≤1 ∧ ∃ E : I×Icc (-1:ℝ) 1 → Plane,
      IsEmbedding E ∧ range E⊆W ∧
      (∀ w : Icc (-1:ℝ) 1, E (0,w)=F.symm (Plane.mk (-1) (-rho*w))) ∧
      (∀ t : I, E (t,⟨0,by norm_num⟩)=G (reparam s ((s+b)/2) t)) ∧
      range E∩K=(fun w : Icc (-1:ℝ) 1 => F.symm (Plane.mk (-1) (-rho*w))) '' univ ∧
      (range E\K)∩(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=
        (G '' Icc s ((s+b)/2))\K := by
  let G' : C(ℝ,Plane) := ⟨fun x => G (-x),G.continuous.comp continuous_neg⟩
  have hG' : IsClosedEmbedding G' := hG.comp (Homeomorph.neg ℝ).isClosedEmbedding
  obtain ⟨hclosed,hpair,hlf⟩ := normalized_line_deck_family G hG T hT hp hc
  have hroweq : (fun j : ℤ => range (fun x : ℝ => G' x+Plane.mk 0 ((j:ℝ)*T)))=
      (fun j : ℤ => range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) := by
    funext j
    ext z
    constructor
    · rintro ⟨x,rfl⟩; exact ⟨-x,rfl⟩
    · rintro ⟨x,rfl⟩; exact ⟨-x,by simp [G']⟩
  rw [←hroweq] at hclosed hpair hlf
  have him (u v : ℝ) : G' '' Icc (-v) (-u)=G '' Icc u v := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      refine ⟨-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,?_⟩
      simp [G']
  have hcore' : G' '' Icc (-s) (-r)⊆K := (him r s) ▸ hcore
  let F' := F.trans (Homeomorph.neg Plane)
  have hFK' : F' '' K=Plane.closedSquare 0 1 := by
    rw [show F' '' K=(fun z : Plane => -z) '' (F '' K) by rw [image_image]; rfl,hFK]
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      rw [mem_closedSquare_zero_one] at hw ⊢
      simpa [Plane.supNorm] using hw
    · intro hz
      refine ⟨-z,?_,neg_neg z⟩
      rw [mem_closedSquare_zero_one] at hz ⊢
      simpa [Plane.supNorm] using hz
  have hsF' : F' (G' (-s))=Plane.mk 1 0 := by
    change -(F (G (- -s)))=Plane.mk 1 0
    rw [neg_neg,hsF]
    ext i; fin_cases i <;> simp [Plane.mk]
  let q : Path (G' (-s)) (G' (-b)) := p.cast (by simp [G']) (by simp [G'])
  have hqE : IsEmbedding q := hpE
  have hqt (t : I) : q t=G' (reparam (-s) (-b) t) := by
    change p t=G (-(reparam (-s) (-b) t))
    rw [hpt]
    congr 1; simp only [reparam]; ring
  have hqR : range q=G' '' Icc (-b) (-s) := by rw [him]; exact hpR
  have hqK : range q∩K={G' (-s)} := by simpa [q,G'] using hpK
  obtain ⟨rho,hrho,hrho1,E,hE,hEW,hport,hcenter,hEK,hEL⟩ :=
    actual_left_whisker_family_collar_of_closed_rows G' hG' T (-b) (-s) (-r)
      (by linarith) (by linarith) hclosed hpair hlf K hcore' F' hFK' hsF' q hqE hqt hqR hqK W hW hpW
  have hport' (w : Icc (-1:ℝ) 1) : E (0,w)=F.symm (Plane.mk (-1) (-rho*w)) := by
    rw [hport]
    change F.symm (-(Plane.mk 1 (rho*w)))=_
    congr 1
    ext i; fin_cases i <;> simp [Plane.mk]
  have hcenter' (t : I) : E (t,⟨0,by norm_num⟩)=G (reparam s ((s+b)/2) t) := by
    rw [hcenter]
    change G (-(reparam (-s) ((-b+-s)/2) t))=_
    congr 1; simp only [reparam]; ring
  have hfamily : (⋃ j : ℤ, range (fun x : ℝ => G' x+Plane.mk 0 ((j:ℝ)*T)))=
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) := by
    exact congrArg (fun f : ℤ → Set Plane => ⋃ j : ℤ, f j) hroweq
  refine ⟨rho,hrho,hrho1,E,hE,hEW,hport',hcenter',?_,?_⟩
  · rw [hEK]
    congr 1
    funext w
    change F.symm (-(Plane.mk 1 (rho*w)))=_
    congr 1
    ext i; fin_cases i <;> simp [Plane.mk]
  · rw [hfamily] at hEL
    have hbounds : (-b+-s)/2= -((s+b)/2) := by ring
    rw [hbounds,him] at hEL
    exact hEL

#print axioms normalized_actual_right_whisker_family_collar
