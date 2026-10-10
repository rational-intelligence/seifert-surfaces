import NativeOriginalProductPrerequisitesV862
import ActualContainedAnnulusCoordinatesV778
import ActualAnnulusWholeFamilyWithSideChoiceV780
import ActualWholeCollarCoreProductExactV791

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped Manifold ContDiff
open Set Topology Manifold
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualOriginalAnnulusFullDiskProductV790

/-- Full product for the literal caller-supplied arbitrary annulus and SAME
    original disk. The contained smooth band is used internally only. -/
theorem given_original_disk_arbitrary_annulus_full_product
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D) :
    ∃ P : ClosedDisk ≃ₜ D.disk,
      (∀ z,P (CompressionAnnulus.capEdge z) = D.boundaryCircle.toFun z) ∧
      ∃ J : C(ClosedDisk × Time,E.Carrier),IsEmbedding J ∧
        (∀ x,J (x,middleTime) = D.toFun (P x)) ∧
        (∀ z t,J (CompressionAnnulus.capEdge z,t) = F.embedding.toFun (A.band (z,t))) ∧
        (range J ⊆ (𝓡∂ 3).interior E.Carrier) ∧
        range J ∩ F.image = range (fun p : Circle × Time => F.embedding.toFun (A.band p)) := by
  obtain ⟨u,hu,e,hwide,hei,heaxis,hblock,σ,hσ,b,hb,hbu,c,hc,hc0,hcb,hco,
    G,hGF,hGB,hGreg,hGireg,g,heqg,hg,hgF,hgb,hgc,hgi,cs,hM,hbd,hsm,hrank,hsemb,hΩ,d,hds,hde,
    W,hW,hAW,hWa,β,hβwide,hβ0,hβi,hβF,γ,hγ0,hγs,e',he',he's,he'i,hgc',τ,hτ,X,hX,htrans,
    O,hO,hκO,hOe,hXrad,δ,hδ,Ψ,hΨ0,hΨsm,hΨinj,hΨrank,hΨint,hΨder,
    a,ha,ha1,η,hη,hηδ,hcollar,
    ε,hε,h2εη,hεa,hwholeG,hγstrip,q,hq,h2q1,h2qε,U,V,hU,hV,hUVnn,hUVdiff,
    hUVbound,hUVleft,hUVright,C,hCsm,hCinj,hCrank,hCpair,hCtube,hCleft,hCright,hCintavoid,
    C₀,cp,hC₀formula,hC₀props,hcpprops,hcppair,hcpO,hcpK,hcpBoundary,
    B,hB,hBsm,hBA,P,hP,JB,hJB,hJBcenter,hJBlateral,hJBinterior,hJBinter,hC₀J,
    RB,hRB,hRBrem,hRBcap,hcaps,havoid,hattach⟩ :=
    CompressionActualWholeRoundedProductQuotient.given_original_disk_whole_rounded_product_quotient E F D A
  let _ := cs
  let _ := hM
  obtain ⟨βA,hβA,hβAval,hβAcore,hβAopen⟩ :=
    CompressionActualContainedAnnulusCoordinatesV778.contained_annulus_coordinates E F D A B hBA
  obtain ⟨R,hR,hRc,H,hH,hH0,hH1,hHcore⟩ :=
    CompressionActualAnnulusWholeFamilyWithSideChoiceV780.whole_annulus_relative_family_with_side_choice
      βA hβA hβAcore hβAopen
  let Rt : Time → Time := fun t => (R ((1:Circle),t)).2
  have hRtc : Continuous Rt := (R.continuous.comp (continuous_const.prodMk continuous_id)).snd
  have hRcoord (z : Circle) (t : Time) : R (z,t) = (z,Rt t) := by
    rcases hR with h | h
    · dsimp only [Rt]
      rw [h]
      rfl
    · dsimp only [Rt]
      rw [h]
      rfl
  have hRti : Function.Injective Rt := by
    intro t s he
    have hh : R ((1:Circle),t) = R (1,s) := by rw [hRcoord,hRcoord,he]
    exact congrArg (fun p : Circle × Time => p.2) (R.injective hh)
  have hRtm : Rt middleTime = middleTime := congrArg (fun p : Circle × Time => p.2) (hRc 1)
  let bA : C(Circle × Time,Circle × Time) := ⟨βA ∘ R,βA.continuous.comp R.continuous⟩
  have hbA : IsEmbedding bA := hβA.comp R.isEmbedding
  have hH0' (p : Circle × Time) : H (0,p) = bA p := hH0 p
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hnormal (s : Time) : σ*b*s.val ∈ Icc (-u) u := by
    apply abs_le.mp
    rw [abs_mul,abs_mul,hσabs,abs_of_pos hb,one_mul,abs_of_nonneg s.property.1]
    exact (mul_le_mul_of_nonneg_left s.property.2 hb.le).trans (by simpa using hbu)
  let Q : Time × (Circle × Time) → ℝ × F.surface := fun p => (σ*b*p.1.val,A.band p.2)
  have hQc : Continuous Q := (continuous_const.mul continuous_fst.subtype_val).prodMk
    (A.band.continuous.comp continuous_snd)
  have hQs (p : Time × (Circle × Time)) : Q p ∈ β.source :=
    hβwide ⟨hnormal p.1,hAW (mem_range_self p.2)⟩
  let wide : C(Time × (Circle × Time),E.Carrier) :=
    ⟨G ∘ β ∘ Q,G.continuous.comp (β.contMDiffOn_toFun.continuousOn.comp_continuous hQc hQs)⟩
  have hwidei : Function.Injective wide := by
    intro p q he
    have hh : Q p = Q q := β.toPartialEquiv.injOn (hQs p) (hQs q) (G.injective he)
    have hs := congrArg (fun x : ℝ × F.surface => x.1) hh
    have hA := congrArg (fun x : ℝ × F.surface => x.2) hh
    exact Prod.ext (Subtype.ext (mul_left_cancel₀ (mul_ne_zero hσne hb.ne') hs)) (A.embedded.injective hA)
  have hwideemb : IsEmbedding wide := (wide.continuous.isClosedEmbedding hwidei).isEmbedding
  have hwide0 (p : Circle × Time) : wide (0,p) = F.embedding.toFun (A.band p) := by
    change G (β (σ*b*0,A.band p)) = _
    rw [mul_zero,hβ0 _ (hAW (mem_range_self p)),hGF _ (mem_range_self _)]
  have hGg (p : D.disk) : G (g p) = D.toFun p := by rw [heqg,G.apply_symm_apply]
  have hwidecenter (z : Circle) (s : Time) : wide (s,(z,middleTime)) = D.toFun (c (z,s)) := by
    change G (β (σ*b*s.val,A.band (z,middleTime))) = _
    rw [A.center,← hγ0 z,← he' (σ*b*s.val,z,0),← hgc' (z,s),hGg]
  have hGFiff (x : E.Carrier) : G x ∈ F.image ↔ x ∈ F.image := by
    constructor
    · intro hx
      have he : x = G x := G.injective (hGF _ hx).symm
      exact he ▸ hx
    · intro hx
      rwa [hGF _ hx]
  have hGint (x : E.Carrier) (hx : x ∈ (𝓡∂ 3).interior E.Carrier) :
      G x ∈ (𝓡∂ 3).interior E.Carrier := by
    apply ((𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint _).mpr
    intro hbd'
    have he : x = G x := G.injective (hGB _ hbd').symm
    exact (((𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint _).mp hx) (he ▸ hbd')
  have hwideint (s : Time) (p : Circle × Time) : wide (s,p) ∈ (𝓡∂ 3).interior E.Carrier :=
    hGint _ (hβi (β.toPartialEquiv.map_source (hQs (s,p))))
  have hwideF (s : Time) (p : Circle × Time) : wide (s,p) ∈ F.image ↔ s.val = 0 := by
    change G (β (Q (s,p))) ∈ F.image ↔ _
    rw [hGFiff,hβF _ ⟨hnormal s,hAW (mem_range_self p)⟩]
    exact mul_eq_zero_iff_left (mul_ne_zero hσne hb.ne')
  let θ : Time → ℝ := fun t => ε*(2*(Rt t).val-1)
  have hθc : Continuous θ := continuous_const.mul
    ((continuous_const.mul hRtc.subtype_val).sub continuous_const)
  have hθ2 (t : Time) : θ t ∈ Icc (-2*ε) (2*ε) := by
    dsimp [θ]
    constructor <;> nlinarith [(Rt t).property.1,(Rt t).property.2]
  have hθε (t : Time) : θ t ∈ Icc (-η) η := by
    exact ⟨by linarith [(hθ2 t).1],by linarith [(hθ2 t).2]⟩
  have hθδ (t : Time) : θ t ∈ Icc (-δ) δ :=
    ⟨by linarith [(hθε t).1],by linarith [(hθε t).2]⟩
  let core : C(D.disk × Time,E.Carrier) :=
    ⟨fun p => G (Ψ p.1 (θ p.2)),G.continuous.comp (hΨsm.continuousOn.comp_continuous
      ((hθc.comp continuous_snd).prodMk continuous_fst) (fun p => ⟨hθδ p.2,mem_univ p.1⟩))⟩
  have hcorei : Function.Injective core := by
    intro p q he
    have he' : Ψ p.1 (θ p.2) = Ψ q.1 (θ q.2) := G.injective he
    have hh := hΨinj (x₁ := (θ p.2,p.1)) (x₂ := (θ q.2,q.1))
      ⟨hθδ p.2,mem_univ p.1⟩ ⟨hθδ q.2,mem_univ q.1⟩ he'
    have hp := congrArg (fun x : ℝ × D.disk => x.2) hh
    have ht := congrArg (fun x : ℝ × D.disk => x.1) hh
    have hRt : Rt p.2 = Rt q.2 := by
      apply Subtype.ext
      change ε*(2*(Rt p.2).val-1) = ε*(2*(Rt q.2).val-1) at ht
      nlinarith
    exact Prod.ext hp (hRti hRt)
  have hcoreemb : IsEmbedding core := (core.continuous.isClosedEmbedding hcorei).isEmbedding
  have hcorecenter (p : D.disk) : core (p,middleTime) = D.toFun p := by
    change G (Ψ p (θ middleTime)) = _
    have hm : θ middleTime = 0 := by dsimp [θ]; rw [hRtm]; norm_num [middleTime]
    rw [hm,hΨ0,hGg]
  have hcoreF (p : D.disk) (t : Time) : core (p,t) ∈ F.image ↔ p ∈ D.disk.boundary := hwholeG _ (hθ2 t) p
  have hcoreint (p : D.disk) (t : Time) : core (p,t) ∈ (𝓡∂ 3).interior E.Carrier :=
    hGint _ (hΨint p _ (hθδ t))
  let ac : Time := ⟨a/2,by constructor <;> linarith⟩
  have hac : 0 < ac.val := by dsimp [ac]; positivity
  have hcorecollar (z : Circle) (s t : Time) (hs : s.val ≤ ac.val) :
      core (c (z,s),t) = wide (s,bA (z,t)) := by
    change G (Ψ (c (z,s)) (θ t)) = G (β (σ*b*s.val,A.band (bA (z,t))))
    rw [hcollar z s (by dsimp [ac] at hs; linarith) _ (hθε t),he']
    change G (β (σ*b*s.val,γ (z,τ*(θ t)))) = G (β (σ*b*s.val,A.band (βA (R (z,t)))))
    rw [hβAval,hRcoord,hB]
  have hfar (p : D.disk) (hp : p ∉ c '' {q : Circle × Time | q.2.val < ac.val})
      (t : Time) (z : Circle × Time) : core (p,t) ≠ wide (0,z) := by
    have hpb : p ∉ D.disk.boundary := by
      intro hpb
      have hpr : p ∈ range D.boundaryCircle.toFun := by rwa [D.boundary_covers]
      obtain ⟨w,hw⟩ := hpr
      exact hp ⟨(w,0),hac,(hc0 w).trans hw⟩
    intro he
    apply hpb
    apply (hcoreF p t).mp
    rw [he,hwide0]
    exact mem_range_self (A.band z)
  obtain ⟨r,hr,hra,Jd,hJd,hJd0,hJdcore,hJdcenter,hJdwide⟩ :=
    CompressionActualWholeCollarCoreProductExactV791.whole_collar_core_product_exact
      c hc hco ac hac wide hwideemb bA hbA H hH hH0' hH1 hHcore core hcoreemb hcorecollar hfar
  have houtside (p : D.disk) (hp : p ∉ c '' {q : Circle × Time | q.2.val ≤ r.val}) :
      p ∉ c '' {q : Circle × Time | q.2.val < r.val} := by
    rintro ⟨q,hq,he⟩
    apply hp
    refine ⟨q,?_,he⟩
    change q.2.val ≤ r.val
    exact le_of_lt hq
  have hJdmid (p : D.disk) : Jd (p,middleTime) = D.toFun p := by
    by_cases hp : p ∈ c '' {q : Circle × Time | q.2.val ≤ r.val}
    · obtain ⟨⟨z,s⟩,hs,rfl⟩ := hp
      rw [hJdcenter z s hs,hwidecenter]
    · rw [hJdcore p middleTime (houtside p hp),hcorecenter]
  have hJdint (p : D.disk) (t : Time) : Jd (p,t) ∈ (𝓡∂ 3).interior E.Carrier := by
    by_cases hp : p ∈ c '' {q : Circle × Time | q.2.val ≤ r.val}
    · obtain ⟨⟨z,s⟩,hs,rfl⟩ := hp
      rw [hJdwide z s t hs]
      exact hwideint _ _
    · rw [hJdcore p t (houtside p hp)]
      exact hcoreint p t
  have hJdF (p : D.disk) (t : Time) : Jd (p,t) ∈ F.image ↔ p ∈ D.disk.boundary := by
    by_cases hp : p ∈ c '' {q : Circle × Time | q.2.val ≤ r.val}
    · obtain ⟨⟨z,s⟩,hs,rfl⟩ := hp
      rw [hJdwide z s t hs,hwideF,hcb]
    · rw [hJdcore p t (houtside p hp),hcoreF]
  let J : C(ClosedDisk × Time,E.Carrier) :=
    ⟨fun p => Jd (P p.1,p.2),Jd.continuous.comp ((P.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  have hJi : Function.Injective J := by
    intro p q he
    have hh := hJd.injective he
    have hp := congrArg (fun a : D.disk × Time => a.1) hh
    have ht := congrArg (fun a : D.disk × Time => a.2) hh
    exact Prod.ext (P.injective hp) ht
  have hJlateral (z : Circle) (t : Time) : J (CompressionAnnulus.capEdge z,t) = F.embedding.toFun (A.band (z,t)) := by
    change Jd (P (CompressionAnnulus.capEdge z),t) = _
    rw [hP,← hc0,hJd0,hwide0]
  refine ⟨P,hP,J,(J.continuous.isClosedEmbedding hJi).isEmbedding,fun x => hJdmid (P x),hJlateral,?_,?_⟩
  · rintro y ⟨p,rfl⟩
    exact hJdint (P p.1) p.2
  · apply Subset.antisymm
    · rintro y ⟨⟨⟨x,t⟩,rfl⟩,hy⟩
      have hpb : P x ∈ D.disk.boundary := (hJdF (P x) t).mp hy
      have hpr : P x ∈ range D.boundaryCircle.toFun := by rwa [D.boundary_covers]
      obtain ⟨z,hz⟩ := hpr
      have hx : x = CompressionAnnulus.capEdge z := P.injective (hz.symm.trans (hP z).symm)
      exact ⟨(z,t),by rw [hx,hJlateral]⟩
    · rintro y ⟨⟨z,t⟩,rfl⟩
      exact ⟨⟨(CompressionAnnulus.capEdge z,t),hJlateral z t⟩,mem_range_self (A.band (z,t))⟩

#print axioms given_original_disk_arbitrary_annulus_full_product
end CompressionActualOriginalAnnulusFullDiskProductV790
