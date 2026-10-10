import MovingLocalSection
import TraceCompactCutoff

open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

theorem zero_time_lift_contMDiffOn
    {U : Set (Time × M)} {Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2}
    (hY : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)) U) :
    ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) ((𝓡∂ 1).prod (𝓡∂ 3)).tangent ∞
      (fun q => (⟨q,(0,Y q)⟩ : TangentBundle ((𝓡∂ 1).prod (𝓡∂ 3)) (Time × M))) U := by
  have hzero : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 1).tangent ∞
      (fun q : Time × M => (⟨q.1,0⟩ : TangentBundle (𝓡∂ 1) Time)) :=
    (contMDiff_zeroSection ℝ (TangentSpace (𝓡∂ 1))).comp contMDiff_fst
  exact contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn (hzero.contMDiffOn.prodMk hY)

variable {S : CompactOrientedSurface.{u}} [T2Space M] [SecondCountableTopology M]
  {f g : NeatEmbedding S M}

/-- A partition of unity glues the actual moving local velocities into one
smooth tangent section. The convex constraints impose the prescribed trace
velocity and ambient boundary tangency simultaneously. -/
theorem normal_exists_global_tangent_velocity
    (F : SmoothNormalIsotopy S M f g) :
    ∃ X : (q : Time × M) → TangentSpace ((𝓡∂ 1).prod (𝓡∂ 3)) q,
      ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) ((𝓡∂ 1).prod (𝓡∂ 3)).tangent ∞
        (fun q => (⟨q,X q⟩ : TangentBundle ((𝓡∂ 1).prod (𝓡∂ 3)) (Time × M))) ∧
      (∀ q, (X q).1 = 0) ∧
      (∀ p, (X (normalTrace F p)).2 = traceVelocity F p) ∧
      ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (X q).2 = 0 := by
  letI : LocallyCompactSpace (EuclideanHalfSpace 3) := (𝓡∂ 3).locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanHalfSpace 3) M
  haveI : SigmaCompactSpace M := inferInstance
  let I := (𝓡∂ 1).prod (𝓡∂ 3)
  let C : (q : Time × M) → Set (TangentSpace I q) := fun q =>
    {w | (show Euc 1 × Euc 3 from w).1 = 0 ∧
      (∀ p, normalTrace F p = q → (show Euc 1 × Euc 3 from w).2 = (show Euc 3 from traceVelocity F p)) ∧
      (q.2 ∈ (𝓡∂ 3).boundary M → (show Euc 1 × Euc 3 from w).2 0 = 0)}
  have hconv (q : Time × M) : Convex ℝ (C q) := by
    change Convex ℝ {w : Euc 1 × Euc 3 | w.1 = 0 ∧
      (∀ p, normalTrace F p = q → w.2 = (show Euc 3 from traceVelocity F p)) ∧
      (q.2 ∈ (𝓡∂ 3).boundary M → w.2 0 = 0)}
    rw [convex_iff_add_mem]
    intro w hw z hz a b _ _ hab
    refine ⟨by simp only [Prod.smul_fst,Prod.fst_add,hw.1,hz.1,smul_zero,add_zero],?_,?_⟩
    · intro p hp
      change a • w.2 + b • z.2 = (show Euc 3 from traceVelocity F p)
      rw [hw.2.1 p hp,hz.2.1 p hp,← add_smul,hab,one_smul]
    · intro hqb
      change (a • w.2 + b • z.2) 0 = 0
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,hw.2.2 hqb,hz.2.2 hqb,mul_zero,add_zero]
  have hlocal (q : Time × M) : ∃ U ∈ 𝓝 q,
      ∃ Y : (r : Time × M) → TangentSpace I r,
        ContMDiffOn I I.tangent ∞ (fun r => (⟨r,Y r⟩ : TangentBundle I (Time × M))) U ∧
        ∀ r ∈ U, Y r ∈ C r := by
    by_cases hq : q ∈ range (normalTrace F)
    · obtain ⟨p,rfl⟩ := hq
      obtain ⟨U,hU,hpU,Y,hY,hagree,hboundary⟩ := normal_exists_local_tangent_velocity F p
      refine ⟨U,hU.mem_nhds hpU,fun r => (0,Y r),zero_time_lift_contMDiffOn hY,?_⟩
      intro r hr
      refine ⟨rfl,?_,?_⟩
      · intro s hs
        have hsr : normalTrace F s ∈ U := hs.symm ▸ hr
        have hag := congrArg (fun q => (show Euc 3 from Y q)) hs
        exact hag.symm.trans (hagree s hsr)
      · intro hb
        have hh := hboundary r hr hb
        rwa [inwardCoordinate_eq] at hh
    · let U := (range (normalTrace F))ᶜ
      have hU : IsOpen U := (normalTrace_isCompact F).isClosed.isOpen_compl
      refine ⟨U,hU.mem_nhds hq,fun _ => 0,(contMDiff_zeroSection ℝ (TangentSpace I)).contMDiffOn,?_⟩
      intro r hr
      refine ⟨rfl,?_,?_⟩
      · intro p hp
        exact False.elim (hr (hp ▸ mem_range_self p))
      · intro hb
        rfl
  obtain ⟨X,hX⟩ := exists_contMDiffSection_forall_mem_convex_of_local I (TangentSpace I)
    C hconv hlocal (n := (⊤ : ℕ∞))
  refine ⟨X,X.contMDiff,fun q => (hX q).1,?_,?_⟩
  · intro p
    exact (hX (normalTrace F p)).2.1 p rfl
  · intro q hqb
    exact (inwardCoordinate_eq q.2 (show TangentSpace (𝓡∂ 3) q.2 from (show Euc 1 × Euc 3 from X q).2)).trans ((hX q).2.2 hqb)

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
