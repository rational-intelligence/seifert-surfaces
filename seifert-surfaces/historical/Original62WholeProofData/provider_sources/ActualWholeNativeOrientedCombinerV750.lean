import NativeGeometryReplayV752

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped Manifold ContDiff
open Set Filter Topology TopologicalSpace Manifold
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionNativeSignedQuotientSeam CompressionLocalPiecesSupport
open CompressionPieceChartsSupport
noncomputable section
namespace CompressionActualWholeNativeOrientedCombinerV750

/-- The full actual product, quotient, rounding and native atlas construct the
approved strong realization on the chosen smooth internal annulus. The supplied
arbitrary annulus remains present in the containment bound. -/
theorem whole_native_oriented_realization_of_given_whole_smooth_witness
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D)
    (hwhole :
    ∃ u : ℝ,0 < u ∧
    ∃ e : PartialDiffeomorph (𝓘(ℝ,ℝ).prod ((𝓡 1).prod 𝓘(ℝ,ℝ))) (𝓡∂ 3)
      (ℝ × (Circle × ℝ)) E.Carrier ∞,
      (Icc (-u) u ×ˢ (univ ×ˢ Icc (-u) u) ⊆ e.source) ∧
      e.target ⊆ (𝓡∂ 3).interior E.Carrier ∧
      (∀ z : Circle,e (0,(z,0)) = F.embedding.toFun (D.surfaceLoop z)) ∧
      CompressionAnnulusCompatibleToroidalData.AnnulusCompatibleBlock E F D A u e ∧
    ∃ σ : ℝ,(σ = 1 ∨ σ = -1) ∧
    ∃ b : ℝ,0 < b ∧ b ≤ u ∧
    ∃ c : C(Circle × Time,D.disk),IsEmbedding c ∧
      (∀ z,c (z,0) = D.boundaryCircle.toFun z) ∧
      (∀ p,c p ∈ D.disk.boundary ↔ (p.2 : ℝ) = 0) ∧
      IsOpen (c '' {p : Circle × Time | (p.2 : ℝ) < 1}) ∧
    ∃ G : E.Carrier ≃ₜ E.Carrier,
      (∀ x ∈ F.image,G x = x) ∧
      (∀ x ∈ (𝓡∂ 3).boundary E.Carrier,G x = x) ∧
      ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞ G (range (fun z : Circle => e (0,(z,0))))ᶜ ∧
      ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞ G.symm (range (fun z : Circle => e (0,(z,0))))ᶜ ∧
    ∃ g : C(D.disk,E.Carrier),
      (∀ p,g p = G.symm (D.toFun p)) ∧ IsEmbedding g ∧
      (∀ p,g p ∈ F.image ↔ p ∈ D.disk.boundary) ∧
      (∀ p ∈ D.disk.boundary,g p = D.toFun p) ∧
      (∀ p : Circle × Time,g (c p) = e (σ*b*(p.2 : ℝ),(p.1,0))) ∧
      (∀ p,(𝓡∂ 3).IsInteriorPoint (g p)) ∧
    ∃ cs : ChartedSpace (EuclideanHalfSpace 2) D.disk,
      let _ := cs
      IsManifold (𝓡∂ 2) ∞ D.disk ∧
        (∀ p : D.disk,(𝓡∂ 2).IsBoundaryPoint p ↔ p ∈ D.disk.boundary) ∧ ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ g ∧
        (∀ p,Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) g p)) ∧
        IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ (E.toSphere ∘ g) ∧
        Nonempty (SmoothVolumeOrientation (𝓡∂ 2) D.disk) ∧
        ∃ d : PartialDiffeomorph ((𝓡 1).prod (𝓡∂ 1)) (𝓡∂ 2)
          CompressionNativeDiskCollarInverse.nativeDiskCollarOpen D.disk ∞,
          d.source = univ ∧
          (∀ p : CompressionNativeDiskCollarInverse.nativeDiskCollarOpen,d p = c p) ∧
        ∃ W : Set F.surface,IsOpen W ∧ range A.band ⊆ W ∧ W ⊆ F.surface.boundaryᶜ ∧
        ∃ β : PartialDiffeomorph (𝓘(ℝ,ℝ).prod (𝓡∂ 2)) (𝓡∂ 3)
          (ℝ × F.surface) E.Carrier ∞,
          (Icc (-u) u ×ˢ W ⊆ β.source) ∧
          (∀ p ∈ W,β (0,p) = F.embedding.toFun p) ∧
          β.target ⊆ (𝓡∂ 3).interior E.Carrier ∧
          (∀ p ∈ Icc (-u) u ×ˢ W,β p ∈ F.image ↔ p.1 = 0) ∧
        ∃ γ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 2)
          (Circle × ℝ) F.surface ∞,
          (∀ z,γ (z,0) = D.surfaceLoop z) ∧
          (∀ z,(z,0) ∈ γ.source) ∧
        ∃ e' : PartialDiffeomorph (𝓘(ℝ,ℝ).prod ((𝓡 1).prod 𝓘(ℝ,ℝ))) (𝓡∂ 3)
          (ℝ × (Circle × ℝ)) E.Carrier ∞,
          (∀ q,e' q = β (q.1,γ q.2)) ∧
          (∀ t ∈ Icc (-u) u,∀ z : Circle,(t,(z,0)) ∈ e'.source) ∧
          e'.target ⊆ (𝓡∂ 3).interior E.Carrier ∧
          (∀ p : Circle × Time,g (c p) = e' (σ*b*(p.2 : ℝ),(p.1,0))) ∧
        ∃ τ : ℝ,(τ = 1 ∨ τ = -1) ∧
        ∃ X : (a : E.Carrier) → TangentSpace (𝓡∂ 3) a,
          ContMDiff (𝓡∂ 3) (𝓡∂ 3).tangent ∞
            (fun a => (⟨a,X a⟩ : TangentBundle (𝓡∂ 3) E.Carrier)) ∧
          (∀ p,X (g p) ∉ (mfderiv (𝓡∂ 2) (𝓡∂ 3) g p).toLinearMap.range) ∧
        ∃ O : Set E.Carrier,IsOpen O ∧
          range (fun z => g (D.boundaryCircle.toFun z)) ⊆ O ∧ O ⊆ e'.target ∧
          (∀ a ∈ O,X a = τ • mfderiv
            (𝓘(ℝ,ℝ).prod ((𝓡 1).prod 𝓘(ℝ,ℝ))) (𝓡∂ 3)
            e' (e'.symm a) (0,(0,1))) ∧
        ∃ δ : ℝ,0 < δ ∧ ∃ Ψ : D.disk → ℝ → E.Carrier,
          (∀ p,Ψ p 0 = g p) ∧
          ContMDiffOn (𝓘(ℝ,ℝ).prod (𝓡∂ 2)) (𝓡∂ 3) ∞
            (fun q : ℝ × D.disk => Ψ q.2 q.1) (Icc (-δ) δ ×ˢ univ) ∧
          InjOn (fun q : ℝ × D.disk => Ψ q.2 q.1) (Icc (-δ) δ ×ˢ univ) ∧
          (∀ q ∈ Icc (-δ) δ ×ˢ (univ : Set D.disk),
            (mfderiv (𝓘(ℝ,ℝ).prod (𝓡∂ 2)) (𝓡∂ 3)
              (fun w : ℝ × D.disk => Ψ w.2 w.1) q).IsInvertible) ∧
          (∀ p,∀ t ∈ Icc (-δ) δ,(𝓡∂ 3).IsInteriorPoint (Ψ p t)) ∧
          (∀ p,∀ t ∈ Icc (-δ) δ,HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 3) (Ψ p) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X (Ψ p t)))) ∧
          ∃ a : ℝ,0 < a ∧ a < 1 ∧
          ∃ η : ℝ,0 < η ∧ η ≤ δ/2 ∧
            (∀ z : Circle,∀ s : Time,(s : ℝ) ≤ a → ∀ t ∈ Icc (-η) η,
              (σ*b*(s : ℝ),(z,τ*t)) ∈ e'.source) ∧
            (∀ z : Circle,∀ s : Time,(s : ℝ) ≤ a → ∀ t ∈ Icc (-η) η,
              Ψ (c (z,s)) t = e' (σ*b*(s : ℝ),(z,τ*t))) ∧
          ∃ ε : ℝ,0 < ε ∧ 2*ε < η ∧ ε < a ∧
            (∀ t ∈ Icc (-2*ε) (2*ε),∀ p : D.disk,
              G (Ψ p t) ∈ F.image ↔ p ∈ D.disk.boundary) ∧
            (∀ z : Circle,∀ t ∈ Icc (-2*ε) (2*ε),
              (z,τ*t) ∈ γ.source ∧ γ (z,τ*t) ∈ W ∩ A.removed) ∧
          ∃ q : ℝ,∃ hq : 0 < q,2*q < 1 ∧ 2*q < ε ∧ q ≤ ε/32 ∧
          ∃ U V : ℝ → ℝ,ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧
            (∀ t,0 ≤ U t ∧ 0 ≤ V t) ∧ (∀ t,V t-U t = t) ∧
            (∀ t ∈ Icc (-2*q) (2*q),U t ≤ 2*q ∧ V t ≤ 2*q) ∧
            (∀ t,t ≤ -q → U t = -t ∧ V t = 0) ∧
            (∀ t,q ≤ t → U t = 0 ∧ V t = t) ∧
          ∃ C : Fin 2 → Circle × ℝ → E.Carrier,
            (∀ k,ContMDiffOn ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 3) ∞ (C k)
              (univ ×ˢ Icc (-2*q) (2*q))) ∧
            (∀ k,InjOn (C k) (univ ×ˢ Icc (-2*q) (2*q))) ∧
            (∀ k p,p ∈ univ ×ˢ Ioo (-2*q) (2*q) →
              Function.Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ,ℝ)) (𝓡∂ 3) (C k) p)) ∧
            Pairwise (fun k l => Disjoint (C k '' (univ ×ˢ Icc (-2*q) (2*q)))
              (C l '' (univ ×ˢ Icc (-2*q) (2*q)))) ∧
            (∀ k z t,t ∈ Icc (-2*q) (2*q) → ∀ ht : V t ∈ Icc (0 : ℝ) 1,
              C k (z,t) = G (Ψ (c (z,⟨V t,ht⟩))
                ((if k = 0 then -1 else 1)*(ε+U t)))) ∧
            (∀ k z t,t ∈ Icc (-2*q) (-q) →
              C k (z,t) = F.embedding.toFun
                (γ (z,τ*((if k = 0 then -1 else 1)*(ε-t))))) ∧
            (∀ k z t,t ∈ Icc q (2*q) → ∀ ht : t ∈ Icc (0 : ℝ) 1,
              C k (z,t) = G (Ψ (c (z,⟨t,ht⟩)) ((if k = 0 then -1 else 1)*ε))) ∧
            (∀ k p,p ∈ univ ×ˢ Icc (-2*q) (2*q) →
              (𝓡∂ 3).IsInteriorPoint (C k p) ∧ C k p ∉ range D.toFun) ∧
          ∃ C₀ cp : Fin 2 → D.disk → E.Carrier,
            (∀ k p,C₀ k p = G (Ψ p ((if k = 0 then -1 else 1)*ε))) ∧
            (∀ k,ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ (C₀ k) ∧ IsEmbedding (C₀ k) ∧
              IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ (E.toSphere ∘ C₀ k) ∧
              (∀ p,Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) (C₀ k) p))) ∧
            (∀ k,ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ (cp k) ∧ IsEmbedding (cp k) ∧
              IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ (E.toSphere ∘ cp k) ∧
              (∀ p,Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 3) (cp k) p)) ∧
              (∀ p,(𝓡∂ 3).IsInteriorPoint (cp k p)) ∧
              Disjoint (range (cp k)) (range D.toFun) ∧ Disjoint (range (cp k)) F.image) ∧
            Pairwise (fun k l => Disjoint (range (cp k)) (range (cp l))) ∧
            (∀ (k : Fin 2) (p : Circle × Time),(p.2 : ℝ) < 2*q → cp k (c p) = C k (p.1,(p.2 : ℝ))) ∧
            (∀ (k : Fin 2) (p : D.disk),p ∉ c '' {p : Circle × Time | (p.2 : ℝ) ≤ q} → cp k p = C₀ k p) ∧
            (∀ k z,cp k (D.boundaryCircle.toFun z) = C k (z,0)) ∧
          ∃ B : CompressionAnnulus D,
            (∀ p : Circle × Time,B.band p = γ (p.1,τ*(ε*(2*(p.2 : ℝ)-1)))) ∧
            ContMDiff ((𝓡 1).prod (𝓡∂ 1)) (𝓡∂ 2) ∞ B.band ∧
            range B.band ⊆ A.removed ∧
          ∃ P : ClosedDisk ≃ₜ D.disk,
            (∀ z,P (CompressionAnnulus.capEdge z) = D.boundaryCircle.toFun z) ∧
          ∃ J : C(ClosedDisk × Time,E.Carrier),IsEmbedding J ∧
            (∀ x,J (x,middleTime) = D.toFun (P x)) ∧
            (∀ z t,J (CompressionAnnulus.capEdge z,t) = F.embedding.toFun (B.band (z,t))) ∧
            range J ⊆ (𝓡∂ 3).interior E.Carrier ∧
            range J ∩ F.image = range (fun p : Circle × Time => F.embedding.toFun (B.band p)) ∧
            (∀ k x,C₀ k (P x) = J (x,CompressionAnnulus.sideTime k)) ∧
          ∃ R : C(B.SurgerySpace,E.Carrier),IsEmbedding R ∧
            (∀ x : B.Remainder,R (B.remainderInclusion x) = F.embedding.toFun x) ∧
            (∀ k x,R (B.capInclusion k x) = J (x,CompressionAnnulus.sideTime k)) ∧
            Disjoint (range (C₀ 0)) (range (C₀ 1)) ∧
            (∀ k,Disjoint (range (C₀ k)) (range D.toFun)) ∧
            (∀ k,range (C₀ k) ∩ (F.embedding.toFun '' B.removedᶜ) =
              range (fun z : Circle => F.embedding.toFun (B.band (z,CompressionAnnulus.sideTime k)))) ∧
          ∃ I : TopologicalAmbientIsotopy E.Carrier,∃ Wr : Set E.Carrier,
            IsOpen Wr ∧ Disjoint (closure Wr) (range D.toFun) ∧
            Disjoint (closure Wr) ((𝓡∂ 3).boundary E.Carrier) ∧
            (∀ t x,x ∉ Wr → I.stage t x = x) ∧
            (∀ t x,x ∈ (𝓡∂ 3).boundary E.Carrier → I.stage t x = x) ∧
            (∀ k : Fin 2,∀ z : Circle,
              F.embedding.toFun (B.band (z,CompressionAnnulus.sideTime k)) ∈ Wr) ∧
            (∀ k z t,∀ ht : t ∈ Icc (0 : ℝ) 1,t ∈ Icc (0 : ℝ) q →
              I.stage 1 (R (B.capInclusion k (P.symm (c (z,⟨t,ht⟩))))) = C k (z,t)) ∧
            (∀ k : Fin 2,Disjoint (closure Wr)
              ((fun p : D.disk => G (Ψ p ((if k = 0 then -1 else 1)*ε))) ''
                (c '' {p : Circle × Time | (p.2 : ℝ) < a/2})ᶜ)) ∧
            (∀ k : Fin 2,∀ p : Circle × (ℝ × ℝ),
              CompressionExactCornerRoundingFamily.cornerCoordinates q hq.ne' p.2 ∈
                CompressionSupportedRectangularFamilyHomeomorph.closedSquare →
              (σ*b*p.2.1,(p.1,τ*((if k = 0 then -1 else 1)*(ε+p.2.2)))) ∈ e'.source) ∧
            (closure Wr ⊆ ⋃ k : Fin 2,
              (fun p : Circle × (ℝ × ℝ) =>
                G (e' (σ*b*p.2.1,(p.1,τ*((if k = 0 then -1 else 1)*(ε+p.2.2)))))) ''
                {p | CompressionExactCornerRoundingFamily.cornerCoordinates q hq.ne' p.2 ∈
                  CompressionSupportedRectangularFamilyHomeomorph.closedSquare}) ∧
            (∀ k z t,t ∈ Icc (-6*q) (6*q) →
              I.stage 1 (G (e' ⟨σ*b*max t 0,
                ⟨z,τ*((if k = 0 then -1 else 1)*(ε+max (-t) 0))⟩⟩)) = C k (z,t)) ∧
            (∀ k p,I.stage 1 (R (B.capInclusion k (P.symm p))) = cp k p) ∧
          ∃ Rs : C(B.SurgerySpace,E.Carrier),IsEmbedding Rs ∧
            (∀ x,Rs x = I.stage 1 (R x)) ∧
          ∃ N : Set F.surface,IsOpen N ∧ Disjoint (closure N) F.surface.boundary ∧
            (∀ k z,B.band (z,CompressionAnnulus.sideTime k) ∈ N) ∧
            (∀ x : B.Remainder,(x : F.surface) ∉ N →
              Rs (B.remainderInclusion x) = F.embedding.toFun x) ∧
            (∀ x : B.Remainder,(x : F.surface) ∈ F.surface.boundary →
              Rs (B.remainderInclusion x) = F.embedding.toFun x) ∧
            (∀ k p,Rs (B.capInclusion k (P.symm p)) = cp k p) ∧
          ∃ sc : Fin 2 → C(CompressionNativeSignedQuotientSeam.Signed,B.SurgerySpace),
            (∀ k,IsEmbedding (sc k)) ∧
            (∀ k,IsOpen ((sc k) '' CompressionNativeSignedQuotientSeam.middle)) ∧
            (∀ k z,sc k (z,⟨0,by norm_num⟩) = B.remainderInclusion (B.edgePoint k z)) ∧
            (∀ k p,Rs (sc k p) = C k (p.1,(3*q/2)*(p.2 : ℝ))) ∧
          ∃ csQ : ChartedSpace (EuclideanHalfSpace 2) B.SurgerySpace,
            let _ := csQ
            IsManifold (𝓡∂ 2) ∞ B.SurgerySpace ∧
            IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ Rs ∧
            (𝓡∂ 2).boundary B.SurgerySpace =
              B.remainderInclusion '' {x : B.Remainder | x.val ∈ F.surface.boundary} ∧
            (Rs ⁻¹' ((𝓡∂ 3).boundary E.Carrier) = (𝓡∂ 2).boundary B.SurgerySpace) ∧
            (∀ y ∈ (𝓡∂ 2).boundary B.SurgerySpace,
              ∃ w : TangentSpace (𝓡∂ 2) y,
                inwardCoordinate (Rs y) (mfderiv (𝓡∂ 2) (𝓡∂ 3) Rs y w) ≠ 0) ∧
            (∀ k v,B.capInclusion k v ∉ (𝓡∂ 2).boundary B.SurgerySpace)) :
    ∃ B : CompressionAnnulus D,range B.band ⊆ A.removed ∧
      ∃ Pout : SmoothCompressionSurface B,
        Nonempty (SeifertSurfaces.OriginalEndpoints.ActualCompressionRealization E F B Pout) := by
  obtain ⟨u,hu,e,hwide,hei,heaxis,hblock,σ,hσ,b,hb,hbu,c,hc,hc0,hcb,hco,
    G,hGF,hGB,hGreg,hGireg,g,heqg,hg,hgF,hgb,hgc,hgi,cs,hM,hbd,hsm,hrank,hsemb,hΩ,d,hds,hde,
    W,hW,hAW,hWa,β,hβwide,hβ0,hβi,hβF,γ,hγ0,hγs,e',he',he's,he'i,hgc',τ,hτ,X,hX,htrans,
    O,hO,hκO,hOe,hXrad,δ,hδ,Ψ,hΨ0,hΨsm,hΨinj,hΨrank,hΨint,hΨder,
    a,ha,ha1,η,hη,hηδ,hcollarSource,hcollar,
    ε,hε,h2εη,hεa,hwholeG,hγstrip,q,hq,h2q1,h2qε,hqε32,U,V,hU,hV,hUVnn,hUVdiff,
    hUVbound,hUVleft,hUVright,C,hCsm,hCinj,hCrank,hCpair,hCtube,hCleft,hCright,hCintavoid,
    C₀,cp,hC₀formula,hC₀props,hcpprops,hcppair,hcpO,hcpK,hcpBoundary,
    B,hB,hBsm,hBA,P,hP,J,hJ,hJcenter,hJlateral,hJinterior,hJinter,hC₀J,
    R,hR,hRrem,hRcap,hcaps,havoid,hattach,
    I,Wr,hWr,hWrD,hWrB,hIoff,hIB,hIedges,hIcaplocal,hIcore,hIsource,hIcontain,hIcorner,hIcp,
    Rs,hRs,hRsI,N,hN,hNbd,hNedge,hRsunchanged,hRsbd,hRscap,sc,hsc,hscopen,hsczero,hscRs,csQ,hMQ,hRsSmooth,hQbd,hQpre,hQtrans,hQcaps⟩ :=
    hwhole
  let _ := cs
  let _ := hM
  let _ := csQ
  let _ := hMQ
  have hsign (k : Fin 2) : (if k = 0 then -1 else 1 : ℝ) = -1 ∨
      (if k = 0 then -1 else 1 : ℝ) = 1 := by split_ifs <;> simp
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have h5q : 5*q < 1 := by linarith
  have hnormal (v : ℝ) (hv : v ∈ Icc (-5*q) (5*q)) : σ*b*v ∈ Icc (-u) u := by
    apply abs_le.mp
    rw [abs_mul,abs_mul,hσabs,abs_of_pos hb,one_mul]
    have hv1 : |v| ≤ 1 := abs_le.mpr ⟨by linarith [hv.1],by linarith [hv.2]⟩
    exact (mul_le_mul_of_nonneg_left hv1 hb.le).trans (by simpa using hbu)
  have hγwide (k : Fin 2) (z : Circle) (w : ℝ) (hw : w ∈ Icc (-5*q) (5*q)) :
      γ (z,τ*((if k = 0 then -1 else 1)*(ε+w))) ∈ W := by
    apply (hγstrip z _ ?_).2.1
    rcases hsign k with h | h <;> rw [h] <;> constructor <;> linarith [hw.1,hw.2]
  obtain ⟨hclass,hclassoutside⟩ :=
    CompressionActualRemainderSupportClassification.actual_rounding_support_on_original_surface
      E F D B G hGF γ β e' he' hq hε (by linarith) (mul_ne_zero hσne hb.ne') hτ
      W hβ0 hβF hnormal hγwide hB Wr hIcontain
  have hrem (x : B.Remainder) : Rs (B.remainderInclusion x) = I.stage 1 (F.embedding.toFun x) := by
    rw [hRsI,hRrem]
  have hγnear (k : Fin 2) (z : Circle) (w : ℝ) (hw : w ∈ Icc (0 : ℝ) q) :
      γ (z,τ*((if k = 0 then -1 else 1)*(ε+w))) ∈ W :=
    hγwide k z w ⟨by linarith [hw.1],by linarith [hw.2]⟩
  have haffected := CompressionActualAffectedRemainderSeamCover.actual_affected_remainder_in_native_seam
    E F D B hq G hGF γ β e' he' W hβ0 hγnear I Wr C hIcorner Rs hRs.injective hrem (fun k => sc k) hscRs hclassoutside
  have hoff (x : B.Remainder) (hx : F.embedding.toFun x ∉ closure Wr) :
      Rs (B.remainderInclusion x) = F.embedding.toFun x := by
    rw [hrem,hIoff 1 _ (fun hy => hx (subset_closure hy))]
  obtain ⟨κo,hκoemb,hκoedge,hκoout,hκoopen,hκocoord,hκoint,hκopair⟩ :=
    CompressionWholeSignedOuterCollars.given_signed_strip_annulus_outer_collars E F D γ hγ0 τ hτ
      hε (show 0 < q by positivity) (by linarith)
      (fun z t ht => ⟨(hγstrip z t ht).1,hWa (hγstrip z t ht).2.1⟩) B hB
  have hcr (k : Fin 2) (p : Circle × Time) (hp : (p.2 : ℝ) < 2*(q)) :
      cp k (c p) = C k (p.1,(p.2 : ℝ)) := by
    exact hcpO k p hp
  have hrr (k : Fin 2) (p : Circle × Time) (hp : (p.2 : ℝ) < 1) :
      Rs (B.remainderInclusion (κo k p)) = C k (p.1,-2*(q)*(p.2 : ℝ)) := by
    let sign : ℝ := if k = 0 then -1 else 1
    have hsign : sign = -1 ∨ sign = 1 := by dsimp [sign];split_ifs <;> simp
    have hqt : 0 ≤ 2*q*(p.2 : ℝ) := mul_nonneg (by positivity) p.2.property.1
    have ht : -2*q*(p.2 : ℝ) ∈ Icc (-6*q) (6*q) :=
      ⟨by nlinarith [p.2.property.2],by nlinarith [p.2.property.1]⟩
    have htγ : sign*(ε+2*q*(p.2 : ℝ)) ∈ Icc (-2*ε) (2*ε) := by
      rcases hsign with h | h <;> rw [h] <;> constructor <;> nlinarith [p.2.property.1,p.2.property.2]
    have he : G (e' (0,(p.1,τ*(sign*(ε+2*q*(p.2 : ℝ)))))) = F.embedding.toFun (κo k p) := by
      rw [he',hβ0 _ (hγstrip p.1 _ htγ).2.1,hGF _ (mem_range_self _),hκocoord]
    have hh := hIcorner k p.1 (-2*q*(p.2 : ℝ)) ht
    have hn : -2*q*(p.2 : ℝ) ≤ 0 := by nlinarith
    have hneg : -(-2*q*(p.2 : ℝ)) = 2*q*(p.2 : ℝ) := by ring
    rw [max_eq_right hn,hneg,max_eq_left hqt,mul_zero] at hh
    change I.stage 1 (G (e' (0,(p.1,τ*(sign*(ε+2*q*(p.2 : ℝ))))))) = _ at hh
    rw [he] at hh
    rw [hRsI,hRrem]
    convert hh using 1 <;> congr 2 <;> ring
  have hPsymmb (z : Circle) : P.symm (D.boundaryCircle.toFun z) = CompressionAnnulus.capEdge z := by
    rw [← hP,P.symm_apply_apply]
  have hnativebd : (𝓡∂ 2).boundary D.disk = D.disk.boundary := Set.ext (fun p => hbd p)
  have hPboundary : P.symm '' (𝓡∂ 2).boundary D.disk = closedDiskBoundary := by
    rw [hnativebd,← D.boundary_covers,← Set.range_comp]
    have he : (P.symm ∘ D.boundaryCircle.toFun) = CompressionAnnulus.capEdge := funext hPsymmb
    rw [he,CompressionCapRadialSupport.capEdge_range]
  have hHb (p : D.disk) : P.symm p ∈ closedDiskBoundary ↔ p ∈ D.disk.boundary := by
    rw [← hPboundary,hnativebd]
    constructor
    · rintro ⟨x,hx,he⟩
      exact P.symm.injective he ▸ hx
    · exact fun hp => ⟨p,hp,rfl⟩
  have hHint (p : D.disk) : P.symm p ∈ diskInterior ↔ p ∉ D.disk.boundary := by
    rw [← hHb p]
    change ‖(P.symm p : Euc 2)‖ < 1 ↔ ‖(P.symm p : Euc 2)‖ ≠ 1
    have hle : ‖(P.symm p : Euc 2)‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using (P.symm p).property
    exact ⟨ne_of_lt,fun h => lt_of_le_of_ne hle h⟩
  obtain ⟨hpositive,hnegative⟩ :=
    CompressionActualNativeSeamDecomposition.actual_native_seam_decomposition
      E F D B hq h2q1 P.symm c κo C
      (fun x => Rs (B.remainderInclusion x)) hrr cp hcr Rs hRs.injective
      (fun _ => rfl) hRscap (fun k => sc k) hscRs
  have hΨF (z : Circle) (s : Time) (r : ℝ) (hr : r ∈ Icc (-2*ε) (2*ε)) :
      G (Ψ (c (z,s)) r) ∈ F.image ↔ (s : ℝ) = 0 := (hwholeG r hr _).trans (hcb _)
  have hΨzero (z : Circle) (r : ℝ) (hr : r ∈ Icc (-2*ε) (2*ε)) :
      G (Ψ (c (z,0)) r) = F.embedding.toFun (γ (z,τ*r)) := by
    have hrη : r ∈ Icc (-η) η := ⟨by linarith [hr.1],by linarith [hr.2]⟩
    rw [hcollar z 0 (by simpa using ha.le) r hrη]
    simp only [show ((0:Time):ℝ)=0 from rfl,mul_zero]
    change G (e' (0,(z,τ*r))) = _
    rw [he',hβ0 _ (hγstrip z r hr).2.1,hGF _ (mem_range_self _)]
  have hCs (k : Fin 2) :=
    CompressionActualRoundedSeamOriginalSurfaceAgreement.actual_rounded_seam_original_surface_agreement
      E F D hq h2qε h2q1 (hsign k) c Ψ G γ hΨF hΨzero U V hUVdiff
      (fun t ht => ⟨(hUVnn t).1,(hUVbound t ht).1,(hUVnn t).2,(hUVbound t ht).2⟩)
      (C k) (hCtube k)
  let α : Fin 2 → ℝ := fun k => τ*(if k = 0 then -1 else 1)
  have hτne : τ ≠ 0 := by rcases hτ with rfl | rfl <;> norm_num
  have hα (k : Fin 2) : α k ≠ 0 := by
    apply mul_ne_zero hτne
    rcases hsign k with h | h <;> rw [h] <;> norm_num
  have hγseam (k : Fin 2) (z : Circle) (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      (z,α k*(ε-(3*q/2)*t)) ∈ γ.source := by
    have hr : (if k = 0 then -1 else 1 : ℝ)*(ε-(3*q/2)*t) ∈ Icc (-2*ε) (2*ε) := by
      rcases hsign k with h | h <;> rw [h] <;> constructor <;> nlinarith [ht.1,ht.2]
    simpa only [α,mul_assoc] using (hγstrip z _ hr).1
  have hCsurface (k : Fin 2) (p : Signed) (hp : p ∈ middle)
      (hCF : C k (p.1,(3*q/2)*(p.2 : ℝ)) ∈ F.image) :
      C k (p.1,(3*q/2)*(p.2 : ℝ)) =
        F.embedding.toFun (γ (p.1,α k*(ε-(3*q/2)*(p.2 : ℝ)))) := by
    have ht : (3*q/2)*(p.2 : ℝ) ∈ Icc (-2*q) (2*q) :=
      ⟨by nlinarith [p.2.property.1],by nlinarith [p.2.property.2]⟩
    convert hCs k p.1 _ ht hCF using 1 <;> congr 2 <;> dsimp [α] <;> ring
  have hUinhabited := CompressionActualUntouchedOriginalPoint.actual_untouched_original_point
    E F D B hε (by linarith) hτ γ (fun z t ht => (hγstrip z t ht).1) hB Wr hclass
  obtain ⟨ΩD⟩ := hΩ
  obtain ⟨Ω,dU,hUs,hUval,hΩray⟩ :=
    CompressionActualNativeRoundedQuotientOrientation.actual_native_rounded_quotient_orientation
      E F D B ΩD P.symm hPboundary hHint Rs hRsSmooth cp hRscap
      (fun k => (hcpprops k).1) (fun k => (hcpprops k).2.2.2.1)
      (fun k => (hcpprops k).2.2.2.2.1)
      (show 0 < 3*q/2 by positivity) (show 3*q/2 < 2*q by linarith) (show 3*q/2 < 1 by linarith)
      c hcb sc hsc hscopen hsczero (fun k p _ hpt => hpositive k p hpt)
      (fun k p _ hpt => ⟨_,hnegative k p hpt.le⟩)
      C hscRs hCsm hCrank (fun k p hp => (hCintavoid k p hp).1) hCpair α hα γ hγseam hCsurface
      Wr hoff haffected hUinhabited
  obtain ⟨N₁,hN₁,hN₁pre,hN₁bd,hN₁edges⟩ :=
    CompressionActualClosedSupportSourceSeam.actual_closed_support_source_seam E F D B Wr hWrB hIedges
  let U₁ : Opens F.surface := ⟨outsideBand B ∩ (F.embedding.toFun ⁻¹' closure Wr)ᶜ,
    (outsideBand_open B).inter (isClosed_closure.preimage
      F.embedding.smoothEmbedding.isEmbedding.continuous).isOpen_compl⟩
  obtain ⟨mark,hmark,hmarks,hmarko⟩ :=
    CompressionActualNativeOrientedRemainderMarking.actual_native_oriented_global_remainder_marking
      E F D B Rs hRsSmooth.isImmersion Wr hoff N₁ hN₁pre hN₁edges U₁ rfl dU hUs hUval Ω hΩray
  have hN₁unchanged (x : B.Remainder) (hx : x.val ∉ N₁) :
      Rs (B.remainderInclusion x) = F.embedding.toFun x :=
    hoff x (fun hy => hx (hN₁pre hy))
  have hJranges (k : Fin 2) :
      range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime k)) = range (C₀ k) := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨P x,hC₀J k x⟩
    · rintro ⟨p,rfl⟩
      exact ⟨P.symm p,(hC₀J k (P.symm p)).symm.trans
        (congrArg (C₀ k) (P.apply_symm_apply p))⟩
  have hJcaps : Disjoint
      (range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime 0)))
      (range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime 1))) := by
    rw [hJranges,hJranges]
    exact hcaps
  have hJavoid (k : Fin 2) : Disjoint
      (range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime k))) (range D.toFun) := by
    rw [hJranges]
    exact havoid k
  have hJattach (k : Fin 2) :
      range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime k)) ∩
        (F.embedding.toFun '' B.removedᶜ) =
      range (fun z : Circle => F.embedding.toFun (B.band (z,CompressionAnnulus.sideTime k))) := by
    rw [hJranges]
    exact hattach k
  obtain ⟨Pout,hPout⟩ :=
    CompressionActualCompressionNativeRealizationAssemblyV728.actual_compression_realization_from_native_geometry
      E F D B Ω Rs hRsSmooth hQbd hQpre hQtrans P hP
      J hJ hJcenter hJlateral hJinterior hJinter hJcaps hJavoid hJattach
      R hR hRrem hRcap I Wr hWr hIedges hWrB hWrD hIoff hIB hRsI
      N₁ hN₁ hN₁edges hN₁bd hN₁unchanged hRsbd mark hmark hmarks hmarko
  exact ⟨B,hBA,Pout,hPout⟩

#print axioms whole_native_oriented_realization_of_given_whole_smooth_witness
end CompressionActualWholeNativeOrientedCombinerV750
