import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryQuotientDeformation
import CurveComplexGenusTwo.Topology.ActualModelHomology.SourceSurvivingGraphJointStarContraction
import CurveComplexGenusTwo.Topology.ActualModelHomology.SourceSurvivingGraphMiddleInverseDictionary
import CurveComplexGenusTwo.Topology.ActualModelHomology.SourceSurvivingGraphOverlapInverseDictionary
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualEdgeParameterQuotientCandidate
import CurveComplexGenusTwo.Topology.ActualModelHomology.SourceSurvivingHandleIntervalOpenEmbedding
import CurveComplexGenusTwo.Topology.ActualModelHomology.SourceSurvivingGraphIncidenceKernel
import CurveComplexGenusTwo.Octagon.GraphMV.DiscreteHZero
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Piecewise
namespace CurveComplex.Hyperbolic.OneBoundaryRay
open Set Topology CategoryTheory CategoryTheory.Limits ContinuousMap CircleHomologyComputation
open CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000
theorem actual_one_boundary_surviving_graph_homology_one (p : ℕ) :
    Nonempty (integralHomology (actualSurvivingBoundary p) 1 ≅
      ModuleCat.of ℤ (Fin (2 * p) → ℤ)) := by
  classical
  have hCoordinates (X D J : Type) [TopologicalSpace X] [TopologicalSpace D] [Fintype D] [DecidableEq D]
      [DiscreteTopology D] [TopologicalSpace J] [ContractibleSpace J]
      (T : X ≃ₜ (D × J)) :
      ∃ e : H X 0 ≃ₗ[ℤ] (D → ℤ),
        (∀ x : X, e (pointClass (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x) (1:ℤ))=Pi.single (T x).1 (1:ℤ)) ∧
        IsZero (H X 1) := by
    classical
    let heq : X ≃ₕ D := T.toHomotopyEquiv.trans
      (((ContinuousMap.HomotopyEquiv.refl D).prodCongr
        (ContractibleSpace.hequiv_unit J).some).trans
          (Homeomorph.prodUnique D Unit).toHomotopyEquiv)
    let e := ((homotopyHomologyIso heq 0) ≪≫
      CurveComplex.Octagon.AttachingMap.GraphMV.finiteDiscreteH0Iso D).toLinearEquiv
    have hpmap (x : X) : pointClass (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) ≫ (homotopyHomologyIso heq 0).hom=
      pointClass (TopCat.toSSet.obj (TopCat.of D)) (TopCat.toSSetObj₀Equiv.symm (T x).1) := by
      change pointClass _ _ ≫ HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom heq.toFun)) RZ) 0=_
      rw [pointClass_map]
      congr 1
    refine ⟨e,?_,?_⟩
    · intro x
      change (pointClass (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) ≫ ((homotopyHomologyIso heq 0).hom ≫
          (CurveComplex.Octagon.AttachingMap.GraphMV.finiteDiscreteH0Iso D).hom)) (1:ℤ)=_
      rw [← Category.assoc,hpmap]
      exact CurveComplex.Octagon.AttachingMap.GraphMV.finiteDiscreteH0Iso_point D (T x).1
    · exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (ModuleCat.{0} ℤ) 1 (ModuleCat.of ℤ ℤ) (TopCat.of D) (by omega)).of_iso
          (homotopyHomologyIso heq 1)
  obtain ⟨U,V,hU,hV,hcover,hEU,hCU,hVr,hContract⟩ := source_surviving_graph_joint_star_contraction p
  obtain ⟨Vm,hVm,hVrM,TM,hTMinv⟩ := source_surviving_graph_middle_inverse_dictionary p
  have hVmEq : Vm=V := hVrM.trans hVr.symm
  cases hVmEq
  obtain ⟨Uo,Vo,hUo,hVo,hCoverO,hEUo,hCUo,hVrO,TO,hTOinv⟩ := source_surviving_graph_overlap_inverse_dictionary p
  have hVoEq : Vo=V := hVrO.trans hVr.symm
  cases hVoEq
  have hUoEq : Uo=U := by
    ext x
    obtain ⟨z,hz⟩ := (source_actual_edge_parameter_map_isQuotientMap p).surjective x
    cases z with
    | inl z =>
      change handleEdge p z.1.1 z.1.2 z.2=x at hz
      rw [← hz,hEU,hEUo]
    | inr z =>
      have hx : x.val.val=Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1)
          (rawEdgePoint (p:=p) (.inr ()) ⟨z.val,⟨z.property.1,z.property.2.le⟩⟩ false) := by
        rw [← hz,rawEdgePoint_seam]
        rfl
      exact iff_of_true (hCUo x _ z.property.2 hx) (hCU x _ z.property.2 hx)
  cases hUoEq
  let X := TopCat.of (actualSurvivingBoundary p)
  let I := U∩V
  let Jm := Ioo (1/4:ℝ) (3/4:ℝ)
  let Jo := Ioo (1/4:ℝ) (3/8:ℝ)
  have : ContractibleSpace Jm := (convex_Ioo (1/4:ℝ) (3/4:ℝ)).contractibleSpace
    ⟨1/2,by constructor <;> norm_num⟩
  have : ContractibleSpace Jo := (convex_Ioo (1/4:ℝ) (3/8:ℝ)).contractibleSpace
    ⟨5/16,by constructor <;> norm_num⟩
  have : ContractibleSpace U := hContract
  obtain ⟨phi,hPhi,hV1⟩ := hCoordinates V (Fin (2*p)) Jm TM
  obtain ⟨psi,hPsi,hI1⟩ := hCoordinates I (Fin (2*p) × Bool) Jo TO
  let incU := actualSubsetHomologyMap X I U inter_subset_left 0
  let incV := actualSubsetHomologyMap X I V inter_subset_right 0
  let u : H U 0 ≃ₗ[ℤ] ℤ := (asIso ((TopCat.of U).singularHomology₀ε RZ)).toLinearEquiv
  let zPt (d : Fin (2*p) × Bool) : I := TO.symm (d,⟨5/16,by constructor <;> norm_num⟩)
  let P : (Fin (2*p) × Bool) → H I 0 := fun d =>
    pointClass (TopCat.toSSet.obj (TopCat.of I)) (TopCat.toSSetObj₀Equiv.symm (zPt d)) (1:ℤ)
  have hp (d : Fin (2*p) × Bool) : psi (P d)=Pi.single d (1:ℤ) := by
    rw [hPsi]
    change (Pi.single (TO (TO.symm (d,⟨5/16,by constructor <;> norm_num⟩))).1 (1:ℤ) :
      (Fin (2*p) × Bool) → ℤ) = Pi.single d (1:ℤ)
    rw [TO.apply_symm_apply]
  let mt (b : Bool) : Jm := ⟨if b then 1-(5/16:ℝ) else 5/16,by
    cases b <;> constructor <;> norm_num⟩
  have hIndex (d : Fin (2*p) × Bool) :
      (TM ⟨(zPt d).val,(zPt d).property.2⟩).1=d.1 := by
    have he : (⟨(zPt d).val,(zPt d).property.2⟩ : V)=TM.symm (d.1,mt d.2) := by
      apply Subtype.ext
      change (TO.symm (d,⟨5/16,by constructor <;> norm_num⟩)).val=_
      rw [hTOinv,hTMinv]
    rw [he,TM.apply_symm_apply]
  have hPi (d : Fin (2*p) × Bool) : phi (incV (P d))=Pi.single d.1 (1:ℤ) := by
    let z : V := ⟨(zPt d).val,(zPt d).property.2⟩
    have hm : pointClass (TopCat.toSSet.obj (TopCat.of I))
        (TopCat.toSSetObj₀Equiv.symm (zPt d)) ≫ incV=
      pointClass (TopCat.toSSet.obj (TopCat.of V)) (TopCat.toSSetObj₀Equiv.symm z) := by
      change pointClass _ _ ≫ HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (singularSubsetInclusion X I V inter_subset_right)) RZ) 0=_
      rw [pointClass_map]
      congr 1
    change phi ((pointClass (TopCat.toSSet.obj (TopCat.of I))
      (TopCat.toSSetObj₀Equiv.symm (zPt d)) ≫ incV) (1:ℤ))=_
    rw [hm]
    exact (hPhi z).trans (congrArg (fun i : Fin (2*p) => Pi.single i (1:ℤ)) (hIndex d))
  have hEdge (x : H I 0) (i : Fin (2*p)) :
      phi (incV x) i=psi x (i,false)+psi x (i,true) := by
    let L : (Fin (2*p) × Bool → ℤ) →ₗ[ℤ] ℤ :=
      (LinearMap.proj (R:=ℤ) (φ:=fun _ : Fin (2*p) => ℤ) i).comp
        (phi.toLinearMap.comp (incV.hom.comp psi.symm.toLinearMap))
    let R : (Fin (2*p) × Bool → ℤ) →ₗ[ℤ] ℤ :=
      LinearMap.proj (R:=ℤ) (φ:=fun _ : Fin (2*p) × Bool => ℤ) (i,false)+
        LinearMap.proj (R:=ℤ) (φ:=fun _ : Fin (2*p) × Bool => ℤ) (i,true)
    have hLR : L=R := by
      apply (Pi.basisFun ℤ (Fin (2*p) × Bool)).ext
      intro d
      simp only [Pi.basisFun_apply]
      have hd : psi.symm (Pi.single d (1:ℤ))=P d := by
        apply psi.injective
        rw [psi.apply_symm_apply,hp]
      change phi (incV (psi.symm (Pi.single d (1:ℤ)))) i=
        (Pi.single d (1:ℤ) : Fin (2*p) × Bool → ℤ) (i,false)+
          (Pi.single d (1:ℤ) : Fin (2*p) × Bool → ℤ) (i,true)
      rw [hd,hPi]
      rcases d with ⟨j,b⟩
      cases b <;> by_cases h : j=i <;> simp [h]
    have hh := congrArg (fun f : (Fin (2*p) × Bool → ℤ) →ₗ[ℤ] ℤ => f (psi x)) hLR
    change phi (incV (psi.symm (psi x))) i=psi x (i,false)+psi x (i,true) at hh
    rw [psi.symm_apply_apply] at hh
    exact hh
  have hAug (x : H I 0) : ((TopCat.of I).singularHomology₀ε RZ) x=
      ∑ i : Fin (2*p), (psi x (i,false)+psi x (i,true)) := by
    have hdec : x=∑ d : Fin (2*p) × Bool, (psi x d) • P d := by
      apply psi.injective
      rw [map_sum]
      simp only [map_zsmul,hp]
      have hs (d : Fin (2*p) × Bool) : (psi x d) •
          (Pi.single d (1:ℤ) : Fin (2*p) × Bool → ℤ)=Pi.single d (psi x d) := by
        funext j
        by_cases h : j=d
        · subst j;simp
        · simp [h]
      simp only [hs]
      exact (Finset.univ_sum_single (psi x)).symm
    have ha (d : Fin (2*p) × Bool) : ((TopCat.of I).singularHomology₀ε RZ) (P d)=1 := by
      have hm : pointClass (TopCat.toSSet.obj (TopCat.of I))
          (TopCat.toSSetObj₀Equiv.symm (zPt d)) ≫ ((TopCat.of I).singularHomology₀ε RZ)=𝟙 _ := by
        simp [pointClass,TopCat.singularHomology₀ε,SSet.homology₀ε]
      exact congrArg (fun f : RZ ⟶ RZ => f (1:ℤ)) hm
    calc
      _ = ((TopCat.of I).singularHomology₀ε RZ) (∑ d : Fin (2*p) × Bool, (psi x d) • P d) := congrArg _ hdec
      _ = ∑ d : Fin (2*p) × Bool, psi x d := by
        simp only [map_sum,map_zsmul,ha,smul_eq_mul,mul_one]
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_bool]
        apply Finset.sum_congr rfl
        intro i hi
        exact add_comm _ _
  have hStar (x : H I 0) : u (incU x)=∑ i : Fin (2*p), (psi x (i,false)+psi x (i,true)) := by
    have hn := congrArg (fun f => f x) (augmentation_naturality (singularSubsetInclusion X I U inter_subset_left))
    change u (incU x)=((TopCat.of I).singularHomology₀ε RZ) x at hn
    exact hn.trans (hAug x)
  obtain ⟨D,hD,⟨eD⟩⟩ := source_surviving_graph_incidence_kernel p
  let g := actualMVDifference X U V 0
  have hDiff (x : H I 0) : g x=0 ↔ D (psi x)=0 := by
    rw [show g x=(incU x,-incV x) from actualMVDifference_apply X U V 0 x]
    constructor
    · intro h
      have hs : incU x=0 := congrArg Prod.fst h
      have he : incV x=0 := neg_eq_zero.mp (congrArg Prod.snd h)
      rw [hD]
      apply Prod.ext
      · change (∑ i : Fin (2*p), (psi x (i,false)+psi x (i,true)))=0
        rw [← hStar,hs,map_zero]
      · funext i
        change psi x (i,false)+psi x (i,true)=0
        rw [← hEdge,he,map_zero]
        rfl
    · intro h
      rw [hD] at h
      have hs : incU x=0 := by
        apply u.injective
        rw [hStar,map_zero]
        exact congrArg Prod.fst h
      have he : incV x=0 := by
        apply phi.injective
        funext i
        rw [hEdge]
        simp only [Pi.zero_apply,map_zero]
        exact congrFun (congrArg Prod.snd h) i
      simp [hs,he]
  have hPair : IsZero (ModuleCat.of ℤ (H U 1 × H V 1)) := by
    have hu : IsZero (H U 1) := contractible_positive_homology U 1 (by omega)
    have : Subsingleton (H U 1) := ModuleCat.subsingleton_of_isZero hu
    have : Subsingleton (H V 1) := ModuleCat.subsingleton_of_isZero hV1
    exact ModuleCat.isZero_of_subsingleton _
  let f := actualMVConnecting X U V hU hV hcover 0
  have hfg : f ≫ g=0 := actualMVConnecting_difference X U V hU hV hcover 0
  have ex := actualMV_exact_intersection X U V hU hV hcover 0
  have hSum : actualMVSum X U V 1=0 := hPair.eq_of_src _ _
  have hm : Mono f := (ShortComplex.exact_iff_mono _ hSum).mp (actualMV_exact_ambient X U V hU hV hcover 0)
  have hinj : Function.Injective f := (ModuleCat.mono_iff_injective _).mp hm
  let ef : H (actualSurvivingBoundary p) 1 →ₗ[ℤ] (Fin (2*p) × Bool → ℤ) := psi.toLinearMap.comp f.hom
  have hz (a : H (actualSurvivingBoundary p) 1) : ef a∈LinearMap.ker D := by
    apply LinearMap.mem_ker.mpr
    apply (hDiff (f a)).mp
    exact congrArg (fun m => m a) hfg
  let k : H (actualSurvivingBoundary p) 1 →ₗ[ℤ] LinearMap.ker D := ef.codRestrict _ hz
  let l : H (actualSurvivingBoundary p) 1 →ₗ[ℤ] (Fin (2*p) → ℤ) := eD.toLinearMap.comp k
  have hi : Function.Injective l := by
    intro a b hab
    apply hinj
    apply psi.injective
    change eD (k a)=eD (k b) at hab
    change (k a).val=(k b).val
    exact congrArg Subtype.val (eD.injective hab)
  have hs : Function.Surjective l := by
    intro z
    let q : LinearMap.ker D := eD.symm z
    let b : H I 0 := psi.symm q.val
    have hb : g b=0 := (hDiff b).mpr (by simp [b])
    obtain ⟨a,ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp ex b hb
    refine ⟨a,?_⟩
    change eD (k a)=z
    rw [← eD.apply_symm_apply z]
    apply congrArg eD
    apply Subtype.ext
    change psi (f a)=q.val
    rw [ha]
    simp [b]
  exact ⟨(LinearEquiv.ofBijective l ⟨hi,hs⟩).toModuleIso⟩
end CurveComplex.Hyperbolic.OneBoundaryRay
