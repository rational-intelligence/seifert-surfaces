import A5TransitionInvertibleV466
import A5ChartSignTransportV466

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
universe u
def a5InteriorExtendedChart (S : A5CompactSmoothCarrier.{u}) (p : S) :
    OpenPartialHomeomorph S (Euc 2) where
  toFun := extChartAt (𝓡∂ 2) p
  invFun := (extChartAt (𝓡∂ 2) p).symm
  source := (extChartAt (𝓡∂ 2) p).source ∩
    (extChartAt (𝓡∂ 2) p) ⁻¹' interior (extChartAt (𝓡∂ 2) p).target
  target := interior (extChartAt (𝓡∂ 2) p).target
  map_source' := fun _ h => h.2
  map_target' := by
    intro y hy
    refine ⟨(extChartAt (𝓡∂ 2) p).map_target (interior_subset hy),?_⟩
    change extChartAt (𝓡∂ 2) p ((extChartAt (𝓡∂ 2) p).symm y) ∈
      interior (extChartAt (𝓡∂ 2) p).target
    rw [(extChartAt (𝓡∂ 2) p).right_inv (interior_subset hy)]
    exact hy
  left_inv' := fun _ h => (extChartAt (𝓡∂ 2) p).left_inv h.1
  right_inv' := fun _ h => (extChartAt (𝓡∂ 2) p).right_inv (interior_subset h)
  open_source := isOpen_extChartAt_preimage' p isOpen_interior
  open_target := isOpen_interior
  continuousOn_toFun := (continuousOn_extChartAt p).mono Set.inter_subset_left
  continuousOn_invFun := (continuousOn_extChartAt_symm p).mono interior_subset

def a5EucComplex : Euc 2 ≃L[ℝ] ℂ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans
    ((LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv.trans Complex.equivRealProdCLM.symm)

def a5NativeComplexChart (S : A5CompactSmoothCarrier.{u}) (p : S) :
    OpenPartialHomeomorph S ℂ :=
  (a5InteriorExtendedChart S p).trans a5EucComplex.toHomeomorph.toOpenPartialHomeomorph

theorem a5_native_complex_chart_source (S : A5CompactSmoothCarrier.{u}) (p x : S) :
    x ∈ (a5NativeComplexChart S p).source ↔
      x ∈ (extChartAt (𝓡∂ 2) p).source ∧ (𝓡∂ 2).IsInteriorPoint x := by
  simp only [a5NativeComplexChart,OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ]
  change (x ∈ (extChartAt (𝓡∂ 2) p).source ∧
    extChartAt (𝓡∂ 2) p x ∈ interior (extChartAt (𝓡∂ 2) p).target) ↔ _
  constructor
  · intro hx
    refine ⟨hx.1,?_⟩
    have hs : x ∈ (chartAt (EuclideanHalfSpace 2) p).source := by
      simpa only [extChartAt_source] using hx.1
    exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p) hs).mpr hx.2
  · intro hx
    refine ⟨hx.1,?_⟩
    have hs : x ∈ (chartAt (EuclideanHalfSpace 2) p).source := by
      simpa only [extChartAt_source] using hx.1
    exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p) hs).mp hx.2

#print axioms a5NativeComplexChart
#print axioms a5_native_complex_chart_source

theorem a5_native_transition_derivative (S : A5CompactSmoothCarrier.{u})
    (p q x : S) (hp : x ∈ (extChartAt (𝓡∂ 2) p).source)
    (hq : x ∈ (extChartAt (𝓡∂ 2) q).source) (hi : (𝓡∂ 2).IsInteriorPoint x) :
    ∃ A : Euc 2 ≃L[ℝ] Euc 2,
      HasFDerivAt ((extChartAt (𝓡∂ 2) q) ∘ (extChartAt (𝓡∂ 2) p).symm)
        A.toContinuousLinearMap (extChartAt (𝓡∂ 2) p x) ∧
      LinearMap.det A.toLinearEquiv.toLinearMap =
        (a5TransitionJacobian S p q x).det := by
  let cp := extChartAt (𝓡∂ 2) p
  let cq := extChartAt (𝓡∂ 2) q
  let y := cp x
  have ht : y ∈ cp.target := cp.map_source hp
  have hint : y ∈ interior cp.target := by
    have hsp : x ∈ (chartAt (EuclideanHalfSpace 2) p).source := by
      simpa only [extChartAt_source] using hp
    exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p) hsp).mp hi
  have hnhds : cp.target ∈ nhds y := mem_interior_iff_mem_nhds.mp hint
  have hdu : UniqueMDiffWithinAt 𝓘(ℝ,Euc 2) cp.target y :=
    (uniqueDiffOn_extChartAt_target p y ht).uniqueMDiffWithinAt
  have hd := (mdifferentiableWithinAt_extChartAt_symm ht).mfderivWithin_mono hdu
    (extChartAt_target_subset_range p)
  have hBInv : (mfderivWithin 𝓘(ℝ,Euc 2) (𝓡∂ 2) cp.symm cp.target y).IsInvertible := by
    rw [hd]
    exact isInvertible_mfderivWithin_extChartAt_symm ht
  obtain ⟨B,hB⟩ := hBInv
  obtain ⟨D,hD⟩ := isInvertible_mfderiv_extChartAt hq
  let A : Euc 2 ≃L[ℝ] Euc 2 := B.trans D
  have hBs : MDifferentiableWithinAt 𝓘(ℝ,Euc 2) (𝓡∂ 2) cp.symm cp.target y :=
    mdifferentiableOn_extChartAt_symm y ht
  have hDs : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ,Euc 2) cq x := by
    apply mdifferentiableAt_extChartAt
    simpa only [extChartAt_source] using hq
  have hDc : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ,Euc 2) cq (cp.symm y) := by
    rwa [cp.left_inv hp]
  have hchain := hDc.hasMFDerivAt.comp y (hBs.hasMFDerivWithinAt.hasMFDerivAt hnhds)
  have hder : HasFDerivAt (cq ∘ cp.symm) A.toContinuousLinearMap y := by
    have hc := hchain.hasFDerivAt
    rw [cp.left_inv hp,← hB,← hD] at hc
    exact hc
  refine ⟨A,hder,?_⟩
  have hfwithin : fderivWithin ℝ (cq ∘ cp.symm) cp.target y=A.toContinuousLinearMap :=
    hder.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_extChartAt_target p y ht)
  have hm : LinearMap.det A.toLinearEquiv.toLinearMap =
      Matrix.det (show Matrix (Fin 2) (Fin 2) ℝ from
        fun i j => fderivWithin ℝ (cq ∘ cp.symm) cp.target y
          (EuclideanSpace.single j 1) i) := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
    congr 1
    ext i j
    simp only [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
    rw [hfwithin]
    rw [show (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis j=EuclideanSpace.single j 1 from
      EuclideanSpace.basisFun_apply _ _ _]
    rfl
  exact hm
def a5ShiftChart {X : Type u} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) : OpenPartialHomeomorph X ℂ :=
  e.trans (Homeomorph.addRight (-e x)).toOpenPartialHomeomorph

theorem a5_shift_chart_source {X : Type u} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) : (a5ShiftChart e x).source=e.source := by
  simp [a5ShiftChart,OpenPartialHomeomorph.trans_source]

theorem a5_shift_chart_apply {X : Type u} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x y : X) : a5ShiftChart e x y=e y-e x := by
  rfl

theorem a5_shift_chart_symm_apply {X : Type u} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (x : X) (z : ℂ) :
    (a5ShiftChart e x).symm z=e.symm (z+e x) := by
  simp [a5ShiftChart,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_apply,Homeomorph.addRight_symm]

theorem a5_native_complex_transition_derivative (S : A5CompactSmoothCarrier.{u})
    (p q x : S) (hp : x ∈ (a5NativeComplexChart S p).source)
    (hq : x ∈ (a5NativeComplexChart S q).source) :
    let e := a5NativeComplexChart S p
    let f := a5NativeComplexChart S q
    let transitionMap := (a5ShiftChart e x).symm.trans (a5ShiftChart f x)
    ∃ A : ℂ ≃L[ℝ] ℂ, transitionMap 0=0 ∧ HasFDerivAt transitionMap A.toContinuousLinearMap 0 ∧
      LinearMap.det A.toLinearEquiv.toLinearMap =
        (a5TransitionJacobian S p q x).det := by
  let e := a5NativeComplexChart S p
  let f := a5NativeComplexChart S q
  let transitionMap := (a5ShiftChart e x).symm.trans (a5ShiftChart f x)
  obtain ⟨hps,hi⟩ := (a5_native_complex_chart_source S p x).mp hp
  obtain ⟨hqs,_⟩ := (a5_native_complex_chart_source S q x).mp hq
  obtain ⟨D,hD,hdet⟩ := a5_native_transition_derivative S p q x hps hqs hi
  let A : ℂ ≃L[ℝ] ℂ := (a5EucComplex.symm.trans D).trans a5EucComplex
  let cp := extChartAt (𝓡∂ 2) p
  let cq := extChartAt (𝓡∂ 2) q
  let g : ℂ → Euc 2 := fun z => a5EucComplex.symm (z+a5EucComplex (cp x))
  have hg : HasFDerivAt g a5EucComplex.symm.toContinuousLinearMap 0 :=
    a5EucComplex.symm.hasFDerivAt.comp 0 ((hasFDerivAt_id (0:ℂ)).add_const _)
  have hg0 : g 0=cp x := by simp [g]
  have hDg : HasFDerivAt (cq ∘ cp.symm) D.toContinuousLinearMap (g 0) := by
    rwa [hg0]
  have hcomplex := (a5EucComplex.hasFDerivAt.comp 0 (hDg.comp 0 hg)).sub_const (f x)
  have htransition : (fun z : ℂ => a5EucComplex ((cq ∘ cp.symm) (g z))-f x)=transitionMap := by
    funext z
    simp only [transitionMap,OpenPartialHomeomorph.trans_apply,a5_shift_chart_apply,
      a5_shift_chart_symm_apply]
    rfl
  have hzero : transitionMap 0=0 := by
    simp only [transitionMap,OpenPartialHomeomorph.trans_apply,a5_shift_chart_apply,
      a5_shift_chart_symm_apply,zero_add,e.left_inv hp,sub_self]
  refine ⟨A,hzero,?_,?_⟩
  · rw [← htransition]
    exact hcomplex
  · have hc : LinearMap.det A.toLinearEquiv.toLinearMap=
        LinearMap.det D.toLinearEquiv.toLinearMap := by
      exact LinearMap.det_conj D.toLinearEquiv.toLinearMap a5EucComplex.toLinearEquiv
    exact hc.trans hdet

#print axioms a5_native_complex_transition_derivative
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
