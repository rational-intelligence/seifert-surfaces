import B1TangencyGraph
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric

set_option maxHeartbeats 8000000
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.CollarMetricExtensions
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates

universe v u
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

/-- The original collar's literal within-derivative pullback coefficients. -/
def actualCollarCoefficients (D : B1OriginalData g J) (s : Circle) (R : ℝ) :
    MetricTensor := fun y i j =>
  g.inner (localCollar D s y)
    (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (localCollar D s) (collarDomain D R) y
      ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 i)))
    (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (localCollar D s) (collarDomain D R) y
      ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 j)))

/-- G01. Local Euclidean coefficient extensions of the SAME original collar;
no manifold-valued extension through its boundary is asserted. -/
theorem actual_collar_local_positive_coefficient_extension
    (D : B1OriginalData g J) (s : Circle) (R : ℝ)
    (hR : 0 < R) (hRradial : R < D.r0) (hRcircle : 4 * R < D.leafLength)
    (K0 : Set E3) (hKcompact : IsCompact K0)
    (hKdomain : K0 ⊆ collarDomain D R)
    (hKradial : ∀ y ∈ K0, y 1 < D.r0) :
    ∀ y ∈ K0, ∃ O : Set E3, IsOpen O ∧ y ∈ O ∧
      ∃ M : CoordinateMetric O,
        ∀ z ∈ O ∩ collarDomain D R, M.tensor z = actualCollarCoefficients D s R z := by
  classical
  let C := collarDomain D R
  let pre : E3 → Circle × (ℝ × ℝ) := fun y => (localCircle D s (y 0), y 1, y 2)
  have hpre : ContMDiff 𝓘(ℝ, E3) ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) ∞ pre := by
    have h0 : ContDiff ℝ ∞ (fun y : E3 => y 0) := (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) 0).contDiff
    have h1 : ContDiff ℝ ∞ (fun y : E3 => y 1) := (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) 1).contDiff
    have h2 : ContDiff ℝ ∞ (fun y : E3 => y 2) := (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) 2).contDiff
    exact (contMDiff_const.mul (contMDiff_circleExp.comp
      (((contDiff_const.mul h0).div_const D.leafLength).contMDiff))).prodMk
      (h1.contMDiff.prodMk h2.contMDiff)
  have hmaps : MapsTo pre C (halfCylinder D.r0 D.eta) := by
    intro y hy
    exact ⟨hy.2.1, hy.2.2⟩
  have hcollar : ContMDiffOn 𝓘(ℝ, E3) (𝓡∂ 3) ∞ (localCollar D s) C :=
    D.collar_smooth.comp hpre.contMDiffOn hmaps
  have huniq : UniqueMDiffOn 𝓘(ℝ, E3) C := by
    let B : Set E3 := {y | y 1 ∈ Icc (0 : ℝ) D.r0}
    let A : Set E3 := {y | |y 0| < 2 * R ∧ |y 2| < D.eta}
    have hBconvex : Convex ℝ B :=
      (convex_Icc (0 : ℝ) D.r0).linear_preimage
        (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) 1).toLinearMap
    have hBinterior : (interior B).Nonempty := by
      let p : E3 := EuclideanSpace.single 1 (D.r0 / 2)
      refine ⟨p, mem_interior_iff_mem_nhds.mpr ?_⟩
      have ho : IsOpen {y : E3 | 0 < y 1 ∧ y 1 < D.r0} :=
        (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 1)).inter
          (isOpen_lt (PiLp.continuous_apply 2 _ 1) continuous_const)
      have hp : p ∈ {y : E3 | 0 < y 1 ∧ y 1 < D.r0} := by
        simpa [p, EuclideanSpace.single] using D.r0_pos
      exact Filter.mem_of_superset (ho.mem_nhds hp) (fun y hy => ⟨hy.1.le, hy.2.le⟩)
    have hAopen : IsOpen A :=
      (isOpen_lt (PiLp.continuous_apply 2 _ 0).abs continuous_const).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ 2).abs continuous_const)
    have hCeq : C = B ∩ A := by ext y; simp [C, collarDomain, B, A]; tauto
    rw [hCeq]
    exact ((uniqueDiffOn_convex hBconvex hBinterior).inter hAopen).uniqueMDiffOn
  have hvec (i : Fin 3) : ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, E3)).tangent ∞
      (fun y => (⟨y, (NormedSpace.fromTangentSpace y).symm (coordinateVector 3 i)⟩ :
        TangentBundle 𝓘(ℝ, E3) E3)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    exact contDiff_const
  have htan (i : Fin 3) : ContMDiffOn 𝓘(ℝ, E3) (𝓡∂ 3).tangent ∞
      (fun y => (⟨localCollar D s y,
        mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (localCollar D s) C y
          ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 i))⟩ :
          TangentBundle (𝓡∂ 3) E.Carrier)) C :=
    (hcollar.contMDiffOn_tangentMapWithin (m := ∞) (by simp) huniq).comp
      (hvec i).contMDiffOn (fun y hy => hy)
  have hcoeff (i j : Fin 3) : ContDiffOn ℝ ∞
      (fun y => actualCollarCoefficients D s R y i j) C := by
    have hg := g.contMDiff.comp_contMDiffOn hcollar
    have happ := hg.clm_bundle_apply₂ (F₁ := Euc 3) (F₂ := Euc 3) (F₃ := ℝ)
      (E₃ := Bundle.Trivial E.Carrier ℝ) (ψ := fun y => g.inner (localCollar D s y))
      (htan i) (htan j)
    intro y hy
    have hscalar := (Bundle.contMDiffWithinAt_totalSpace.mp (happ y hy)).2
    simpa [actualCollarCoefficients, C] using hscalar.contDiffWithinAt
  have hprerank (y : E3) : Function.Injective
      (mfderiv 𝓘(ℝ, E3) ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) pre y) := by
    let P0 := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) 0
    let P1 := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) 1
    let P2 := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) 2
    let gamma : ℝ → ℂ := fun t => (localCircle D s t : ℂ)
    let c : ℂ := (s : ℂ) *
      (Complex.exp ((2 * Real.pi * (y 0) / D.leafLength : ℝ) * Complex.I) *
        ((2 * Real.pi / D.leafLength : ℝ) * Complex.I))
    have hgam : HasDerivAt gamma c (y 0) := by
      simpa [gamma, c, localCircle, Circle.coe_mul, Circle.coe_exp] using
        (((((hasDerivAt_id (y 0)).const_mul (2 * Real.pi)).div_const D.leafLength
          ).ofReal_comp.mul_const Complex.I).cexp.const_mul (s : ℂ))
    have hc : c ≠ 0 := by
      dsimp [c]
      apply mul_ne_zero (Circle.coe_ne_zero s)
      apply mul_ne_zero (Complex.exp_ne_zero _)
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
        (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) D.leafLength_pos.ne'))
        Complex.I_ne_zero
    let post : Circle × (ℝ × ℝ) → ℂ := fun p => (p.1 : ℂ)
    letI : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
    have hpost : ContMDiff ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ, ℂ) ∞ post :=
      (contMDiff_coe_sphere (E := ℂ) (n := 1)).comp contMDiff_fst
    have hf : HasFDerivAt (post ∘ pre)
        (ContinuousLinearMap.toSpanSingleton ℝ c ∘L P0) y :=
      hgam.hasFDerivAt.comp y P0.hasFDerivAt
    have hchain := mfderiv_comp y
      (hpost.mdifferentiable (by simp) (pre y)) (hpre.mdifferentiable (by simp) y)
    rw [hf.hasMFDerivAt.mfderiv] at hchain
    have hpost1 : ContMDiff ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ) ∞
        (fun p : Circle × (ℝ × ℝ) => p.2.1) := contMDiff_fst.comp contMDiff_snd
    have hpost2 : ContMDiff ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ) ∞
        (fun p : Circle × (ℝ × ℝ) => p.2.2) := contMDiff_snd.comp contMDiff_snd
    have hchain1 := mfderiv_comp y
      (hpost1.mdifferentiable (by simp) (pre y)) (hpre.mdifferentiable (by simp) y)
    have hchain2 := mfderiv_comp y
      (hpost2.mdifferentiable (by simp) (pre y)) (hpre.mdifferentiable (by simp) y)
    have hmf1 : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ)
        ((fun p : Circle × (ℝ × ℝ) => p.2.1) ∘ pre) y = P1 :=
      P1.hasFDerivAt.hasMFDerivAt.mfderiv
    have hmf2 : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ)
        ((fun p : Circle × (ℝ × ℝ) => p.2.2) ∘ pre) y = P2 :=
      P2.hasFDerivAt.hasMFDerivAt.mfderiv
    rw [hmf1] at hchain1
    rw [hmf2] at hchain2
    intro u v huv
    change E3 at u v
    have h0 : u 0 = v 0 := by
      have h := congrArg (mfderiv ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ, ℂ) post (pre y)) huv
      have hu := congrArg (fun L => L u) hchain
      have hv := congrArg (fun L => L v) hchain
      change (u 0 : ℝ) • c = _ at hu
      change (v 0 : ℝ) • c = _ at hv
      exact (smul_left_injective ℝ hc) (hu.trans (h.trans hv.symm))
    have h1 : u 1 = v 1 := by
      have h := congrArg (mfderiv ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ)
        (fun p : Circle × (ℝ × ℝ) => p.2.1) (pre y)) huv
      exact (congrArg (fun L => L u) hchain1).trans
        (h.trans (congrArg (fun L => L v) hchain1).symm)
    have h2 : u 2 = v 2 := by
      have h := congrArg (mfderiv ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) 𝓘(ℝ)
        (fun p : Circle × (ℝ × ℝ) => p.2.2) (pre y)) huv
      exact (congrArg (fun L => L u) hchain2).trans
        (h.trans (congrArg (fun L => L v) hchain2).symm)
    change (u : E3) = (v : E3)
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

  have hrank : ∀ y ∈ C, Function.Injective
      (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (localCollar D s) C y) := by
    intro y hy
    have hchain := mfderivWithin_comp y
      (D.collar_smooth.mdifferentiableOn (by simp) (pre y) (hmaps hy))
      ((hpre.mdifferentiable (by simp) y).mdifferentiableWithinAt) hmaps (huniq y hy)
    change mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (localCollar D s) C y = _ at hchain
    rw [hchain, mfderivWithin_eq_mfderiv (huniq y hy) (hpre.mdifferentiable (by simp) y)]
    exact (D.collar_immersion (pre y) (hmaps hy)).comp (hprerank y)

  have hsymm : ∀ y ∈ C, ∀ i j : Fin 3,
      actualCollarCoefficients D s R y i j = actualCollarCoefficients D s R y j i := by
    intro y hy i j
    exact g.symm _ _ _
  have hpositive : ∀ y ∈ C, ∀ v : E3, v ≠ 0 →
      0 < coordinateInner (actualCollarCoefficients D s R) y v v := by
    intro y hy v hv
    let d := (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (localCollar D s) C y) ∘L
      (NormedSpace.fromTangentSpace y).symm.toContinuousLinearMap
    have hvsum : v = ∑ i : Fin 3, v i • coordinateVector 3 i := by
      ext j
      simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
    have hquad : coordinateInner (actualCollarCoefficients D s R) y v v =
        g.inner (localCollar D s y) (d v) (d v) := by
      conv_rhs => rw [hvsum]
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        map_sum, map_smul, smul_eq_mul, coordinateInner, actualCollarCoefficients, d, C,
        ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [g.symm _ _ _]
      ring
    rw [hquad]
    apply g.pos
    exact fun h => hv (((hrank y hy).comp (NormedSpace.fromTangentSpace y).symm.injective)
      (by simpa [d] using h))
  let e : E3 ≃L[ℝ] ℝ × (ℝ × ℝ) :=
    { toFun := fun y => (y 1, y 0, y 2)
      invFun := fun p => (EuclideanSpace.equiv (Fin 3) ℝ).symm ![p.2.1, p.1, p.2.2]
      left_inv := by intro y; ext i; fin_cases i <;> rfl
      right_inv := by intro p; rcases p with ⟨a,b,c⟩; rfl
      map_add' := by intro y z; rfl
      map_smul' := by intro c y; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let P : Set (ℝ × ℝ) := {p | |p.1| < 2 * R ∧ |p.2| < D.eta}
  have hP : IsOpen P :=
    (isOpen_lt continuous_fst.abs continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)
  let F : E3 → Fin 3 → Fin 3 → ℝ := actualCollarCoefficients D s R
  have hG : ContDiffOn ℝ ∞ F C :=
    contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (hcoeff i))
  have hpull : ContDiffOn ℝ ∞
      (F ∘ e.symm) (Icc (0 : ℝ) D.r0 ×ˢ P) :=
    hG.comp e.symm.contDiff.contDiffOn (by
      intro p hp
      exact ⟨hp.2.1,hp.1,hp.2.2⟩)
  intro y hy
  have hyC : y ∈ C := hKdomain hy
  have hyP : (e y).2 ∈ P := ⟨hyC.1,hyC.2.2⟩
  obtain ⟨ext, V, hV, hsmooth, hagree⟩ :=
    DifferentialGeometry.Analysis.borel_interval_extend_param
      (fun t p => F (e.symm (t,p))) D.r0 D.r0_pos
      P (e y).2 (by rwa [hP.interior_eq]) hpull
  let O0 : Set E3 := e ⁻¹' (univ ×ˢ interior V)
  have hO0 : IsOpen O0 := (isOpen_univ.prod isOpen_interior).preimage e.continuous
  have hyO0 : y ∈ O0 := ⟨mem_univ _, mem_interior_iff_mem_nhds.mpr hV⟩
  let H : MetricTensor := fun z i j => (ext (e z).1 (e z).2 i j + ext (e z).1 (e z).2 j i) / 2
  have hHsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) O0 := by
    have h0 : ContDiffOn ℝ ∞ (fun z => ext (e z).1 (e z).2) O0 :=
      hsmooth.comp e.contDiff.contDiffOn (by intro z hz; exact ⟨hz.1, interior_subset hz.2⟩)
    intro i j
    exact ((contDiffOn_pi.mp (contDiffOn_pi.mp h0 i) j).add
      (contDiffOn_pi.mp (contDiffOn_pi.mp h0 j) i)).div_const 2
  have hHsymm : ∀ z, ∀ i j, H z i j = H z j i := by
    intro z i j
    dsimp [H]
    rw [add_comm]
  have hHagree : ∀ z ∈ O0 ∩ C, H z = actualCollarCoefficients D s R z := by
    intro z hz
    have heq := hagree (e z).1 hz.2.2.1 (e z).2 (interior_subset hz.1.2)
    simp only [e.symm_apply_apply] at heq
    ext i j
    change (ext (e z).1 (e z).2 i j + ext (e z).1 (e z).2 j i) / 2 = _
    rw [heq]
    change (actualCollarCoefficients D s R z i j + actualCollarCoefficients D s R z j i) / 2 = _
    rw [hsymm z hz.2 j i]
    ring

  let Q : E3 × E3 → ℝ := fun p => coordinateInner H p.1 p.2 p.2
  have hQ : ContinuousOn Q (O0 ×ˢ univ) := by
    apply continuousOn_finset_sum
    intro i hi
    apply continuousOn_finset_sum
    intro j hj
    exact (((hHsmooth i j).continuousOn.comp continuous_fst.continuousOn
      (fun p hp => hp.1)).mul
      ((PiLp.continuous_apply 2 _ i).comp continuous_snd).continuousOn).mul
      ((PiLp.continuous_apply 2 _ j).comp continuous_snd).continuousOn
  have hN : IsOpen ((O0 ×ˢ univ) ∩ Q ⁻¹' Ioi 0) :=
    hQ.isOpen_inter_preimage (hO0.prod isOpen_univ) isOpen_Ioi
  have htube : ({y} : Set E3) ×ˢ Metric.sphere (0 : E3) 1 ⊆
      (O0 ×ˢ univ) ∩ Q ⁻¹' Ioi 0 := by
    rintro ⟨z,v⟩ ⟨hz,hv⟩
    have hz : z = y := hz
    subst z
    refine ⟨⟨hyO0,mem_univ _⟩,?_⟩
    have h0 : v ≠ 0 := by
      intro h0
      simp [h0, Metric.mem_sphere] at hv
    have heq : H y = actualCollarCoefficients D s R y := hHagree y ⟨hyO0,hyC⟩
    change 0 < coordinateInner H y v v
    simpa only [coordinateInner, heq] using hpositive y hyC v h0
  obtain ⟨O,Vunit,hO,hVunit,hyO,hunit,hprod⟩ := generalized_tube_lemma
    (isCompact_singleton (x := y)) (isCompact_sphere (0 : E3) 1) hN htube
  have hposO : ∀ z ∈ O, ∀ v : E3, v ≠ 0 → 0 < coordinateInner H z v v := by
    intro z hz v hv
    let w : E3 := ‖v‖⁻¹ • v
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hw : w ∈ Metric.sphere (0 : E3) 1 := by
      simp [w, Metric.mem_sphere, dist_zero_right, norm_smul, abs_of_pos hn,
        abs_of_pos (inv_pos.mpr hn), hn.ne']
    have hwV : w ∈ Vunit := hunit hw
    have hpair : (z,w) ∈ O ×ˢ Vunit := ⟨hz,hwV⟩
    have hp := hprod hpair
    have hp : 0 < coordinateInner H z w w := hp.2
    have hscale : coordinateInner H z w w = ‖v‖⁻¹ ^ 2 * coordinateInner H z v v := by
      simp only [w, coordinateInner, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hscale] at hp
    exact (mul_pos_iff.mp hp).resolve_right (fun h => (sq_nonneg ‖v‖⁻¹).not_gt h.1) |>.2
  let O1 := O ∩ O0
  refine ⟨O1, hO.inter hO0, ⟨hyO (mem_singleton y),hyO0⟩, ?_⟩
  refine ⟨{ tensor := H
            smooth := fun i j => (hHsmooth i j).mono inter_subset_right
            symmetric := fun z hz i j => hHsymm z i j
            positive := fun z hz v hv => hposO z hz.1 v hv }, ?_⟩
  intro z hz
  exact hHagree z ⟨hz.1.2,hz.2⟩


/-- A finite weighted sum of the supplied patch coefficients, on all E3.
Subordinate weights make every weighted term vanish off its own patch. -/
def finiteWeightedTensor {ι : Type u} (O : ι → Set E3)
    (M : ∀ i, CoordinateMetric (O i)) {n : ℕ} (selected : Fin n → ι)
    {V : Set E3} (ρ : SmoothPartitionOfUnity (Fin n) 𝓘(ℝ, E3) E3 (closure V)) :
    MetricTensor := fun y a b => ∑ k : Fin n, ρ k y * (M (selected k)).tensor y a b

/-- G02. Compact finite gluing of the genuine supplied local metrics. The
output tensor is literally their finite weighted sum and equals G on ALL V∩C. -/
theorem finite_positive_coefficient_gluing {ι : Type u}
    (K0 C : Set E3) (hKcompact : IsCompact K0) (hKC : K0 ⊆ C)
    (G : MetricTensor) (O : ι → Set E3) (hO : ∀ i, IsOpen (O i))
    (M : ∀ i, CoordinateMetric (O i)) (hcover : K0 ⊆ ⋃ i, O i)
    (hsame : ∀ i, ∀ y ∈ O i ∩ C, (M i).tensor y = G y) :
    ∃ n : ℕ, ∃ selected : Fin n → ι, ∃ V : Set E3,
      IsOpen V ∧ K0 ⊆ V ∧ closure V ⊆ ⋃ k : Fin n, O (selected k) ∧
      ∃ ρ : SmoothPartitionOfUnity (Fin n) 𝓘(ℝ, E3) E3 (closure V),
        ρ.IsSubordinate (fun k => O (selected k)) ∧
        ∃ glued : CoordinateMetric V,
          glued.tensor = finiteWeightedTensor O M selected ρ ∧
          ∀ y ∈ V ∩ C, glued.tensor y = G y := by
  classical
  obtain ⟨t, ht⟩ := hKcompact.elim_finite_subcover O hO hcover
  let selected : Fin t.card → ι := fun k => (t.equivFin.symm k).val
  have hfinitecover : K0 ⊆ ⋃ k : Fin t.card, O (selected k) := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (ht hy)
    refine mem_iUnion.mpr ⟨t.equivFin ⟨i, hi⟩, ?_⟩
    simpa [selected] using hyi
  obtain ⟨V, hV, hKV, hclosure⟩ := normal_exists_closure_subset
    hKcompact.isClosed (isOpen_iUnion (fun k => hO (selected k))) hfinitecover
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, E3) isClosed_closure (fun k => O (selected k))
    (fun k => hO (selected k)) hclosure
  have hpatch : ∀ k y, ρ k y ≠ 0 → y ∈ O (selected k) := by
    intro k y h
    exact hρ k (subset_tsupport _ h)
  have hsmooth : ∀ a b, ContDiffOn ℝ ∞
      (fun y => finiteWeightedTensor O M selected ρ y a b) V := by
    intro a b y hy
    have h := ρ.contDiffAt_finsum (n := ⊤) (x₀ := y)
      (g := fun k z => (M (selected k)).tensor z a b)
      (fun k hk => ((M (selected k)).smooth a b).contDiffAt
        ((hO (selected k)).mem_nhds (hρ k hk)))
    change ContDiffWithinAt ℝ ∞ (fun z => ∑ k, ρ k z * (M (selected k)).tensor z a b) V y
    simpa only [finsum_eq_sum_of_fintype, smul_eq_mul] using
      h.contDiffWithinAt
  have hsym : ∀ y ∈ V, ∀ a b,
      finiteWeightedTensor O M selected ρ y a b =
        finiteWeightedTensor O M selected ρ y b a := by
    intro y hy a b
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hz : ρ k y = 0
    · simp only [hz, zero_mul]
    · rw [(M (selected k)).symmetric y (hpatch k y hz) a b]
  have hinner : ∀ y v, coordinateInner (finiteWeightedTensor O M selected ρ) y v v =
      ∑ k : Fin t.card, ρ k y * coordinateInner (M (selected k)).tensor y v v := by
    intro y v
    change (∑ a, ∑ b, (∑ k, ρ k y * (M (selected k)).tensor y a b) * v a * v b) =
      ∑ k, ρ k y * ∑ a, ∑ b, (M (selected k)).tensor y a b * v a * v b
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hpos : ∀ y ∈ V, ∀ v : E3, v ≠ 0 →
      0 < coordinateInner (finiteWeightedTensor O M selected ρ) y v v := by
    intro y hy v hv
    rw [hinner]
    apply Finset.sum_pos'
    · intro k hk
      by_cases hz : ρ k y = 0
      · rw [hz, zero_mul]
      · exact mul_nonneg (ρ.nonneg k y)
          ((M (selected k)).positive y (hpatch k y hz) v hv).le
    · obtain ⟨k, hk⟩ := ρ.exists_pos_of_mem (subset_closure hy)
      exact ⟨k, Finset.mem_univ _, mul_pos hk
        ((M (selected k)).positive y (hpatch k y (ne_of_gt hk)) v hv)⟩
  let glued : CoordinateMetric V :=
    ⟨finiteWeightedTensor O M selected ρ, hsmooth, hsym, hpos⟩
  refine ⟨t.card, selected, V, hV, hKV, hclosure, ρ, hρ, glued, rfl, ?_⟩
  intro y hy
  funext a b
  change (∑ k : Fin t.card, ρ k y * (M (selected k)).tensor y a b) = G y a b
  calc
    _ = ∑ k : Fin t.card, ρ k y * G y a b := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hz : ρ k y = 0
      · simp only [hz, zero_mul]
      · rw [hsame (selected k) y ⟨hpatch k y hz, hy.2⟩]
    _ = (∑ k : Fin t.card, ρ k y) * G y a b := (Finset.sum_mul ..).symm
    _ = G y a b := by
      have hsum := ρ.sum_eq_one (subset_closure hy.1)
      rw [finsum_eq_sum_of_fintype] at hsum
      rw [hsum, one_mul]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.CollarMetricExtensions
