import B1ActualCollarTopology_v475
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Rank of the literal original collar within its actual half-domain. -/
theorem actual_localCollar_within_injective_v475
    (D : B1OriginalData g J) (s : Circle) (R : ℝ) :
    ∀ y ∈ collarDomain D R, Function.Injective
      (mfderivWithin 𝓘(ℝ,E3) (𝓡∂ 3) (localCollar D s) (collarDomain D R) y) := by
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

  exact hrank

/-- The same supplied collar admits a smooth ambient inverse on every
interior subpatch. It is constructed through the actual exterior inclusion
and the inverse function theorem, rather than assumed as extra B1 data. -/
theorem actual_interior_collar_partialDiffeomorph_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (O : Set E3) (hO : IsOpen O) (hOC : O ⊆ collarDomain D W.R)
    (x : E3) (hx : x ∈ O) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ,E3) (𝓡 3) E3 ThreeSphere ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ O ∧
      EqOn (E.toSphere ∘ localCollar D s) Φ Φ.source := by
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  let F : E3 → ThreeSphere := E.toSphere ∘ localCollar D s
  have hF : ContMDiffOn 𝓘(ℝ,E3) (𝓡 3) ∞ F O :=
    hinc.contMDiff.comp_contMDiffOn ((actual_localCollar_smooth_v475 D s W.R).mono hOC)
  have hinv : ∀ y ∈ O,
      (fderiv ℝ (writtenInExtChartAt 𝓘(ℝ,E3) (𝓡 3) y F)
        (extChartAt 𝓘(ℝ,E3) y y)).IsInvertible := by
    intro y hy
    have hCnhds : collarDomain D W.R ∈ 𝓝 y :=
      Filter.mem_of_superset (hO.mem_nhds hy) hOC
    have hcollar : MDifferentiableAt 𝓘(ℝ,E3) (𝓡∂ 3) (localCollar D s) y :=
      ((actual_localCollar_smooth_v475 D s W.R).contMDiffAt hCnhds).mdifferentiableAt (by simp)
    have hcollarinj : Injective (mfderiv 𝓘(ℝ,E3) (𝓡∂ 3) (localCollar D s) y) := by
      have h := actual_localCollar_within_injective_v475 D s W.R y (hOC hy)
      rwa [mfderivWithin_of_mem_nhds hCnhds] at h
    have hrank : Injective (mfderiv 𝓘(ℝ,E3) (𝓡 3) F y) := by
      dsimp only [F]
      rw [mfderiv_comp y (hinc.contMDiff.mdifferentiableAt (by simp)) hcollar]
      exact ((hinc.isImmersion.isImmersionAt _).mfderiv_injective (by simp)).comp hcollarinj
    let L : E3 →L[ℝ] E3 := mfderiv 𝓘(ℝ,E3) (𝓡 3) F y
    let e : E3 ≃ₗ[ℝ] E3 := L.toLinearMap.linearEquivOfInjective hrank rfl
    have hLinvertible : L.IsInvertible := by
      let eL : E3 ≃L[ℝ] E3 := {
        toLinearEquiv := e
        continuous_toFun := L.continuous
        continuous_invFun := e.symm.toLinearMap.continuous_of_finiteDimensional }
      exact ⟨eL,rfl⟩
    have hmdiff := (hF.contMDiffAt (hO.mem_nhds hy)).mdifferentiableAt (by simp)
    have hderiv : fderiv ℝ (writtenInExtChartAt 𝓘(ℝ,E3) (𝓡 3) y F)
        (extChartAt 𝓘(ℝ,E3) y y) = mfderiv 𝓘(ℝ,E3) (𝓡 3) F y := by
      rw [hmdiff.mfderiv_abuse, ModelWithCorners.Boundaryless.range_eq_univ,
        fderivWithin_univ]
    rw [hderiv]
    exact hLinvertible
  exact DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty
    hO hx hF hinv

#print axioms actual_localCollar_within_injective_v475
#print axioms actual_interior_collar_partialDiffeomorph_v475

/-- Injective local smooth inverses glue to the literal original collar on
the entire chosen open interior domain. This covers a whole compact graph
support by one ambient coordinate map. -/
theorem actual_interior_collar_global_partialDiffeomorph_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (O : Set E3) (hO : IsOpen O) (hOC : O ⊆ collarDomain D W.R) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ,E3) (𝓡 3) E3 ThreeSphere ∞,
      Φ.source = O ∧ Φ.target = (E.toSphere ∘ localCollar D s) '' O ∧
      (Φ : E3 → ThreeSphere) = E.toSphere ∘ localCollar D s := by
  classical
  let F : E3 → ThreeSphere := E.toSphere ∘ localCollar D s
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hinj : InjOn F O := hinc.isEmbedding.injective.injOn.comp
    ((actual_localCollar_injective_v475 D s W).mono hOC) (mapsTo_univ _ _)
  let e := hinj.toPartialEquiv F O
  have hopen : IsOpen (F '' O) := by
    let f : O → ThreeSphere := fun y => F y
    have hf : Continuous f :=
      (hinc.contMDiff.comp_contMDiffOn
        ((actual_localCollar_smooth_v475 D s W.R).mono hOC)).continuousOn.domRestrict
    have hi : Injective f := fun y z he => Subtype.ext (hinj y.property z.property he)
    have hh := DifferentialGeometry.Topology.isOpen_range_of_isOpen_of_continuous_injective_real
      (𝓡 3) hO f hf hi
    have heq : range f = F '' O := by
      ext p
      constructor
      · rintro ⟨y,rfl⟩
        exact ⟨y,y.property,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨⟨y,hy⟩,rfl⟩
    rwa [heq] at hh
  have hinverse : ContMDiffOn (𝓡 3) 𝓘(ℝ,E3) ∞ e.symm e.target := by
    rintro p ⟨y,hy,rfl⟩
    obtain ⟨Ψ,hyΨ,hΨO,heqΨ⟩ := actual_interior_collar_partialDiffeomorph_v475
      D s W O hO hOC y hy
    have hFy : F y ∈ Ψ.target := by
      change (E.toSphere ∘ localCollar D s) y ∈ Ψ.target
      rw [heqΨ hyΨ]
      exact Ψ.toPartialEquiv.map_source hyΨ
    have heq : e.symm =ᶠ[𝓝 (F y)] (Ψ.symm : ThreeSphere → E3) := by
      filter_upwards [Ψ.open_target.mem_nhds hFy] with q hq
      have hqΨ : Ψ.symm q ∈ Ψ.source := Ψ.toPartialEquiv.map_target hq
      have hqF : F (Ψ.symm q) = q := by
        change (E.toSphere ∘ localCollar D s) (Ψ.symm q) = q
        rw [heqΨ hqΨ]
        exact Ψ.toPartialEquiv.right_inv hq
      change e.symm q = Ψ.symm q
      calc e.symm q = e.symm (F (Ψ.symm q)) := congrArg e.symm hqF.symm
        _ = Ψ.symm q := e.left_inv (hΨO hqΨ)
    exact ((Ψ.symm.contMDiffOn.contMDiffAt (Ψ.open_target.mem_nhds hFy)).congr_of_eventuallyEq
      heq).contMDiffWithinAt
  let Φ : PartialDiffeomorph 𝓘(ℝ,E3) (𝓡 3) E3 ThreeSphere ∞ := {
    toPartialEquiv := e
    open_source := hO
    open_target := hopen
    contMDiffOn_toFun := hinc.contMDiff.comp_contMDiffOn
      ((actual_localCollar_smooth_v475 D s W.R).mono hOC)
    contMDiffOn_invFun := hinverse }
  exact ⟨Φ,rfl,rfl,rfl⟩

#print axioms actual_interior_collar_global_partialDiffeomorph_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
