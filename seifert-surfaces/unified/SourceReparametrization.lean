import A3SharedGraph
set_option autoImplicit false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.SourceReparametrization
open SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- Domain reparametrization in one fixed actual metric; the tangential
correction is retained instead of asserting equality of whole accelerations. -/
theorem source_reparametrization_covariant_trace
    (V : Set E3) (hV : IsOpen V) (g : CoordinateMetric V)
    (Ω U : Set E2) (hΩ : IsOpen Ω) (hU : IsOpen U)
    (Φ : E2 → E3) (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    (hΦimage : MapsTo Φ Ω V)
    (hΦregular : ∀ y ∈ Ω, Function.Injective (fderiv ℝ Φ y))
    (κ : E2 → E2) (hκ : ContDiffOn ℝ ∞ κ U) (hκimage : MapsTo κ U Ω)
    (hκregular : ∀ x ∈ U, Function.Bijective (fderiv ℝ κ x)) :
    ∀ x ∈ U,
      fderiv ℝ (Φ ∘ κ) x = (fderiv ℝ Φ (κ x)).comp (fderiv ℝ κ x) ∧
      LinearMap.range (fderiv ℝ (Φ ∘ κ) x).toLinearMap =
        LinearMap.range (fderiv ℝ Φ (κ x)).toLinearMap ∧
      tracedAcceleration g.tensor (Φ ∘ κ) x - tracedAcceleration g.tensor Φ (κ x) ∈
        LinearMap.range (fderiv ℝ (Φ ∘ κ) x).toLinearMap := by
  classical
  intro x hx
  have hΦat := hΦ.contDiffAt (hΩ.mem_nhds (hκimage hx))
  have hκat := hκ.contDiffAt (hU.mem_nhds hx)
  have hΦd := hΦat.differentiableAt (by norm_num)
  have hκd := hκat.differentiableAt (by norm_num)
  have hchain : fderiv ℝ (Φ ∘ κ) x = (fderiv ℝ Φ (κ x)).comp (fderiv ℝ κ x) :=
    (hΦd.hasFDerivAt.comp x hκd.hasFDerivAt).fderiv
  have hrange : LinearMap.range (fderiv ℝ (Φ ∘ κ) x).toLinearMap =
      LinearMap.range (fderiv ℝ Φ (κ x)).toLinearMap := by
    rw [hchain]
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨fderiv ℝ κ x v, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := (hκregular x hx).2 v
      exact ⟨w, by simp [hw]⟩
  refine ⟨hchain, hrange, ?_⟩
  let F := fderiv ℝ Φ (κ x)
  let A := fderiv ℝ κ x
  let J : Matrix (Fin 2) (Fin 2) ℝ := fun a i => A (coordinateVector 2 i) a
  let m := inducedMetric g.tensor Φ (κ x)
  let M := inducedMetric g.tensor (Φ ∘ κ) x
  have hcoord : ∀ v : E2, v = ∑ a : Fin 2, v a • coordinateVector 2 a := by
    intro v
    ext a
    fin_cases a <;> simp [Fin.sum_univ_succ, coordinateVector,
      EuclideanSpace.single, PiLp.single_apply, PiLp.add_apply, PiLp.smul_apply]
  have hJmatrix : J = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis A.toLinearMap := by
    ext a i
    simp [J, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_toBasis,
      PiLp.basisFun_repr, PiLp.basisFun_apply, coordinateVector, A]
  have hJunit : IsUnit J.det := by
    apply (Matrix.isUnit_iff_isUnit_det J).mp
    rw [hJmatrix]
    apply (LinearMap.isUnit_toMatrix_iff _).mpr
    exact (LinearMap.isUnit_iff_ker_eq_bot _).mpr
      (LinearMap.ker_eq_bot.mpr (hκregular x hx).1)
  have hFbasis : ∀ v : E2, F v = ∑ a : Fin 2, v a • graphTangent Φ (κ x) a := by
    intro v
    calc
      F v = F (∑ a : Fin 2, v a • coordinateVector 2 a) := congrArg F (hcoord v)
      _ = _ := by simp only [map_sum, map_smul]; rfl
  have htangent : ∀ i : Fin 2, graphTangent (Φ ∘ κ) x i =
      ∑ a : Fin 2, J a i • graphTangent Φ (κ x) a := by
    intro i
    change fderiv ℝ (Φ ∘ κ) x (coordinateVector 2 i) = _
    rw [hchain, ContinuousLinearMap.comp_apply]
    exact hFbasis (A (coordinateVector 2 i))
  have hmetric : M = J.transpose * m * J := by
    ext i j
    dsimp only [M, m, inducedMetric]
    simp only [htangent, Matrix.mul_apply, Matrix.transpose_apply]
    dsimp only [inducedMetric]
    simp only [Function.comp_apply, coordinateInner, Fin.sum_univ_succ, Fin.sum_univ_zero,
      PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, add_zero, zero_add, mul_zero, zero_mul]
    fin_cases i <;> fin_cases j <;> ring
  have hcontraction : J * M⁻¹ * J.transpose = m⁻¹ := by
    rw [hmetric, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    have hJTunit : IsUnit J.transpose.det := by simpa using hJunit
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul J.transpose hJTunit, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J⁻¹, Matrix.mul_nonsing_inv J hJunit, Matrix.one_mul]
  have hDF : DifferentiableAt ℝ (fderiv ℝ Φ) (κ x) :=
    (hΦat.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDA : DifferentiableAt ℝ (fderiv ℝ κ) x :=
    (hκat.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hκjd : ∀ j : Fin 2, DifferentiableAt ℝ (fun z => (fderiv ℝ κ z (coordinateVector 2 j))) x := by
    intro j
    exact (hDA.hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector 2 j) x)).differentiableAt
  have htangent_local : ∀ j : Fin 2,
      (fun z => graphTangent (Φ ∘ κ) z j) =ᶠ[𝓝 x]
        (fun z => (fderiv ℝ Φ (κ z)) ((fderiv ℝ κ z (coordinateVector 2 j)))) := by
    intro j
    filter_upwards [hU.mem_nhds hx] with z hz
    have hΦz := (hΦ.contDiffAt (hΩ.mem_nhds (hκimage hz))).differentiableAt (by norm_num)
    have hκz := (hκ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
    dsimp only [graphTangent]
    rw [(hΦz.hasFDerivAt.comp z hκz.hasFDerivAt).fderiv]
    rfl
  have hsecond : ∀ i j : Fin 2,
      fderiv ℝ (fun z => graphTangent (Φ ∘ κ) z j) x (coordinateVector 2 i) =
        F (fderiv ℝ (fun z => (fderiv ℝ κ z (coordinateVector 2 j))) x (coordinateVector 2 i)) +
        (fderiv ℝ (fderiv ℝ Φ) (κ x)) (A (coordinateVector 2 i)) (A (coordinateVector 2 j)) := by
    intro i j
    rw [(htangent_local j).fderiv_eq]
    have happly := fderiv_clm_apply (hDF.comp x hκd) (hκjd j)
    simp only [Function.comp_def] at happly
    rw [happly]
    have hcomp := fderiv_comp x hDF hκd
    simp only [Function.comp_def] at hcomp
    rw [hcomp]
    rfl
  have hsecond_basis : ∀ a b : Fin 2,
      (fderiv ℝ (fderiv ℝ Φ) (κ x)) (coordinateVector 2 a) (coordinateVector 2 b) =
        fderiv ℝ (fun z => graphTangent Φ z b) (κ x) (coordinateVector 2 a) := by
    intro a b
    change _ = fderiv ℝ (fun z => (fderiv ℝ Φ z) (coordinateVector 2 b)) (κ x) _
    rw [fderiv_clm_apply hDF (differentiableAt_const _)]
    simp
  have hsecond_expand : ∀ i j : Fin 2,
      (fderiv ℝ (fderiv ℝ Φ) (κ x)) (A (coordinateVector 2 i)) (A (coordinateVector 2 j)) =
        ∑ a : Fin 2, ∑ b : Fin 2, (J a i * J b j) •
          fderiv ℝ (fun z => graphTangent Φ z b) (κ x) (coordinateVector 2 a) := by
    intro i j
    conv_lhs => arg 1; rw [hcoord (A (coordinateVector 2 i))]
    rw [map_sum]
    simp only [ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hcoord (A (coordinateVector 2 j)), map_sum, Finset.smul_sum]
    simp only [map_smul, smul_smul, hsecond_basis, J]
  have hacceleration : ∀ i j : Fin 2,
      covariantAcceleration g.tensor (Φ ∘ κ) x i j =
        F (fderiv ℝ (fun z => (fderiv ℝ κ z (coordinateVector 2 j))) x (coordinateVector 2 i)) +
        ∑ a : Fin 2, ∑ b : Fin 2, (J a i * J b j) •
          covariantAcceleration g.tensor Φ (κ x) a b := by
    intro i j
    dsimp only [covariantAcceleration]
    simp only [hsecond, hsecond_expand, htangent, Function.comp_apply]
    ext k
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, PiLp.add_apply, PiLp.smul_apply,
      PiLp.zero_apply, smul_eq_mul, coordinateVector, EuclideanSpace.single, PiLp.single_apply]
    fin_cases k <;> simp <;> ring
  have hcontraction_coefficient : ∀ a b : Fin 2,
      (∑ i : Fin 2, ∑ j : Fin 2, M⁻¹ i j * J a i * J b j) = m⁻¹ a b := by
    intro a b
    have heq := congrArg (fun H : Matrix (Fin 2) (Fin 2) ℝ => H a b) hcontraction
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero] at heq ⊢
    linear_combination heq
  have hweighted :
      (∑ i : Fin 2, ∑ j : Fin 2, M⁻¹ i j •
        (∑ a : Fin 2, ∑ b : Fin 2, (J a i * J b j) •
          covariantAcceleration g.tensor Φ (κ x) a b)) =
      tracedAcceleration g.tensor Φ (κ x) := by
    calc
      _ = ∑ a : Fin 2, ∑ b : Fin 2,
          (∑ i : Fin 2, ∑ j : Fin 2, M⁻¹ i j * J a i * J b j) •
            covariantAcceleration g.tensor Φ (κ x) a b := by
        ext k
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, PiLp.add_apply,
          PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, add_zero, mul_zero, zero_mul]
        ring
      _ = _ := by
        dsimp only [tracedAcceleration]
        simp only [hcontraction_coefficient, m]
  let correction : E2 := ∑ i : Fin 2, ∑ j : Fin 2,
    M⁻¹ i j • fderiv ℝ (fun z => (fderiv ℝ κ z (coordinateVector 2 j))) x (coordinateVector 2 i)
  have htrace : tracedAcceleration g.tensor (Φ ∘ κ) x =
      F correction + tracedAcceleration g.tensor Φ (κ x) := by
    calc
      _ = (∑ i : Fin 2, ∑ j : Fin 2, M⁻¹ i j •
            F (fderiv ℝ (fun z => (fderiv ℝ κ z (coordinateVector 2 j))) x (coordinateVector 2 i))) +
          (∑ i : Fin 2, ∑ j : Fin 2, M⁻¹ i j •
            (∑ a : Fin 2, ∑ b : Fin 2, (J a i * J b j) •
              covariantAcceleration g.tensor Φ (κ x) a b)) := by
        dsimp only [tracedAcceleration]
        simp only [M, hacceleration, smul_add, Finset.sum_add_distrib]
      _ = _ := by rw [hweighted]; simp only [correction, map_sum, map_smul]
  rw [hrange]
  refine ⟨correction, ?_⟩
  change F correction = _
  rw [htrace, add_sub_cancel_right]


universe u v
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]

/-- Actual local original-sheet coordinates and two smooth inverse maps.
All boundary avoidance and domains are output geometry obligations. -/
structure OriginalSheetLocalReparametrization (P : EmbeddedSheet.{u,v} N)
    (Ψ : E2 → N) (U : Set E2) (c : SmoothAmbientChart N) (x : E2) where
  sourcePoint : P.carrier
  sourcePoint_value : P.inclusion sourcePoint = Ψ x
  sourcePoint_interior : sourcePoint ∈ (𝓡∂ 2).interior P.carrier
  targetDomain : Set E2
  target_open : IsOpen targetDomain
  point_inside : x ∈ targetDomain
  target_inside : targetDomain ⊆ U ∩ Ψ ⁻¹' c.chart.source
  sourceDomain : Set E2
  source_open : IsOpen sourceDomain
  source_inside : sourceDomain ⊆ P.coordinateInterior sourcePoint c
  source_smooth : ContDiffOn ℝ ∞ (c.chart ∘ P.parameter sourcePoint) sourceDomain
  source_regular : ∀ y ∈ sourceDomain,
    Function.Injective (fderiv ℝ (c.chart ∘ P.parameter sourcePoint) y)
  lift : E2 → E2
  lift_smooth : ContDiffOn ℝ ∞ lift targetDomain
  lift_image : lift '' targetDomain = sourceDomain
  lift_regular : ∀ z ∈ targetDomain, Function.Bijective (fderiv ℝ lift z)
  inverse : E2 → E2
  inverse_smooth : ContDiffOn ℝ ∞ inverse sourceDomain
  inverse_image : MapsTo inverse sourceDomain targetDomain
  inverse_left : ∀ z ∈ targetDomain, inverse (lift z) = z
  inverse_right : ∀ y ∈ sourceDomain, lift (inverse y) = y
  original_parameter_eq : ∀ z ∈ targetDomain, P.parameter sourcePoint (lift z) = Ψ z

/-- Smooth immersed image inclusion must produce an actual interior lift;
the original sheet's boundary is not silently used as an open coordinate set. -/
theorem original_sheet_local_smooth_inverse
    (P : EmbeddedSheet.{u,v} N) (U : Set E2) (hU : IsOpen U) (Ψ : E2 → N)
    (hΨ : ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E3) ∞ Ψ U)
    (hΨregular : ∀ z ∈ U,
      Function.Injective (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) Ψ z))
    (himage : MapsTo Ψ U P.image)
    (c : SmoothAmbientChart N) (x : E2) (hx : x ∈ U) (hcx : Ψ x ∈ c.chart.source) :
    Nonempty (OriginalSheetLocalReparametrization P Ψ U c x) := by
  classical
  obtain ⟨s₀, hs₀⟩ := himage hx
  letI : Nonempty P.carrier := ⟨s₀⟩
  let L : E2 → P.carrier := Function.invFun P.inclusion ∘ Ψ
  have hLvalue : ∀ z ∈ U, P.inclusion (L z) = Ψ z := by
    intro z hz
    exact Function.invFun_eq (himage hz)
  have hLat : ∀ z ∈ U, ContMDiffAt 𝓘(ℝ, E2) (𝓡∂ 2) ∞ L z := by
    intro z hz
    have heq : P.inclusion ∘ L =ᶠ[𝓝 z] Ψ := by
      filter_upwards [hU.mem_nhds hz] with y hy
      exact hLvalue y hy
    have hcomp : ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, E3) ∞ (P.inclusion ∘ L) z :=
      (hΨ.contMDiffAt (hU.mem_nhds hz)).congr_of_eventuallyEq heq
    have hcontinuous : ContinuousAt L z :=
      P.smoothEmbedding.isEmbedding.isInducing.continuousAt_iff.mpr hcomp.continuousAt
    exact (ContMDiffAt.iff_comp_isImmersionAt (P.smoothEmbedding.isImmersion.isImmersionAt (L z))).mpr
      ⟨hcontinuous, hcomp⟩
  have hLregular : ∀ z ∈ U,
      Function.Bijective (mfderiv 𝓘(ℝ, E2) (𝓡∂ 2) L z) := by
    intro z hz
    have hLd := (hLat z hz).mdifferentiableAt (by norm_num)
    have hPd := (P.smoothEmbedding.contMDiff.contMDiffAt (x := L z)).mdifferentiableAt (by norm_num)
    have heq : P.inclusion ∘ L =ᶠ[𝓝 z] Ψ := by
      filter_upwards [hU.mem_nhds hz] with y hy
      exact hLvalue y hy
    have htarget := heq.mfderiv_eq (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E3))
    have hcomp := mfderiv_comp z hPd hLd
    have hinjcomp : Function.Injective (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) (P.inclusion ∘ L) z) := by
      rw [htarget]
      exact (tangentSpaceCast 𝓘(ℝ, E3) (Ψ z) ((P.inclusion ∘ L) z)).injective.comp
        (hΨregular z hz)
    have hinj : Function.Injective (mfderiv 𝓘(ℝ, E2) (𝓡∂ 2) L z) := by
      intro a b hab
      apply hinjcomp
      rw [hcomp]
      simpa only [ContinuousLinearMap.comp_apply, hab]
    exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hLinterior : ∀ z ∈ U, (𝓡∂ 2).IsInteriorPoint (L z) := by
    intro z hz
    apply ((hLat z hz).mdifferentiableAt (by norm_num)).isInteriorPoint_of_surjective_mfderiv
      (hLregular z hz).2
    simp [ModelWithCorners.IsInteriorPoint]
  let s : P.carrier := L x
  let e := extChartAt (𝓡∂ 2) s
  let D : Set E2 := U ∩ L ⁻¹' (chartAt (EuclideanHalfSpace 2) s).source ∩
    Ψ ⁻¹' c.chart.source
  have hLcont : ContinuousOn L U := fun z hz => (hLat z hz).continuousAt.continuousWithinAt
  have hDopen : IsOpen D := by
    have hset : D = (U ∩ L ⁻¹' (chartAt (EuclideanHalfSpace 2) s).source) ∩
        (U ∩ Ψ ⁻¹' c.chart.source) := by
      ext z
      change ((z ∈ U ∧ L z ∈ (chartAt (EuclideanHalfSpace 2) s).source) ∧
        Ψ z ∈ c.chart.source) ↔
        ((z ∈ U ∧ L z ∈ (chartAt (EuclideanHalfSpace 2) s).source) ∧
          (z ∈ U ∧ Ψ z ∈ c.chart.source))
      tauto
    rw [hset]
    exact (hLcont.isOpen_inter_preimage hU (chartAt (EuclideanHalfSpace 2) s).open_source).inter
      (hΨ.continuousOn.isOpen_inter_preimage hU c.chart.open_source)
  have hxD : x ∈ D := by
    exact ⟨⟨hx, mem_chart_source (EuclideanHalfSpace 2) s⟩, hcx⟩
  let k : E2 → E2 := e ∘ L
  have hkAt : ∀ z ∈ D, ContDiffAt ℝ ∞ k z := by
    intro z hz
    have he : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, E2) ∞ e (L z) :=
      contMDiffAt_extChartAt' hz.1.2
    exact (he.comp z (hLat z hz.1.1)).contDiffAt
  have hkReg : ∀ z ∈ D, Function.Bijective (fderiv ℝ k z) := by
    intro z hz
    have he := (contMDiffAt_extChartAt' (I := 𝓡∂ 2) (n := ∞) hz.1.2).mdifferentiableAt (by norm_num)
    have hLd := (hLat z hz.1.1).mdifferentiableAt (by norm_num)
    have hcomp := mfderiv_comp z he hLd
    have hsource : L z ∈ (extChartAt (𝓡∂ 2) s).source := by
      simpa only [extChartAt_source] using (show L z ∈ (chartAt (EuclideanHalfSpace 2) s).source from hz.1.2)
    have hinv := (isInvertible_mfderiv_extChartAt hsource).bijective
    have hbij : Function.Bijective (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) k z) := by
      rw [hcomp]
      exact hinv.comp (hLregular z hz.1.1)
    have hinj : Function.Injective (fderiv ℝ k z) := by
      intro a b hab
      have ha := congrArg (fun F => F ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm a))
        (mfderiv_eq_fderiv (𝕜 := ℝ) (f := k) (x := z))
      have hb := congrArg (fun F => F ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm b))
        (mfderiv_eq_fderiv (𝕜 := ℝ) (f := k) (x := z))
      have heq : mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) k z ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm a) =
          mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) k z ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm b) := by
        simp only [ha, hb, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.apply_symm_apply, hab]
      exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.injective (hbij.1 heq)
    exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hcMD : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
    ⟨c.smooth.mdifferentiableOn (by norm_num), c.inverse_smooth.mdifferentiableOn (by norm_num)⟩
  have hcoordAt : ∀ z ∈ D, ContDiffAt ℝ ∞ (c.chart ∘ Ψ) z := by
    intro z hz
    exact ((c.smooth.contMDiffAt (c.chart.open_source.mem_nhds hz.2)).comp z
      (hΨ.contMDiffAt (hU.mem_nhds hz.1.1))).contDiffAt
  have hcoordReg : ∀ z ∈ D, Function.Injective (fderiv ℝ (c.chart ∘ Ψ) z) := by
    intro z hz
    have hc := hcMD.mdifferentiableAt hz.2
    have hp := (hΨ.contMDiffAt (hU.mem_nhds hz.1.1)).mdifferentiableAt (by norm_num)
    have hcomp := mfderiv_comp z hc hp
    have hi : Function.Injective (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) (c.chart ∘ Ψ) z) := by
      rw [hcomp]
      exact (hcMD.mfderiv_injective hz.2).comp (hΨregular z hz.1.1)
    intro a b hab
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.injective
    apply hi
    rw [mfderiv_eq_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, hab]
  let k' : E2 ≃L[ℝ] E2 := ContinuousLinearEquiv.ofBijective (fderiv ℝ k x)
    (LinearMap.ker_eq_bot.mpr (hkReg x hxD).1) (LinearMap.range_eq_top.mpr (hkReg x hxD).2)
  have hk' : HasFDerivAt k (k' : E2 →L[ℝ] E2) x := by
    change HasFDerivAt k (fderiv ℝ k x) x
    exact ((hkAt x hxD).differentiableAt (by norm_num)).hasFDerivAt
  let f : OpenPartialHomeomorph E2 E2 := (hkAt x hxD).toOpenPartialHomeomorph k hk' (by norm_num)
  have hfx : x ∈ f.source := (hkAt x hxD).mem_toOpenPartialHomeomorph_source hk' (by norm_num)
  have hfcoe : (f : E2 → E2) = k := rfl
  let T : Set E2 := f.source ∩ D
  let S : Set E2 := f '' T
  have hTopen : IsOpen T := f.open_source.inter hDopen
  have hxT : x ∈ T := ⟨hfx, hxD⟩
  have hSopen : IsOpen S := f.isOpen_image_of_subset_source hTopen inter_subset_left
  have hS_inv : ∀ y ∈ S, f.symm y ∈ T := by
    rintro y ⟨z, hz, rfl⟩
    simpa only [f.left_inv hz.1] using hz
  have hS_target : S ⊆ f.target := by
    rintro y ⟨z, hz, rfl⟩
    exact f.map_source hz.1
  have hInvAt : ∀ y ∈ S, ContDiffAt ℝ ∞ (f.symm : E2 → E2) y := by
    intro y hy
    have hz := hS_inv y hy
    let ky' : E2 ≃L[ℝ] E2 := ContinuousLinearEquiv.ofBijective (fderiv ℝ k (f.symm y))
      (LinearMap.ker_eq_bot.mpr (hkReg (f.symm y) hz.2).1)
      (LinearMap.range_eq_top.mpr (hkReg (f.symm y) hz.2).2)
    have hd : HasFDerivAt (f : E2 → E2) (ky' : E2 →L[ℝ] E2) (f.symm y) :=
      by
        change HasFDerivAt k (fderiv ℝ k (f.symm y)) (f.symm y)
        exact ((hkAt (f.symm y) hz.2).differentiableAt (by norm_num)).hasFDerivAt
    exact f.contDiffAt_symm (hS_target hy) hd (hkAt (f.symm y) hz.2)
  have hInvReg : ∀ y ∈ S, Function.Bijective (fderiv ℝ (f.symm : E2 → E2) y) := by
    intro y hy
    have hz := hS_inv y hy
    have hi := (hInvAt y hy).differentiableAt (by norm_num)
    have hkz := (hkAt (f.symm y) hz.2).differentiableAt (by norm_num)
    have heq : k ∘ (f.symm : E2 → E2) =ᶠ[𝓝 y] id := by
      filter_upwards [f.open_target.mem_nhds (hS_target hy)] with w hw
      exact f.right_inv hw
    have hidentity := heq.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp y hkz hi, fderiv_id] at hidentity
    have hinj : Function.Injective (fderiv ℝ (f.symm : E2 → E2) y) := by
      intro a b hab
      have ha := congrArg (fun F : E2 →L[ℝ] E2 => F a) hidentity
      have hb := congrArg (fun F : E2 →L[ℝ] E2 => F b) hidentity
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at ha hb
      rw [hab] at ha
      exact ha.symm.trans hb
    exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hparam : ∀ z ∈ T, P.parameter s (k z) = Ψ z := by
    intro z hz
    change P.inclusion (e.symm (e (L z))) = Ψ z
    rw [e.left_inv (by simpa only [e, extChartAt_source] using (show L z ∈ (chartAt (EuclideanHalfSpace 2) s).source from hz.2.1.2))]
    exact hLvalue z hz.2.1.1
  have hparam_inverse : ∀ y ∈ S, P.parameter s y = Ψ (f.symm y) := by
    intro y hy
    have hz := hS_inv y hy
    have heq := hparam (f.symm y) hz
    simpa only [← hfcoe, f.right_inv (hS_target hy)] using heq
  have hsource_inside : S ⊆ P.coordinateInterior s c := by
    rintro y ⟨z, hz, rfl⟩
    have hLsource : L z ∈ e.source := by
      simpa only [e, extChartAt_source] using (show L z ∈ (chartAt (EuclideanHalfSpace 2) s).source from hz.2.1.2)
    change ((f z ∈ e.target ∧ e.symm (f z) ∈ (𝓡∂ 2).interior P.carrier) ∧
      P.parameter s (f z) ∈ c.chart.source)
    change ((e (L z) ∈ e.target ∧ e.symm (e (L z)) ∈ (𝓡∂ 2).interior P.carrier) ∧
      P.parameter s (k z) ∈ c.chart.source)
    rw [e.left_inv hLsource, hparam z hz]
    exact ⟨⟨e.map_source hLsource, hLinterior z hz.2.1.1⟩, hz.2.2⟩
  have hparamAt : ∀ y ∈ S, ContDiffAt ℝ ∞ (c.chart ∘ P.parameter s) y := by
    intro y hy
    have hz := hS_inv y hy
    have heq : c.chart ∘ P.parameter s =ᶠ[𝓝 y] (c.chart ∘ Ψ) ∘ (f.symm : E2 → E2) := by
      filter_upwards [hSopen.mem_nhds hy] with w hw
      exact congrArg c.chart (hparam_inverse w hw)
    exact ((hcoordAt (f.symm y) hz.2).comp y (hInvAt y hy)).congr_of_eventuallyEq heq
  have hparamReg : ∀ y ∈ S, Function.Injective (fderiv ℝ (c.chart ∘ P.parameter s) y) := by
    intro y hy
    have hz := hS_inv y hy
    have heq : c.chart ∘ P.parameter s =ᶠ[𝓝 y] (c.chart ∘ Ψ) ∘ (f.symm : E2 → E2) := by
      filter_upwards [hSopen.mem_nhds hy] with w hw
      exact congrArg c.chart (hparam_inverse w hw)
    rw [heq.fderiv_eq, fderiv_comp y
      ((hcoordAt (f.symm y) hz.2).differentiableAt (by norm_num))
      ((hInvAt y hy).differentiableAt (by norm_num))]
    exact (hcoordReg (f.symm y) hz.2).comp (hInvReg y hy).1
  refine ⟨{
    sourcePoint := s
    sourcePoint_value := hLvalue x hx
    sourcePoint_interior := hLinterior x hx
    targetDomain := T
    target_open := hTopen
    point_inside := hxT
    target_inside := fun z hz => ⟨hz.2.1.1, hz.2.2⟩
    sourceDomain := S
    source_open := hSopen
    source_inside := hsource_inside
    source_smooth := fun y hy => (hparamAt y hy).contDiffWithinAt
    source_regular := hparamReg
    lift := k
    lift_smooth := fun z hz => (hkAt z hz.2).contDiffWithinAt
    lift_image := by exact congrArg (fun q : E2 → E2 => q '' T) hfcoe |>.symm
    lift_regular := fun z hz => hkReg z hz.2
    inverse := f.symm
    inverse_smooth := fun y hy => (hInvAt y hy).contDiffWithinAt
    inverse_image := hS_inv
    inverse_left := fun z hz => f.left_inv hz.1
    inverse_right := fun y hy => f.right_inv (hS_target hy)
    original_parameter_eq := hparam
  }⟩


/-- Minimality comes from the supplied ORIGINAL sheet, after constructing
the local lift; no minimality certificate for Ψ or chart replacement is input. -/
theorem immersed_map_in_original_minimal_sheet {h : AmbientMetric N}
    (P : EmbeddedSheet.{u,v} N) (hminimal : P.Minimal h)
    (U : Set E2) (hU : IsOpen U) (Ψ : E2 → N)
    (hΨ : ContMDiffOn 𝓘(ℝ, E2) 𝓘(ℝ, E3) ∞ Ψ U)
    (hΨregular : ∀ x ∈ U,
      Function.Injective (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) Ψ x))
    (himage : MapsTo Ψ U P.image) (c : SmoothAmbientChart N) :
    IsMinimalParametrizationOn (actualChartTensor h c) (c.chart ∘ Ψ)
      (U ∩ Ψ ⁻¹' c.chart.source) := by
  classical
  have hmetric :
      (∀ i j, ContDiffOn ℝ ∞ (fun y => actualChartTensor h c y i j) c.chart.target) ∧
      (∀ y ∈ c.chart.target, ∀ i j,
        actualChartTensor h c y i j = actualChartTensor h c y j i) ∧
      (∀ y ∈ c.chart.target, ∀ w : E3, w ≠ 0 →
        0 < coordinateInner (actualChartTensor h c) y w w) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      letI : Bundle.RiemannianBundle (fun p : N => TangentSpace 𝓘(ℝ, E3) p) :=
        ⟨h.toRiemannianMetric⟩
      have hv (k : Fin 3) : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
          (fun y => (⟨c.chart.symm y, inverseChartDifferential c y (coordinateVector 3 k)⟩ :
            TangentBundle 𝓘(ℝ, E3) N)) c.chart.target := by
        have hs : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3).tangent ∞
            (fun y => (⟨y, (NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k)⟩ :
              TangentBundle 𝓘(ℝ, E3) E3)) :=
          contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
        have ht := c.inverse_smooth.contMDiffOn_tangentMapWithin
          (m := ∞) (by simp) c.chart.open_target.uniqueMDiffOn
        have hc := ht.comp hs.contMDiffOn (by intro y hy; exact hy)
        apply hc.congr
        intro y hy
        change (⟨c.chart.symm y, (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm y)
          ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩ : TangentBundle 𝓘(ℝ, E3) N) =
            ⟨c.chart.symm y, (mfderivWithin 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart.symm c.chart.target y)
              ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 k))⟩
        rw [mfderivWithin_eq_mfderiv (c.chart.open_target.uniqueMDiffOn y hy)
          (((c.inverse_smooth y hy).mdifferentiableWithinAt (by simp)).mdifferentiableAt
            (c.chart.open_target.mem_nhds hy))]
      exact (open scoped Bundle in (hv i |>.inner_bundle (hv j)).contDiffOn)
    · intro y hy i j
      exact h.symm _ _ _
    · intro y hy w hw
      have he : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
        ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
      have hinj : Function.Injective (inverseChartDifferential c y) :=
        (he.symm.mfderiv_injective hy).comp (NormedSpace.fromTangentSpace y).symm.injective
      have hn : inverseChartDifferential c y w ≠ 0 := by
        intro hh
        apply hw
        apply hinj
        simpa only [map_zero] using hh
      have hid (v w : E3) : coordinateInner (actualChartTensor h c) y v w =
          h.inner (c.chart.symm y) (inverseChartDifferential c y v)
            (inverseChartDifferential c y w) := by
        have hsum (v : E3) : (∑ i : Fin 3, v i • coordinateVector 3 i) = v := by
          ext j
          simp [coordinateVector, EuclideanSpace.single, Pi.single_apply]
        have hdiff (v : E3) : inverseChartDifferential c y v =
            ∑ i : Fin 3, v i • inverseChartDifferential c y (coordinateVector 3 i) := by
          simpa only [map_sum, map_smul] using congrArg (inverseChartDifferential c y) (hsum v).symm
        dsimp only [coordinateInner, actualChartTensor]
        rw [hdiff v, hdiff w, map_sum]
        simp only [map_smul, sum_apply, smul_apply, map_sum, smul_eq_mul]
        simp only [Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
      rw [hid]
      exact h.pos _ _ hn
  let g : CoordinateMetric c.chart.target := {
    tensor := actualChartTensor h c
    smooth := hmetric.1
    symmetric := hmetric.2.1
    positive := hmetric.2.2 }
  refine ⟨?_, ?_⟩
  · exact (c.smooth.comp (hΨ.mono inter_subset_left) (fun z hz => hz.2)).contDiffOn
  · intro x hx
    obtain ⟨r⟩ := original_sheet_local_smooth_inverse P U hU Ψ hΨ hΨregular himage c x hx.1 hx.2
    let Φ : E2 → E3 := c.chart ∘ P.parameter r.sourcePoint
    have hΦimage : MapsTo Φ r.sourceDomain c.chart.target := by
      intro y hy
      exact c.chart.map_source (r.source_inside hy).2
    have hkimage : MapsTo r.lift r.targetDomain r.sourceDomain := by
      intro z hz
      rw [← r.lift_image]
      exact mem_image_of_mem r.lift hz
    have htransport := source_reparametrization_covariant_trace c.chart.target c.chart.open_target g
      r.sourceDomain r.targetDomain r.source_open r.target_open Φ r.source_smooth hΦimage r.source_regular
      r.lift r.lift_smooth hkimage r.lift_regular x r.point_inside
    have heq : Φ ∘ r.lift =ᶠ[𝓝 x] c.chart ∘ Ψ := by
      filter_upwards [r.target_open.mem_nhds r.point_inside] with z hz
      exact congrArg c.chart (r.original_parameter_eq z hz)
    have hderiv := heq.fderiv_eq (𝕜 := ℝ)
    have htangent : ∀ j : Fin 2,
        (fun z => graphTangent (Φ ∘ r.lift) z j) =ᶠ[𝓝 x]
          (fun z => graphTangent (c.chart ∘ Ψ) z j) := by
      intro j
      filter_upwards [heq.fderiv (𝕜 := ℝ)] with z hz
      exact congrArg (fun F : E2 →L[ℝ] E3 => F (coordinateVector 2 j)) hz
    have htrace : tracedAcceleration (actualChartTensor h c) (Φ ∘ r.lift) x =
        tracedAcceleration (actualChartTensor h c) (c.chart ∘ Ψ) x := by
      have hv := heq.eq_of_nhds
      dsimp only [tracedAcceleration]
      have hgram : inducedMetric (actualChartTensor h c) (Φ ∘ r.lift) x =
          inducedMetric (actualChartTensor h c) (c.chart ∘ Ψ) x := by
        change (fun i j => coordinateInner (actualChartTensor h c) ((Φ ∘ r.lift) x)
          (fderiv ℝ (Φ ∘ r.lift) x (coordinateVector 2 i))
          (fderiv ℝ (Φ ∘ r.lift) x (coordinateVector 2 j))) = _
        rw [hv, hderiv]
        rfl
      rw [hgram]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      have hsecond := (htangent j).fderiv_eq (𝕜 := ℝ)
      dsimp only [graphTangent] at hsecond
      dsimp only [covariantAcceleration, graphTangent]
      rw [hsecond, hv, hderiv]
    have hmin := (hminimal r.sourcePoint c).2 (r.lift x)
      (r.source_inside (hkimage r.point_inside))
    have hmin' : tracedAcceleration g.tensor Φ (r.lift x) ∈
        LinearMap.range (fderiv ℝ (Φ ∘ r.lift) x).toLinearMap := by
      rw [htransport.2.1]
      exact hmin
    have hadd := (LinearMap.range (fderiv ℝ (Φ ∘ r.lift) x).toLinearMap).add_mem
      htransport.2.2 hmin'
    rw [sub_add_cancel] at hadd
    change tracedAcceleration (actualChartTensor h c) (Φ ∘ r.lift) x ∈
      LinearMap.range (fderiv ℝ (Φ ∘ r.lift) x).toLinearMap at hadd
    rwa [htrace, hderiv] at hadd


end SeifertSurfaces.OriginalEndpoints.SourceReparametrization
