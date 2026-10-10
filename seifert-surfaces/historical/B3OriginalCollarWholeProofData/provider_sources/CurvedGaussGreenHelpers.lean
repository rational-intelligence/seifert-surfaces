import CurvedSignedDivergence

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

def coordinates : E2 ≃L[ℝ] ℝ × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

def IsCoordinateFrame (Q : E2 ≃ₗᵢ[ℝ] E2) : Prop :=
  (∀ x : E2, Q x 0 = x 0 ∧ Q x 1 = x 1) ∨
  (∀ x : E2, Q x 0 = x 1 ∧ Q x 1 = x 0)

def shear (Q : E2 ≃ₗᵢ[ℝ] E2) (sigma : ℝ) (f : ℝ → ℝ) : ℝ × ℝ → E2 :=
  fun z => Q.symm (coordinates.symm (z.1, f z.1 + sigma * z.2))

def unshear (Q : E2 ≃ₗᵢ[ℝ] E2) (sigma : ℝ) (f : ℝ → ℝ) : E2 → ℝ × ℝ :=
  fun x => ((Q x) 0, sigma * ((Q x) 1 - f ((Q x) 0)))

def shearDerivative (Q : E2 ≃ₗᵢ[ℝ] E2) (sigma : ℝ) (f : ℝ → ℝ)
    (u : ℝ) : (ℝ × ℝ) →L[ℝ] E2 :=
  Q.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (coordinates.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (deriv f u • ContinuousLinearMap.fst ℝ ℝ ℝ +
          sigma • ContinuousLinearMap.snd ℝ ℝ ℝ)))

def transverse (Q : E2 ≃ₗᵢ[ℝ] E2) (s : E2 → ℝ) (x : E2) : ℝ :=
  fderiv ℝ (s ∘ Q.symm) (Q x) (coordinateVector 2 1)

def transformedFlux (Q : E2 ≃ₗᵢ[ℝ] E2) (sigma : ℝ) (f : ℝ → ℝ)
    (W : E2 → E2) : ℝ × ℝ → ℝ × ℝ :=
  fun z => ((Q (W (shear Q sigma f z))) 0,
    sigma * ((Q (W (shear Q sigma f z))) 1 -
      deriv f z.1 * (Q (W (shear Q sigma f z))) 0))

def halfBox (positive : Bool) (a b h : ℝ) : Set (ℝ × ℝ) :=
  if positive then Icc (a, 0) (b, h) else Icc (a, -h) (b, 0)

def openHalfBox (positive : Bool) (a b h : ℝ) : Set (ℝ × ℝ) :=
  Ioo a b ×ˢ (if positive then Ioo 0 h else Ioo (-h) 0)

theorem weighted_support_and_divergence
    (disc : Set E2) (s : E2 → ℝ) (gamma : ℝ → E2) (left right : ℝ)
    (G : SignedArcGeometry disc s gamma left right)
    (F : E2 → E2) (hF : ContinuousOn F disc)
    (hside : ∀ positive : Bool, ContDiffOn ℝ 1 F (signedDomain disc s positive))
    (phi : E2 → ℝ) (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ disc)
    (hdiv : ∀ positive : Bool, IntegrableOn
      (fun x => planarDivergence F x * phi x) (signedDomain disc s positive))
    (chi : E2 → ℝ) (hchi : ContDiff ℝ ∞ chi) (hbound : ∀ x, |chi x| ≤ 1) :
    let theta : E2 → ℝ := fun x => chi x * phi x
    let W : E2 → E2 := fun x => theta x • F x
    ContDiff ℝ ∞ theta ∧ HasCompactSupport theta ∧
    tsupport theta ⊆ tsupport phi ∩ tsupport chi ∧ tsupport theta ⊆ disc ∧
    Continuous W ∧
    (∀ positive : Bool, ContDiffOn ℝ 1 W (signedDomain disc s positive)) ∧
    (∀ positive : Bool, ∀ x ∈ signedDomain disc s positive,
      planarDivergence W x = inner ℝ (F x) (planarGradient theta x) +
        planarDivergence F x * theta x) ∧
    (∀ positive : Bool, IntegrableOn
      (fun x => inner ℝ (F x) (planarGradient theta x) + planarDivergence F x * theta x)
      (signedDomain disc s positive)) ∧
    (∀ x ∉ tsupport theta, theta x = 0 ∧ planarGradient theta x = 0 ∧
      W =ᶠ[𝓝 x] fun _ => 0) := by
  dsimp only
  let theta : E2 → ℝ := fun x => chi x * phi x
  let W : E2 → E2 := fun x => theta x • F x
  have htheta : ContDiff ℝ ∞ theta := hchi.mul hphi
  have hcompact : HasCompactSupport theta := hc.mul_left
  have hts : tsupport theta ⊆ tsupport phi ∩ tsupport chi :=
    subset_inter tsupport_mul_subset_right tsupport_mul_subset_left
  have htd : tsupport theta ⊆ disc := (Subset.trans hts inter_subset_left).trans hs
  have hWsupport : tsupport W ⊆ tsupport theta := tsupport_smul_subset_left theta F
  have hWcont : Continuous W := (htheta.continuous.continuousOn.smul hF).continuous_of_tsupport_subset
    G.disc_open (hWsupport.trans htd)
  have hopen (p : Bool) : IsOpen (signedDomain disc s p) := by
    cases p
    · exact G.signed_smooth.continuousOn.isOpen_inter_preimage G.disc_open isOpen_Iio
    · exact G.signed_smooth.continuousOn.isOpen_inter_preimage G.disc_open isOpen_Ioi
  have hgradzero : ∀ x ∉ tsupport theta, planarGradient theta x = 0 :=
    fun x hx => planarGradient_eq_zero_off_support theta hx
  have hint : Integrable (fun x => inner ℝ (F x) (planarGradient theta x)) := by
    have hh : tsupport (fun x => inner ℝ (F x) (planarGradient theta x)) ⊆ tsupport theta := by
      apply closure_minimal _ (isClosed_tsupport _)
      intro x hx
      by_contra hn
      exact hx (by simp [hgradzero x hn])
    have hcont : Continuous (fun x => inner ℝ (F x) (planarGradient theta x)) :=
      (hF.inner (continuous_planarGradient htheta).continuousOn).continuous_of_tsupport_subset
        G.disc_open (hh.trans htd)
    exact hcont.integrable_of_hasCompactSupport
      (hcompact.of_isClosed_subset (isClosed_tsupport _) hh)
  refine ⟨htheta, hcompact, hts, htd, hWcont, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (htheta.of_le (by simp)).contDiffOn.smul (hside p)
  · intro p x hx
    have hdF := ((hside p).contDiffAt ((hopen p).mem_nhds hx)).differentiableAt (by simp)
    have hdtheta := htheta.differentiable (by simp) x
    have hcomp (i : Fin 2) : DifferentiableAt ℝ (fun y => F y i) x := by
      exact (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).differentiableAt.comp x hdF
    change (∑ i : Fin 2, fderiv ℝ (fun y => theta y * F y i) x (coordinateVector 2 i)) = _
    simp only [fderiv_fun_mul hdtheta (hcomp _), ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
    have hpair : inner ℝ (F x) (planarGradient theta x) =
        ∑ i : Fin 2, F x i * fderiv ℝ theta x (coordinateVector 2 i) := by
      simp [planarGradient, inner_sum, inner_smul_right, coordinateVector,
        PiLp.inner_apply, Fin.sum_univ_two, EuclideanSpace.single, PiLp.single_apply]
      <;> ring
    rw [hpair]
    simp only [planarDivergence, Fin.sum_univ_two, theta]
    ring
  · intro p
    have hi := (hdiv p).bdd_mul hchi.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x)
    have hie : IntegrableOn (fun x => planarDivergence F x * theta x) (signedDomain disc s p) := by
      simpa only [IntegrableOn, theta, mul_left_comm, mul_assoc] using hi
    exact hint.integrableOn.add hie
  · intro x hx
    refine ⟨image_eq_zero_of_notMem_tsupport (f := theta) hx, hgradzero x hx, ?_⟩
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    change theta y • F y = 0
    change theta y = 0 at hy
    rw [hy, zero_smul]

theorem explicit_shear_and_measure_bridge
    (Q : E2 ≃ₗᵢ[ℝ] E2) (hQ : IsCoordinateFrame Q)
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (f : ℝ → ℝ) (a0 b0 : ℝ) (hf : ContDiffOn ℝ ∞ f (Ioo a0 b0)) :
    (∀ x : E2, coordinates x = (x 0, x 1)) ∧
    MeasurePreserving coordinates (volume : Measure E2) (volume : Measure (ℝ × ℝ)) ∧
    MeasurePreserving coordinates.symm (volume : Measure (ℝ × ℝ)) (volume : Measure E2) ∧
    (∀ z : ℝ × ℝ, unshear Q sigma f (shear Q sigma f z) = z) ∧
    (∀ x : E2, shear Q sigma f (unshear Q sigma f x) = x) ∧
    Function.Injective (shear Q sigma f) ∧
    ContDiffOn ℝ ∞ (shear Q sigma f) (Ioo a0 b0 ×ˢ (univ : Set ℝ)) ∧
    ContDiffOn ℝ ∞ (unshear Q sigma f) {x : E2 | (Q x) 0 ∈ Ioo a0 b0} ∧
    (∀ z : ℝ × ℝ, z.1 ∈ Ioo a0 b0 →
      HasFDerivAt (shear Q sigma f) (shearDerivative Q sigma f z.1) z) ∧
    (∀ x : E2, (coordinates x).1 ∈ Ioo a0 b0 →
      |(fderiv ℝ (shear Q sigma f ∘ coordinates) x).det| = 1) := by
  have hc (x : E2) : coordinates x = (x 0, x 1) := rfl
  have hcs (u v : ℝ) : (coordinates.symm (u, v)) 0 = u ∧
      (coordinates.symm (u, v)) 1 = v := by simp [coordinates]
  have hm : MeasurePreserving coordinates (volume : Measure E2) (volume : Measure (ℝ × ℝ)) := by
    exact (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  have hms : MeasurePreserving coordinates.symm (volume : Measure (ℝ × ℝ)) (volume : Measure E2) := by
    exact hm.symm coordinates.toHomeomorph.toMeasurableEquiv
  have hleft (z : ℝ × ℝ) : unshear Q sigma f (shear Q sigma f z) = z := by
    rcases hsigma with rfl | rfl <;> simp [unshear, shear, coordinates]
  have hright (x : E2) : shear Q sigma f (unshear Q sigma f x) = x := by
    apply Q.injective
    apply coordinates.injective
    rcases hsigma with rfl | rfl <;> simp [unshear, shear, coordinates]
  have hsf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1) (Ioo a0 b0 ×ˢ (univ : Set ℝ)) :=
    hf.comp contDiff_fst.contDiffOn (fun _ hz => hz.1)
  have hsm : ContDiffOn ℝ ∞ (shear Q sigma f) (Ioo a0 b0 ×ˢ (univ : Set ℝ)) := by
    exact Q.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (coordinates.symm.contDiff.comp_contDiffOn
        (contDiff_fst.contDiffOn.prodMk (hsf.add (contDiff_const.mul contDiff_snd).contDiffOn)))
  have hproj (i : Fin 2) : ContDiff ℝ ∞ (fun x : E2 => Q x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).contDiff.comp Q.toContinuousLinearEquiv.contDiff
  have hum : ContDiffOn ℝ ∞ (unshear Q sigma f) {x : E2 | Q x 0 ∈ Ioo a0 b0} := by
    exact (hproj 0).contDiffOn.prodMk
      (contDiffOn_const.mul ((hproj 1).contDiffOn.sub (hf.comp (hproj 0).contDiffOn (fun _ hx => hx))))
  have hd (z : ℝ × ℝ) (hz : z.1 ∈ Ioo a0 b0) :
      HasFDerivAt (shear Q sigma f) (shearDerivative Q sigma f z.1) z := by
    have hdf := ((hf.contDiffAt (isOpen_Ioo.mem_nhds hz)).differentiableAt (by simp)).hasDerivAt
    have hfz := hdf.comp_hasFDerivAt z (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
    have hp := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).prodMk
      (hfz.add ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).const_mul sigma))
    simpa only [shear, shearDerivative, Function.comp_def, Pi.add_apply] using!
      Q.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp z
        (coordinates.symm.toContinuousLinearMap.hasFDerivAt.comp z hp)
  refine ⟨hc, hm, hms, hleft, hright, Function.LeftInverse.injective hleft, hsm, hum, hd, ?_⟩
  intro x hx
  have hdcomp := (hd (coordinates x) hx).comp x coordinates.toContinuousLinearMap.hasFDerivAt
  rw [hdcomp.fderiv]
  change |LinearMap.det ((shearDerivative Q sigma f (coordinates x).1).comp
    coordinates.toContinuousLinearMap).toLinearMap| = 1
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
  have hsym : (∀ y : E2, Q.symm y 0 = y 0 ∧ Q.symm y 1 = y 1) ∨
      (∀ y : E2, Q.symm y 0 = y 1 ∧ Q.symm y 1 = y 0) := by
    rcases hQ with h | h
    · left
      intro y
      exact ⟨by simpa using (h (Q.symm y)).1.symm, by simpa using (h (Q.symm y)).2.symm⟩
    · right
      intro y
      have he := h (Q.symm y)
      exact ⟨by simpa using he.2.symm, by simpa using he.1.symm⟩
  have href (v : E2) : (LinearIsometryEquiv.refl ℝ E2).symm v = v := rfl
  rcases hsym with hi | hi <;> rcases hsigma with rfl | rfl <;>
    simp [LinearMap.toMatrix_apply, shearDerivative, hc, EuclideanSpace.basisFun,
      coordinates, (hi _).1, (hi _).2, href,
      EuclideanSpace.single, PiLp.single_apply]

theorem transformed_flux_divergence
    (Q : E2 ≃ₗᵢ[ℝ] E2) (hQ : IsCoordinateFrame Q)
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (f : ℝ → ℝ) (a0 b0 a b h : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Ioo a0 b0))
    (ha : a0 < a) (hab : a < b) (hb : b < b0) (hh : 0 < h)
    (W : E2 → E2) (hW : Continuous W)
    (hWside : ∀ positive : Bool, ContDiffOn ℝ 1 W
      (shear Q sigma f '' openHalfBox positive a b h)) :
    let Z := transformedFlux Q sigma f W
    (∀ positive : Bool,
      ContinuousOn (fun z => (Z z).1) (halfBox positive a b h) ∧
      ContinuousOn (fun z => (Z z).2) (halfBox positive a b h)) ∧
    (∀ positive : Bool, ∀ z ∈ openHalfBox positive a b h,
      HasFDerivAt (fun z => (Z z).1) (fderiv ℝ (fun z => (Z z).1) z) z ∧
      HasFDerivAt (fun z => (Z z).2) (fderiv ℝ (fun z => (Z z).2) z) z ∧
      fderiv ℝ (fun z => (Z z).1) z (1, 0) +
        fderiv ℝ (fun z => (Z z).2) z (0, 1) = planarDivergence W (shear Q sigma f z)) := by
  dsimp only
  obtain ⟨hc, hm, hms, hleft, hright, hinj, hsm, hum, hsd, hdet⟩ :=
    explicit_shear_and_measure_bridge Q hQ sigma hsigma f a0 b0 hf
  have hbox (p : Bool) : halfBox p a b h ⊆ Ioo a0 b0 ×ˢ (univ : Set ℝ) := by
    intro z hz
    have hz' : a ≤ z.1 ∧ z.1 ≤ b := by
      cases p <;> exact ⟨hz.1.1, hz.2.1⟩
    exact ⟨⟨ha.trans_le hz'.1, hz'.2.trans_lt hb⟩, mem_univ _⟩
  have hdfcont : ContinuousOn (deriv f) (Ioo a0 b0) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  have hproj (i : Fin 2) : Continuous (fun x : E2 => Q x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).continuous.comp Q.continuous
  constructor
  · intro p
    have hcw := hW.comp_continuousOn (hsm.continuousOn.mono (hbox p))
    have hca := (hproj 0).comp_continuousOn hcw
    have hcb := (hproj 1).comp_continuousOn hcw
    exact ⟨hca, continuousOn_const.mul (hcb.sub
      ((hdfcont.comp continuousOn_fst (fun _ hz => (hbox p hz).1)).mul hca))⟩
  · intro p z hz
    have hop : IsOpen (openHalfBox p a b h) := by
      cases p <;> exact isOpen_Ioo.prod isOpen_Ioo
    have hzu : z.1 ∈ Ioo a0 b0 := ⟨ha.trans hz.1.1, hz.1.2.trans hb⟩
    let x := shear Q sigma f z
    have hqx : Q x 0 = z.1 := by simp [x, shear, coordinates]
    have hus : IsOpen {y : E2 | Q y 0 ∈ Ioo a0 b0} :=
      isOpen_Ioo.preimage (hproj 0)
    have huc : ContinuousAt (unshear Q sigma f) x :=
      (hum.contDiffAt (hus.mem_nhds (by change Q x 0 ∈ Ioo a0 b0; rwa [hqx]))).continuousAt
    have hnb : shear Q sigma f '' openHalfBox p a b h ∈ 𝓝 x := by
      have hh := huc.preimage_mem_nhds (by simpa [x, hleft] using hop.mem_nhds hz)
      apply Filter.mem_of_superset hh
      intro y hy
      exact ⟨unshear Q sigma f y, hy, hright y⟩
    have hdW : DifferentiableAt ℝ W x :=
      ((hWside p).contDiffAt hnb).differentiableAt (by simp)
    have hdA (i : Fin 2) := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).hasFDerivAt.comp x
      (Q.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x hdW.hasFDerivAt)
    have hdZ (i : Fin 2) := (hdA i).comp z (hsd z hzu)
    have hdff : DifferentiableAt ℝ (deriv f) z.1 :=
      ((hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by simp)).contDiffAt
        (isOpen_Ioo.mem_nhds hzu)).differentiableAt (by simp)
    have hdfz := hdff.hasDerivAt.comp_hasFDerivAt z (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
    have hsecond := ((hdZ 1).sub (hdfz.mul (hdZ 0))).const_mul sigma
    have hz0 : HasFDerivAt (fun z => (transformedFlux Q sigma f W z).1)
        (fderiv ℝ (fun z => (transformedFlux Q sigma f W z).1) z) z := by
      exact (hdZ 0).differentiableAt.hasFDerivAt
    have hz1 : HasFDerivAt (fun z => (transformedFlux Q sigma f W z).2)
        (fderiv ℝ (fun z => (transformedFlux Q sigma f W z).2) z) z := by
      exact hsecond.differentiableAt.hasFDerivAt
    refine ⟨hz0, hz1, ?_⟩
    rw [hz0.unique (hdZ 0), hz1.unique hsecond]
    have hWa (i : Fin 2) := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).hasFDerivAt.comp x hdW.hasFDerivAt
    have hWcoords (i : Fin 2) : fderiv ℝ (fun y => W y i) x =
        (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).comp (fderiv ℝ W x) := by
      exact (hWa i).fderiv
    change _ = planarDivergence W x
    simp only [planarDivergence, hWcoords, Fin.sum_univ_two,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_zero, zero_mul, add_zero, sub_zero]
    have he (u v : ℝ) : coordinates.symm (u, v) =
        u • coordinateVector 2 0 + v • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinates, coordinateVector, EuclideanSpace.single]
    have hsym : (∀ y : E2, Q.symm y 0 = y 0 ∧ Q.symm y 1 = y 1) ∨
        (∀ y : E2, Q.symm y 0 = y 1 ∧ Q.symm y 1 = y 0) := by
      rcases hQ with hi | hi
      · left; intro y
        exact ⟨by simpa using (hi (Q.symm y)).1.symm, by simpa using (hi (Q.symm y)).2.symm⟩
      · right; intro y
        exact ⟨by simpa using (hi (Q.symm y)).2.symm, by simpa using (hi (Q.symm y)).1.symm⟩
    rcases hQ with hi | hi
    · have hqi (y : E2) : Q y = y := by ext i; fin_cases i <;> simp [(hi y).1, (hi y).2]
      have hqs (y : E2) : Q.symm y = y := by rw [← hqi (Q.symm y), Q.apply_symm_apply]
      simp [shearDerivative, hqi, hqs, he, map_add, map_smul, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul]
      rcases hsigma with rfl | rfl <;> ring
    · have hqs (y : E2) : Q.symm y = coordinates.symm (y 1, y 0) := by
        apply Q.injective
        apply coordinates.injective
        simp [hc, (hi _).1, (hi _).2, coordinates]
      simp [shearDerivative, (hi _).1, (hi _).2, hqs, he, map_add, map_smul,
        coordinates, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, coordinateVector,
        EuclideanSpace.single]
      have hv (u v : ℝ) : (WithLp.toLp 2 ![u, v] : E2) =
          u • coordinateVector 2 0 + v • coordinateVector 2 1 := by
        ext i
        fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
      simp only [hv, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rcases hsigma with rfl | rfl <;> simp [coordinateVector, EuclideanSpace.single] <;> ring

theorem lower_upper_half_box_adapter
    (f g : ℝ × ℝ → ℝ) (f' g' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ))
    (a b h : ℝ) (hab : a < b) (hh : 0 < h) (positive : Bool)
    (hcf : ContinuousOn f (halfBox positive a b h))
    (hcg : ContinuousOn g (halfBox positive a b h))
    (hdf : ∀ z ∈ openHalfBox positive a b h, HasFDerivAt f (f' z) z)
    (hdg : ∀ z ∈ openHalfBox positive a b h, HasFDerivAt g (g' z) z)
    (hi : IntegrableOn (fun z => f' z (1, 0) + g' z (0, 1)) (halfBox positive a b h))
    (hfaces : ∀ v ∈ (if positive then Icc 0 h else Icc (-h) 0),
      f (a, v) = 0 ∧ f (b, v) = 0)
    (houter : ∀ u ∈ Icc a b, g (u, if positive then h else -h) = 0) :
    (∫ z in halfBox positive a b h, f' z (1, 0) + g' z (0, 1)) =
      (if positive then -(∫ u in Icc a b, g (u, 0)) else ∫ u in Icc a b, g (u, 0)) := by
  have integral_zero_on (p : ℝ → ℝ) (c d : ℝ) (hcd : c ≤ d)
      (hp : ∀ x ∈ Icc c d, p x = 0) : (∫ x in c..d, p x) = 0 := by
    rw [intervalIntegral.integral_of_le hcd]
    exact setIntegral_eq_zero_of_forall_eq_zero (fun x hx => hp x ⟨hx.1.le, hx.2⟩)
  have convert_integral : (∫ u in a..b, g (u, 0)) = ∫ u in Icc a b, g (u, 0) := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact setIntegral_congr_set Ioc_ae_eq_Icc
  cases positive
  · simp only [Bool.false_eq_true, ↓reduceIte, halfBox, openHalfBox] at *
    have ht := integral_divergence_prod_Icc_of_hasFDerivAt_of_le f g f' g'
      (a, -h) (b, 0) ⟨hab.le, by linarith⟩ hcf hcg hdf hdg hi
    have hl := integral_zero_on (fun v => f (a, v)) (-h) 0 (by linarith)
      (fun v hv => (hfaces v hv).1)
    have hr := integral_zero_on (fun v => f (b, v)) (-h) 0 (by linarith)
      (fun v hv => (hfaces v hv).2)
    have ho := integral_zero_on (fun u => g (u, -h)) a b hab.le houter
    simpa only [ho, hl, hr, sub_zero, add_zero, convert_integral] using ht
  · simp only [↓reduceIte, halfBox, openHalfBox] at *
    have ht := integral_divergence_prod_Icc_of_hasFDerivAt_of_le f g f' g'
      (a, 0) (b, h) ⟨hab.le, hh.le⟩ hcf hcg hdf hdg hi
    have hl := integral_zero_on (fun v => f (a, v)) 0 h hh.le
      (fun v hv => (hfaces v hv).1)
    have hr := integral_zero_on (fun v => f (b, v)) 0 h hh.le
      (fun v hv => (hfaces v hv).2)
    have ho := integral_zero_on (fun u => g (u, h)) a b hab.le houter
    simpa only [ho, hl, hr, zero_sub, sub_zero, add_zero, convert_integral] using ht

theorem signed_normal_graph_density
    (disc : Set E2) (s : E2 → ℝ) (hs : ContDiffOn ℝ ∞ s disc)
    (hdisc : IsOpen disc) (Q : E2 ≃ₗᵢ[ℝ] E2) (hQ : IsCoordinateFrame Q)
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (f : ℝ → ℝ) (a0 b0 : ℝ) (hf : ContDiffOn ℝ ∞ f (Ioo a0 b0))
    (hgraph : ∀ u ∈ Ioo a0 b0, shear Q sigma f (u, 0) ∈ disc ∧
      s (shear Q sigma f (u, 0)) = 0)
    (htrans : ∀ u ∈ Ioo a0 b0, 0 < sigma * transverse Q s (shear Q sigma f (u, 0)))
    (W : E2 → E2) :
    ∀ u ∈ Ioo a0 b0,
      let x := shear Q sigma f (u, 0)
      let d := transverse Q s x
      let density := Real.sqrt (1 + (deriv f u)^2)
      0 < density ∧ Q (planarGradient s x) = d • coordinates.symm (-deriv f u, 1) ∧
      ‖planarGradient s x‖ = |d| * density ∧
      signedNormal s false x = Q.symm (density⁻¹ • (sigma • coordinates.symm (-deriv f u, 1))) ∧
      signedNormal s true x = -signedNormal s false x ∧
      (transformedFlux Q sigma f W (u, 0)).2 =
        inner ℝ (W x) (signedNormal s false x) * density ∧
      -(transformedFlux Q sigma f W (u, 0)).2 =
        inner ℝ (W x) (signedNormal s true x) * density := by
  intro u hu
  dsimp only
  let x := shear Q sigma f (u, 0)
  let d := transverse Q s x
  let density := Real.sqrt (1 + (deriv f u)^2)
  let n : E2 := coordinates.symm (-deriv f u, 1)
  have hdensity : 0 < density := Real.sqrt_pos.2 (by positivity)
  have hsx := ((hs.contDiffAt (hdisc.mem_nhds (hgraph u hu).1)).differentiableAt (by simp))
  have hdf := ((hf.contDiffAt (isOpen_Ioo.mem_nhds hu)).differentiableAt (by simp)).hasDerivAt
  have hcurve : HasDerivAt (fun v => shear Q sigma f (v, 0))
      (Q.symm (coordinates.symm (1, deriv f u))) u := by
    have hp := (hasDerivAt_id u).prodMk hdf
    simpa [shear, Function.comp_def] using!
      Q.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt u
        (coordinates.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt u hp)
  have hzero : fderiv ℝ s x (Q.symm (coordinates.symm (1, deriv f u))) = 0 := by
    have hh := hsx.hasFDerivAt.comp_hasDerivAt u hcurve
    have he : (fun v => s (shear Q sigma f (v, 0))) =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv using (hgraph v hv).2
    exact hh.unique ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq he)
  have hpair (v : E2) : inner ℝ (planarGradient s x) v = fderiv ℝ s x v := by
    have hv : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector, EuclideanSpace.single]
    conv_rhs => rw [hv]
    simp [planarGradient, PiLp.inner_apply, Fin.sum_univ_two, coordinateVector,
      EuclideanSpace.single, PiLp.single_apply, map_add, map_smul]
  have hcoord (i : Fin 2) : Q (planarGradient s x) i =
      fderiv ℝ s x (Q.symm (coordinateVector 2 i)) := by
    rw [← hpair]
    rw [← Q.inner_map_map, Q.apply_symm_apply]
    simp [coordinateVector, PiLp.inner_apply, EuclideanSpace.single,
      PiLp.single_apply, Fin.sum_univ_two]
  have hd : d = fderiv ℝ s x (Q.symm (coordinateVector 2 1)) := by
    change fderiv ℝ (s ∘ Q.symm) (Q x) (coordinateVector 2 1) = _
    have hss : DifferentiableAt ℝ s (Q.symm (Q x)) := by simpa using hsx
    rw [fderiv_comp (Q x) hss Q.symm.toContinuousLinearEquiv.differentiableAt]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv,
      Q.symm_apply_apply]
    have hqi : HasFDerivAt (fun y : E2 => Q.symm y)
        Q.symm.toContinuousLinearEquiv.toContinuousLinearMap (Q x) := by
      simpa only using! Q.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt (x := Q x)
    rw [hqi.fderiv]
    rfl
  have hsecond : Q (planarGradient s x) 1 = d := (hcoord 1).trans hd.symm
  have hfirst : Q (planarGradient s x) 0 = -deriv f u * d := by
    have hv : coordinates.symm (1, deriv f u) = coordinateVector 2 0 +
        deriv f u • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinates, coordinateVector, EuclideanSpace.single]
    rw [hv, map_add, map_smul, map_add, map_smul, smul_eq_mul, ← hd, ← hcoord 0] at hzero
    linarith
  have hgrad : Q (planarGradient s x) = d • n := by
    ext i
    fin_cases i <;> simp [n, coordinates, hfirst, hsecond, mul_comm]
  have hnormn : ‖n‖ = density := by
    rw [EuclideanSpace.norm_eq]
    simp [n, coordinates, Fin.sum_univ_two, density, add_comm]
  have hnorm : ‖planarGradient s x‖ = |d| * density := by
    rw [← Q.norm_map, hgrad, norm_smul, Real.norm_eq_abs, hnormn]
  have hsign : 0 < sigma * d := htrans u hu
  have hdne : d ≠ 0 := by intro he; simp [he] at hsign
  have hratio : (|d| * density)⁻¹ * d = density⁻¹ * sigma := by
    rcases hsigma with rfl | rfl
    · have hp : 0 < d := by simpa using hsign
      rw [abs_of_pos hp]
      field_simp
    · have hn : d < 0 := by linarith
      rw [abs_of_neg hn]
      field_simp
      <;> ring
  have hnormal : signedNormal s false x = Q.symm (density⁻¹ • (sigma • n)) := by
    apply Q.injective
    simp only [signedNormal, Bool.false_eq_true, ↓reduceIte, map_smul, Q.apply_symm_apply]
    rw [hgrad, hnorm, smul_smul, smul_smul, hratio]
  have hopposite : signedNormal s true x = -signedNormal s false x := rfl
  have hflux : (transformedFlux Q sigma f W (u, 0)).2 =
      inner ℝ (W x) (signedNormal s false x) * density := by
    rw [hnormal, ← Q.inner_map_map, Q.apply_symm_apply]
    simp only [inner_smul_right, real_inner_smul_right]
    have hi : inner ℝ (Q (W x)) n = (Q (W x)) 1 - deriv f u * (Q (W x)) 0 := by
      simp [n, coordinates, PiLp.inner_apply, Fin.sum_univ_two]
      ring
    rw [hi]
    change sigma * ((Q (W x)) 1 - deriv f u * (Q (W x)) 0) = _
    field_simp
  refine ⟨hdensity, hgrad, hnorm, hnormal, hopposite, hflux, ?_⟩
  rw [hopposite, inner_neg_right, neg_mul, ← hflux]

theorem original_clock_derivative_speed
    (Q : E2 ≃ₗᵢ[ℝ] E2) (hQ : IsCoordinateFrame Q)
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (f : ℝ → ℝ) (gamma : ℝ → E2) (a0 b0 j0 j1 : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Ioo a0 b0))
    (hgamma : ContDiffOn ℝ ∞ gamma (Ioo j0 j1))
    (hclock : ∀ t ∈ Ioo j0 j1, (Q (gamma t)) 0 ∈ Ioo a0 b0)
    (hgraph : ∀ t ∈ Ioo j0 j1,
      gamma t = shear Q sigma f ((Q (gamma t)) 0, 0)) :
    let kappa : ℝ → ℝ := fun t => (Q (gamma t)) 0
    ∀ t ∈ Ioo j0 j1,
      coordinates (Q (fderiv ℝ gamma t 1)) =
        (deriv kappa t, deriv kappa t * deriv f (kappa t)) ∧
      ‖fderiv ℝ gamma t 1‖ = |deriv kappa t| * Real.sqrt (1 + (deriv f (kappa t))^2) ∧
      |(fderiv ℝ kappa t).det| = |deriv kappa t| := by
  dsimp only
  let kappa : ℝ → ℝ := fun t => (Q (gamma t)) 0
  intro t ht
  have hg := (hgamma.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
  have hp (i : Fin 2) := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).hasFDerivAt.comp t
    (Q.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp t hg.hasFDerivAt)
  have hk : HasDerivAt kappa ((Q (fderiv ℝ gamma t 1)) 0) t := by
    simpa [kappa] using! (hp 0).hasDerivAt
  have hf' := (hf.contDiffAt (isOpen_Ioo.mem_nhds (hclock t ht))).differentiableAt (by simp)
  have heq : (fun v => (Q (gamma v)) 1) =ᶠ[𝓝 t] (fun v => f (kappa v)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with v hv
    have hgv := congrArg (fun x : E2 => (Q x) 1) (hgraph v hv)
    simpa [shear, coordinates, kappa] using hgv
  have hsecond : (Q (fderiv ℝ gamma t 1)) 1 = deriv kappa t * deriv f (kappa t) := by
    have hd := ((hf'.hasDerivAt).comp t hk).congr_of_eventuallyEq heq
    have hv := (hp 1).hasDerivAt.unique hd
    change (Q (fderiv ℝ gamma t 1)) 1 = deriv f (kappa t) *
      (Q (fderiv ℝ gamma t 1)) 0 at hv
    rw [← hk.deriv, mul_comm] at hv
    exact hv
  have hfirst : (Q (fderiv ℝ gamma t 1)) 0 = deriv kappa t := hk.deriv.symm
  refine ⟨?_, ?_, ?_⟩
  · change ((Q (fderiv ℝ gamma t 1)) 0, (Q (fderiv ℝ gamma t 1)) 1) = _
    rw [hfirst, hsecond]
  · rw [← Q.norm_map (fderiv ℝ gamma t 1), EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, hfirst, hsecond]
    rw [show (deriv kappa t)^2 + (deriv kappa t * deriv f (kappa t))^2 =
      (deriv kappa t)^2 * (1 + (deriv f (kappa t))^2) by ring]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  · have he : (fderiv ℝ kappa t).toLinearMap = deriv kappa t • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
      apply LinearMap.ext_ring
      change (fderiv ℝ kappa t) 1 = deriv kappa t * 1
      exact (mul_one _).symm
    change |(fderiv ℝ kappa t).toLinearMap.det| = _
    rw [he, LinearMap.det_smul]
    simp [kappa]

structure SignedGraphChart (disc : Set E2) (s : E2 → ℝ)
    (gamma : ℝ → E2) (left right : ℝ) where
  center : E2
  center_mem : center ∈ disc
  center_zero : s center = 0
  Q : E2 ≃ₗᵢ[ℝ] E2
  frame : IsCoordinateFrame Q
  sigma : ℝ
  sigma_choice : sigma = 1 ∨ sigma = -1
  a0 : ℝ
  b0 : ℝ
  interval_nonempty : a0 < b0
  f : ℝ → ℝ
  graph_smooth : ContDiffOn ℝ ∞ f (Ioo a0 b0)
  h0 : ℝ
  height_positive : 0 < h0
  omega_open : IsOpen (shear Q sigma f '' (Ioo a0 b0 ×ˢ Ioo (-h0) h0))
  omega_subset : shear Q sigma f '' (Ioo a0 b0 ×ˢ Ioo (-h0) h0) ⊆ disc
  graph_zero : ∀ u ∈ Ioo a0 b0, s (shear Q sigma f (u, 0)) = 0
  level_zero_exact :
    {x ∈ shear Q sigma f '' (Ioo a0 b0 ×ˢ Ioo (-h0) h0) | s x = 0} =
      (fun u => shear Q sigma f (u, 0)) '' Ioo a0 b0
  strict_signs : ∀ z ∈ Ioo a0 b0 ×ˢ Ioo (-h0) h0,
    (s (shear Q sigma f z) < 0 ↔ z.2 < 0) ∧
    (0 < s (shear Q sigma f z) ↔ 0 < z.2)
  transverse_positive : ∀ z ∈ Ioo a0 b0 ×ˢ Ioo (-h0) h0,
    0 < sigma * transverse Q s (shear Q sigma f z)
  strict_side_image : ∀ positive : Bool,
    signedDomain disc s positive ∩ (shear Q sigma f '' (Ioo a0 b0 ×ˢ Ioo (-h0) h0)) =
      shear Q sigma f '' (Ioo a0 b0 ×ˢ (if positive then Ioo 0 h0 else Ioo (-h0) 0))
  shear_smooth : ContDiffOn ℝ ∞ (shear Q sigma f) (Ioo a0 b0 ×ˢ Ioo (-h0) h0)
  inverse_smooth : ContDiffOn ℝ ∞ (unshear Q sigma f)
    (shear Q sigma f '' (Ioo a0 b0 ×ˢ Ioo (-h0) h0))
  chart_derivative : ∀ z ∈ Ioo a0 b0 ×ˢ Ioo (-h0) h0,
    HasFDerivAt (shear Q sigma f) (shearDerivative Q sigma f z.1) z
  inverse_left : ∀ z : ℝ × ℝ, unshear Q sigma f (shear Q sigma f z) = z
  inverse_right : ∀ x : E2, shear Q sigma f (unshear Q sigma f x) = x
  j0 : ℝ
  j1 : ℝ
  parameter_nonempty : j0 < j1
  parameter_closure : Icc j0 j1 ⊆ Ioo left right
  clock_image : (fun t => (Q (gamma t)) 0) '' Ioo j0 j1 = Ioo a0 b0
  gamma_graph : ∀ t ∈ Ioo j0 j1, gamma t = shear Q sigma f ((Q (gamma t)) 0, 0)
  original_parameter_exclusion : ∀ t ∈ Ioo left right,
    gamma t ∈ shear Q sigma f '' (Ioo a0 b0 ×ˢ Ioo (-h0) h0) → t ∈ Ioo j0 j1
  inverseClock : ℝ → ℝ
  inverseClock_mem : ∀ u ∈ Ioo a0 b0, inverseClock u ∈ Ioo j0 j1
  inverseClock_left : ∀ t ∈ Ioo j0 j1, inverseClock ((Q (gamma t)) 0) = t
  inverseClock_right : ∀ u ∈ Ioo a0 b0, (Q (gamma (inverseClock u))) 0 = u
  window : Set E2
  window_open : IsOpen window
  center_in_window : center ∈ window
  window_precompact : IsCompact (closure window)
  window_closure_subset : closure window ⊆
    shear Q sigma f '' (Ioo a0 b0 ×ˢ Ioo (-h0) h0)

theorem signed_graph_chart_from_original_geometry
    (disc : Set E2) (s : E2 → ℝ) (gamma : ℝ → E2) (left right : ℝ)
    (G : SignedArcGeometry disc s gamma left right)
    (q : E2) (hq : q ∈ disc) (hz : s q = 0) :
    ∃ C : SignedGraphChart disc s gamma left right, C.center = q := by
  classical
  have hFrame (disc : Set E2) (s : E2 → ℝ) (gamma : ℝ → E2) (left right : ℝ)
      (G : SignedArcGeometry disc s gamma left right)
      (q : E2) (hq : q ∈ disc) (hz : s q = 0) :
      ∃ Q : E2 ≃ₗᵢ[ℝ] E2, IsCoordinateFrame Q ∧ transverse Q s q ≠ 0 := by
    classical
    have hd : DifferentiableAt ℝ s q :=
      (G.signed_smooth.contDiffAt (G.disc_open.mem_nhds hq)).differentiableAt (by simp)
    by_cases h1 : fderiv ℝ s q (coordinateVector 2 1) = 0
    · have h0 : fderiv ℝ s q (coordinateVector 2 0) ≠ 0 := by
        intro h0
        apply G.signed_regular q hq hz
        change (∑ i : Fin 2, fderiv ℝ s q (coordinateVector 2 i) • coordinateVector 2 i) = 0
        apply Finset.sum_eq_zero
        intro i hi
        fin_cases i
        · change fderiv ℝ s q (coordinateVector 2 0) • coordinateVector 2 0 = 0
          rw [h0, zero_smul]
        · change fderiv ℝ s q (coordinateVector 2 1) • coordinateVector 2 1 = 0
          rw [h1, zero_smul]
      let Q : E2 ≃ₗᵢ[ℝ] E2 := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)
      have hQ : IsCoordinateFrame Q := by
        right
        intro x
        constructor <;> simp [Q, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
      have hv : Q.symm (coordinateVector 2 1) = coordinateVector 2 0 := by
        ext i
        fin_cases i <;> simp [Q, LinearIsometryEquiv.piLpCongrLeft_symm,
          LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', coordinateVector]
      have hds : HasFDerivAt s (fderiv ℝ s q) (Q.symm (Q q)) := by
        simpa only [LinearIsometryEquiv.symm_apply_apply] using hd.hasFDerivAt
      have hcomp := hds.comp (Q q) Q.symm.toContinuousLinearEquiv.hasFDerivAt
      refine ⟨Q, hQ, ?_⟩
      change (fderiv ℝ (s ∘ Q.symm) (Q q)) (coordinateVector 2 1) ≠ 0
      rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
      change fderiv ℝ s q (Q.symm (coordinateVector 2 1)) ≠ 0
      rw [hv]
      exact h0
    · refine ⟨LinearIsometryEquiv.refl ℝ E2, Or.inl (fun x => ⟨rfl, rfl⟩), ?_⟩
      exact h1
  have hGraph (disc : Set E2) (s : E2 → ℝ) (gamma : ℝ → E2) (left right : ℝ)
      (G : SignedArcGeometry disc s gamma left right)
      (t : ℝ) (ht : t ∈ Ioo left right) (hq : gamma t ∈ disc)
      (Q : E2 ≃ₗᵢ[ℝ] E2) (hv : transverse Q s (gamma t) ≠ 0) :
      ∃ (j0 j1 a b : ℝ) (f eta : ℝ → ℝ),
        t ∈ Ioo j0 j1 ∧ Icc j0 j1 ⊆ Ioo left right ∧ a < b ∧
        (fun u => (Q (gamma u)) 0) '' Ioo j0 j1 = Ioo a b ∧
        ContDiffOn ℝ ∞ f (Ioo a b) ∧ ContDiffOn ℝ ∞ eta (Ioo a b) ∧
        (∀ u ∈ Ioo a b, eta u ∈ Ioo j0 j1) ∧
        (∀ v ∈ Ioo j0 j1, eta ((Q (gamma v)) 0) = v) ∧
        (∀ u ∈ Ioo a b, (Q (gamma (eta u))) 0 = u) ∧
        (∀ u ∈ Ioo a b, shear Q 1 f (u, 0) ∈ disc ∧ s (shear Q 1 f (u, 0)) = 0) ∧
        (∀ v ∈ Ioo j0 j1, gamma v = shear Q 1 f ((Q (gamma v)) 0, 0)) := by
    have hregularClock (disc : Set E2) (s : E2 → ℝ) (gamma : ℝ → E2) (left right : ℝ)
        (G : SignedArcGeometry disc s gamma left right)
        (t : ℝ) (ht : t ∈ Ioo left right) (hq : gamma t ∈ disc)
        (Q : E2 ≃ₗᵢ[ℝ] E2) (hv : transverse Q s (gamma t) ≠ 0) :
        deriv (fun u => (Q (gamma u)) 0) t ≠ 0 := by
      let kappa : ℝ → ℝ := fun u => (Q (gamma u)) 0
      have hgamma : DifferentiableAt ℝ gamma t :=
        (G.arc_smooth.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
      have hs : DifferentiableAt ℝ s (gamma t) :=
        (G.signed_smooth.contDiffAt (G.disc_open.mem_nhds hq)).differentiableAt (by simp)
      have hlevel : (s ∘ gamma) =ᶠ[𝓝 t] fun _ => 0 := by
        have hmem : ∀ᶠ u in 𝓝 t, gamma u ∈ disc :=
          hgamma.continuousAt.preimage_mem_nhds (G.disc_open.mem_nhds hq)
        filter_upwards [isOpen_Ioo.mem_nhds ht, hmem] with u hu hgu
        have hh : gamma u ∈ {x ∈ disc | s x = 0} := by
          rw [G.zero_set_exact]
          exact ⟨⟨u, hu, rfl⟩, hgu⟩
        exact hh.2
      have htangent : fderiv ℝ s (gamma t) (fderiv ℝ gamma t 1) = 0 := by
        have hh := hs.hasFDerivAt.comp t hgamma.hasFDerivAt
        have hzero := (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) t).congr_of_eventuallyEq hlevel
        have heq := hh.unique hzero
        simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] using
          congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) heq
      have hQc := Q.toContinuousLinearEquiv.hasFDerivAt.comp t hgamma.hasFDerivAt
      have hfirst : HasFDerivAt (fun u => (Q (gamma u)) 0)
          ((EuclideanSpace.proj 0).comp (Q.toContinuousLinearEquiv.toContinuousLinearMap.comp
            (fderiv ℝ gamma t))) t := by
        exact (EuclideanSpace.proj 0).hasFDerivAt.comp t hQc
      intro hkzero
      have hw0 : (Q (fderiv ℝ gamma t 1)) 0 = 0 := by
        have h := hfirst.hasDerivAt.deriv
        have heq : deriv (fun u => (Q (gamma u)) 0) t = (Q (fderiv ℝ gamma t 1)) 0 := h
        exact heq.symm.trans hkzero
      let w := Q (fderiv ℝ gamma t 1)
      have hwform : w = w 1 • coordinateVector 2 1 := by
        ext i
        fin_cases i
        · change (Q (fderiv ℝ gamma t 1)) 0 = (w 1 • coordinateVector 2 1) 0
          rw [hw0]
          simp [coordinateVector]
        · simp [coordinateVector]
      have hsw : fderiv ℝ (s ∘ Q.symm) (Q (gamma t)) w = 0 := by
        have hd : HasFDerivAt s (fderiv ℝ s (gamma t)) (Q.symm (Q (gamma t))) := by
          simpa only [LinearIsometryEquiv.symm_apply_apply] using hs.hasFDerivAt
        rw [(hd.comp (Q (gamma t)) Q.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv]
        change fderiv ℝ s (gamma t) (Q.symm (Q (fderiv ℝ gamma t 1))) = 0
        rw [Q.symm_apply_apply]
        exact htangent
      have hw1 : w 1 = 0 := by
        rw [hwform, map_smul] at hsw
        change w 1 * transverse Q s (gamma t) = 0 at hsw
        exact (mul_eq_zero.mp hsw).resolve_right hv
      have hwzero : w = 0 := by
        rw [hwform, hw1, zero_smul]
      apply G.arc_regular t ht
      exact Q.injective (hwzero.trans Q.map_zero.symm)
    have hclockInterval (kappa : ℝ → ℝ) (left right t : ℝ)
        (hk : ContDiffOn ℝ ∞ kappa (Ioo left right))
        (ht : t ∈ Ioo left right) (hkt : deriv kappa t ≠ 0) :
        ∃ (j0 j1 a b : ℝ) (eta : ℝ → ℝ),
          t ∈ Ioo j0 j1 ∧ Icc j0 j1 ⊆ Ioo left right ∧ a < b ∧
          kappa '' Ioo j0 j1 = Ioo a b ∧
          (∀ u ∈ Ioo a b, eta u ∈ Ioo j0 j1) ∧
          (∀ v ∈ Ioo j0 j1, eta (kappa v) = v) ∧
          (∀ u ∈ Ioo a b, kappa (eta u) = u) ∧
          ContDiffOn ℝ ∞ eta (Ioo a b) := by
      have hktSmooth : ContDiffAt ℝ ∞ kappa t := hk.contDiffAt (isOpen_Ioo.mem_nhds ht)
      have hktD : HasDerivAt kappa (deriv kappa t) t :=
        (hktSmooth.differentiableAt (by simp)).hasDerivAt
      let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (.mk0 (deriv kappa t) hkt)
      have hF : HasFDerivAt kappa e.toContinuousLinearMap t := hktD.hasFDerivAt_equiv hkt
      let R := hktSmooth.toOpenPartialHomeomorph kappa hF (by simp)
      have hR : (R : ℝ → ℝ) = kappa := rfl
      have htR : t ∈ R.source := hktSmooth.mem_toOpenPartialHomeomorph_source hF (by simp)
      have hD : ContinuousAt (fun x => deriv kappa x) t := by
        change ContinuousAt (fun x => fderiv ℝ kappa x (1 : ℝ)) t
        exact ((hk.continuousOn_fderiv_of_isOpen isOpen_Ioo (by simp)).continuousAt
          (isOpen_Ioo.mem_nhds ht)).clm_apply continuousAt_const
      have hnonzero : ∀ᶠ x in 𝓝 t, deriv kappa x ≠ 0 := hD.eventually_ne hkt
      obtain ⟨l, r, hlr, hsmall⟩ := mem_nhds_iff_exists_Ioo_subset.mp
        (inter_mem (inter_mem (R.open_source.mem_nhds htR) (isOpen_Ioo.mem_nhds ht)) hnonzero)
      let j0 := (l+t)/2
      let j1 := (t+r)/2
      have hjt : t ∈ Ioo j0 j1 := ⟨by dsimp [j0]; linarith [hlr.1], by dsimp [j1]; linarith [hlr.2]⟩
      have hj : j0 < j1 := hjt.1.trans hjt.2
      have hsub : Icc j0 j1 ⊆ Ioo l r := by
        intro u hu
        have hlow : (l+t)/2 ≤ u := hu.1
        have hupp : u ≤ (t+r)/2 := hu.2
        constructor <;> linarith [hlr.1, hlr.2]
      have hsource : Icc j0 j1 ⊆ R.source := fun u hu => (hsmall (hsub hu)).1.1
      have hparameters : Icc j0 j1 ⊆ Ioo left right := fun u hu => (hsmall (hsub hu)).1.2
      have hnonzeroJ : ∀ u ∈ Icc j0 j1, deriv kappa u ≠ 0 := fun u hu => (hsmall (hsub hu)).2
      have hcontinuous : ContinuousOn kappa (Icc j0 j1) := hk.continuousOn.mono hparameters
      have hinjective : InjOn kappa (Icc j0 j1) := by
        rw [← hR]
        exact R.injOn.mono hsource
      have himage : ∃ a b : ℝ, a < b ∧ kappa '' Ioo j0 j1 = Ioo a b := by
        rcases hcontinuous.strictMonoOn_of_injOn_Icc' hj.le hinjective with hmono | hanti
        · exact ⟨kappa j0, kappa j1,
            hmono (left_mem_Icc.mpr hj.le) (right_mem_Icc.mpr hj.le) hj,
            hcontinuous.image_Ioo_of_strictMonoOn hj.le hmono⟩
        · exact ⟨kappa j1, kappa j0,
            hanti (left_mem_Icc.mpr hj.le) (right_mem_Icc.mpr hj.le) hj,
            hcontinuous.image_Ioo_of_strictAntiOn hj.le hanti⟩
      obtain ⟨a, b, hab, himage⟩ := himage
      let eta : ℝ → ℝ := R.symm
      have hleft : ∀ v ∈ Ioo j0 j1, eta (kappa v) = v := by
        intro v hv
        rw [← hR]
        exact R.left_inv (hsource (Ioo_subset_Icc_self hv))
      have hmem : ∀ u ∈ Ioo a b, eta u ∈ Ioo j0 j1 := by
        intro u hu
        rw [← himage] at hu
        obtain ⟨v, hv, rfl⟩ := hu
        rw [hleft v hv]
        exact hv
      have htarget : ∀ u ∈ Ioo a b, u ∈ R.target := by
        intro u hu
        rw [← himage] at hu
        obtain ⟨v, hv, rfl⟩ := hu
        rw [← hR]
        exact R.map_source (hsource (Ioo_subset_Icc_self hv))
      refine ⟨j0, j1, a, b, eta, hjt, hparameters, hab, himage, hmem, hleft, ?_, ?_⟩
      · intro u hu
        rw [← hR]
        exact R.right_inv (htarget u hu)
      · intro u hu
        have hEtaJ := hmem u hu
        have hEtaP : eta u ∈ Ioo left right := hparameters (Ioo_subset_Icc_self hEtaJ)
        have hsm : ContDiffAt ℝ ∞ kappa (eta u) :=
          hk.contDiffAt (isOpen_Ioo.mem_nhds hEtaP)
        have hd : HasDerivAt R (deriv kappa (eta u)) (R.symm u) := by
          rw [hR]
          exact (hsm.differentiableAt (by simp)).hasDerivAt
        have hsmR : ContDiffAt ℝ ∞ R (R.symm u) := by rw [hR]; exact hsm
        exact (R.contDiffAt_symm_deriv (hnonzeroJ _ (Ioo_subset_Icc_self hEtaJ))
          (htarget u hu) hd hsmR).contDiffWithinAt
    let kappa : ℝ → ℝ := fun u => (Q (gamma u)) 0
    have hk : ContDiffOn ℝ ∞ kappa (Ioo left right) := by
      exact ((EuclideanSpace.proj 0).contDiff.comp_contDiffOn
        (Q.toContinuousLinearEquiv.contDiff.comp_contDiffOn G.arc_smooth))
    have hg : ContinuousAt gamma t :=
      G.arc_smooth.continuousOn.continuousAt (isOpen_Ioo.mem_nhds ht)
    obtain ⟨l, r, htr, hsmall⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (inter_mem (isOpen_Ioo.mem_nhds ht)
        (hg.preimage_mem_nhds (G.disc_open.mem_nhds hq)))
    have hLR : Ioo l r ⊆ Ioo left right := fun u hu => (hsmall hu).1
    have hDisc : ∀ u ∈ Ioo l r, gamma u ∈ disc := fun u hu => (hsmall hu).2
    have hkt : deriv kappa t ≠ 0 := hregularClock disc s gamma left right G t ht hq Q hv
    obtain ⟨j0, j1, a, b, eta, hjt, hJlr, hab, himage, hmem, hleft, hright, heta⟩ :=
      hclockInterval kappa l r t (hk.mono hLR) htr hkt
    have hJLR : Icc j0 j1 ⊆ Ioo left right := hJlr.trans hLR
    have hJDisc : ∀ u ∈ Icc j0 j1, gamma u ∈ disc := fun u hu => hDisc u (hJlr hu)
    let f : ℝ → ℝ := fun u => (Q (gamma (eta u))) 1
    have hf : ContDiffOn ℝ ∞ f (Ioo a b) := by
      exact (EuclideanSpace.proj 1).contDiff.comp_contDiffOn
        (Q.toContinuousLinearEquiv.contDiff.comp_contDiffOn
          (G.arc_smooth.comp heta (fun u hu => hJLR (Ioo_subset_Icc_self (hmem u hu)))))
    have hcoordinates : ∀ x : E2, coordinates x = (x 0, x 1) := by
      intro x
      rfl
    have hgraph : ∀ u ∈ Ioo a b, shear Q 1 f (u, 0) = gamma (eta u) := by
      intro u hu
      apply Q.injective
      dsimp only [shear]
      rw [Q.apply_symm_apply]
      change coordinates.symm (u, f u + 1*0) = Q (gamma (eta u))
      apply coordinates.injective
      rw [coordinates.apply_symm_apply, hcoordinates]
      apply Prod.ext
      · exact (hright u hu).symm
      · simp only [mul_zero, add_zero]; rfl
    refine ⟨j0, j1, a, b, f, eta, hjt, hJLR, hab, himage, hf, heta,
      hmem, hleft, hright, ?_, ?_⟩
    · intro u hu
      rw [hgraph u hu]
      have huDisc := hJDisc _ (Ioo_subset_Icc_self (hmem u hu))
      refine ⟨huDisc, ?_⟩
      have hzero : gamma (eta u) ∈ {x ∈ disc | s x = 0} := by
        rw [G.zero_set_exact]
        exact ⟨⟨eta u, hJLR (Ioo_subset_Icc_self (hmem u hu)), rfl⟩, huDisc⟩
      exact hzero.2
    · intro v hv
      have hvImage : kappa v ∈ Ioo a b := by rw [← himage]; exact mem_image_of_mem _ hv
      rw [hgraph _ hvImage, hleft v hv]
  have hExclusion (disc : Set E2) (s : E2 → ℝ) (gamma : ℝ → E2) (left right : ℝ)
      (G : SignedArcGeometry disc s gamma left right)
      (t : ℝ) (ht : t ∈ Ioo left right)
      (J : Set ℝ) (hJ : IsOpen J) (htJ : t ∈ J) :
      ∃ V : Set E2, IsOpen V ∧ gamma t ∈ V ∧
        ∀ u ∈ Ioo left right, gamma u ∈ V → u ∈ J := by
    have hopen : IsOpen ((Subtype.val : Ioo left right → ℝ) ⁻¹' J) :=
      hJ.preimage continuous_subtype_val
    obtain ⟨V, hV, heq⟩ := G.arc_embedding.isInducing.isOpen_iff.mp hopen
    refine ⟨V, hV, ?_, ?_⟩
    · have hh : (⟨t, ht⟩ : Ioo left right) ∈ Subtype.val ⁻¹' J := htJ
      rw [← heq] at hh
      exact hh
    · intro u hu hgu
      have hh : (⟨u, hu⟩ : Ioo left right) ∈
          (fun v : Ioo left right => gamma v) ⁻¹' V := hgu
      rw [heq] at hh
      exact hh
  have hOrientation (disc : Set E2) (s : E2 → ℝ) (hdisc : IsOpen disc)
      (hs : ContDiffOn ℝ ∞ s disc) (q : E2) (hq : q ∈ disc)
      (Q : E2 ≃ₗᵢ[ℝ] E2) (hv : transverse Q s q ≠ 0) :
      ∃ (sigma : ℝ) (V : Set E2), (sigma = 1 ∨ sigma = -1) ∧
        IsOpen V ∧ q ∈ V ∧ V ⊆ disc ∧
        ∀ x ∈ V, 0 < sigma * transverse Q s x := by
    have heq : ∀ x ∈ disc,
        transverse Q s x = fderiv ℝ s x (Q.symm (coordinateVector 2 1)) := by
      intro x hx
      have hd : HasFDerivAt s (fderiv ℝ s x) (Q.symm (Q x)) := by
        simpa only [Q.symm_apply_apply] using
          (hs.contDiffAt (hdisc.mem_nhds hx)).differentiableAt (by simp) |>.hasFDerivAt
      have hh := hd.comp (Q x) Q.symm.toContinuousLinearEquiv.hasFDerivAt
      change fderiv ℝ (s ∘ Q.symm) (Q x) (coordinateVector 2 1) = _
      rw [hh.fderiv]
      rfl
    have hcont : ContinuousOn (transverse Q s) disc := by
      have hh := (hs.continuousOn_fderiv_of_isOpen hdisc (by simp)).clm_apply
        (continuousOn_const (c := Q.symm (coordinateVector 2 1)))
      exact hh.congr heq
    have hsig : ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧ 0 < sigma * transverse Q s q := by
      rcases lt_or_gt_of_ne hv with hneg | hpos
      · exact ⟨-1, Or.inr rfl, by linarith⟩
      · exact ⟨1, Or.inl rfl, by simpa using hpos⟩
    obtain ⟨sigma, hchoice, hpos⟩ := hsig
    let V : Set E2 := disc ∩ (fun x => sigma * transverse Q s x) ⁻¹' Ioi 0
    have hV : IsOpen V := (continuousOn_const.mul hcont).isOpen_inter_preimage hdisc isOpen_Ioi
    exact ⟨sigma, V, hchoice, hV, ⟨hq, hpos⟩, inter_subset_left, fun x hx => hx.2⟩
  have hUniform (Q : E2 ≃ₗᵢ[ℝ] E2) (sigma : ℝ) (f : ℝ → ℝ)
      (A B a b : ℝ) (hab : a ≤ b) (ha : A < a) (hb : b < B)
      (hT : ContinuousOn (shear Q sigma f) (Ioo A B ×ˢ (univ : Set ℝ)))
      (V : Set E2) (hV : IsOpen V)
      (hgraph : ∀ u ∈ Icc a b, shear Q sigma f (u, 0) ∈ V) :
      ∃ h : ℝ, 0 < h ∧ shear Q sigma f '' (Icc a b ×ˢ Ioo (-h) h) ⊆ V := by
    let N := (Ioo A B ×ˢ (univ : Set ℝ)) ∩ shear Q sigma f ⁻¹' V
    have hN : IsOpen N := hT.isOpen_inter_preimage (isOpen_Ioo.prod isOpen_univ) hV
    have hsegment : Icc a b ×ˢ ({0} : Set ℝ) ⊆ N := by
      rintro ⟨u, v⟩ ⟨hu, hv⟩
      have hv0 : v = 0 := hv
      subst v
      exact ⟨⟨⟨ha.trans_le hu.1, hu.2.trans_lt hb⟩, mem_univ _⟩, hgraph u hu⟩
    obtain ⟨X, Y, hX, hY, hKX, h0Y, hXY⟩ :=
      generalized_tube_lemma isCompact_Icc isCompact_singleton hN hsegment
    have hz : (0 : ℝ) ∈ Y := h0Y (mem_singleton 0)
    obtain ⟨l, r, hlr, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hY.mem_nhds hz)
    let h : ℝ := min (-l) r / 2
    have hh : 0 < h := by dsimp [h]; exact div_pos (lt_min (neg_pos.mpr hlr.1) hlr.2) (by norm_num)
    have hhl : h < -l := by
      have hp : 0 < min (-l) r := lt_min (neg_pos.mpr hlr.1) hlr.2
      have hle := min_le_left (-l) r
      dsimp [h]
      linarith
    have hhr : h < r := by
      have hp : 0 < min (-l) r := lt_min (neg_pos.mpr hlr.1) hlr.2
      have hle := min_le_right (-l) r
      dsimp [h]
      linarith
    refine ⟨h, hh, ?_⟩
    rintro x ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    have hvY : v ∈ Y := hsub ⟨by linarith [hv.1], hv.2.trans hhr⟩
    exact (hXY ⟨hKX hu, hvY⟩).2
  have hSigns (disc : Set E2) (s : E2 → ℝ) (hdisc : IsOpen disc)
      (hs : ContDiffOn ℝ ∞ s disc)
      (Q : E2 ≃ₗᵢ[ℝ] E2) (sigma : ℝ) (f : ℝ → ℝ) (A B H : ℝ)
      (hH : 0 < H)
      (hsub : shear Q sigma f '' (Ioo A B ×ˢ Ioo (-H) H) ⊆ disc)
      (hpos : ∀ z ∈ Ioo A B ×ˢ Ioo (-H) H,
        0 < sigma * transverse Q s (shear Q sigma f z))
      (hzero : ∀ u ∈ Ioo A B, s (shear Q sigma f (u, 0)) = 0) :
      ∀ z ∈ Ioo A B ×ˢ Ioo (-H) H,
        (s (shear Q sigma f z) < 0 ↔ z.2 < 0) ∧
        (0 < s (shear Q sigma f z) ↔ 0 < z.2) := by
    have hvertical : ∀ u ∈ Ioo A B, ∀ v ∈ Ioo (-H) H,
        HasDerivAt (fun w => s (shear Q sigma f (u, w)))
          (sigma * transverse Q s (shear Q sigma f (u, v))) v := by
      intro u hu v hv
      have hx : shear Q sigma f (u, v) ∈ disc := hsub (mem_image_of_mem _ ⟨hu, hv⟩)
      have hd : HasFDerivAt (s ∘ Q.symm)
          ((fderiv ℝ s (shear Q sigma f (u, v))).comp
            Q.symm.toContinuousLinearEquiv.toContinuousLinearMap)
          (Q (shear Q sigma f (u, v))) := by
        have hh : HasFDerivAt s (fderiv ℝ s (shear Q sigma f (u, v)))
            (Q.symm (Q (shear Q sigma f (u, v)))) := by
          simpa only [Q.symm_apply_apply] using
            (hs.contDiffAt (hdisc.mem_nhds hx)).differentiableAt (by simp) |>.hasFDerivAt
        exact hh.comp _ Q.symm.toContinuousLinearEquiv.hasFDerivAt
      have hQpoint : Q (shear Q sigma f (u, v)) = coordinates.symm (u, f u + sigma*v) := by
        dsimp only [shear]
        exact Q.apply_symm_apply _
      have hp : HasDerivAt (fun w => (u, f u + sigma*w)) (0, sigma) v := by
        convert!
          (hasDerivAt_const v u).prodMk ((hasDerivAt_const v (f u)).add
            ((hasDerivAt_id v).const_mul sigma)) using 1 <;> simp
      have hc : HasDerivAt (fun w => coordinates.symm (u, f u + sigma*w))
          (coordinates.symm (0, sigma)) v :=
        coordinates.symm.hasFDerivAt.comp_hasDerivAt v hp
      have hvec : coordinates.symm (0, sigma) = sigma • coordinateVector 2 1 := by
        ext i
        fin_cases i <;> simp [coordinates, coordinateVector]
      rw [← hd.fderiv] at hd
      rw [hQpoint] at hd
      have hh := hd.comp_hasDerivAt v hc
      rw [hvec, map_smul] at hh
      change HasDerivAt (fun w => s (shear Q sigma f (u, w)))
        (sigma * fderiv ℝ (s ∘ Q.symm) (Q (shear Q sigma f (u, v)))
          (coordinateVector 2 1)) v
      convert! hh using 1 <;>
        simp only [Function.comp_apply, shear, Q.apply_symm_apply, smul_eq_mul]
    intro z hz
    let g : ℝ → ℝ := fun v => s (shear Q sigma f (z.1, v))
    have hg : ContinuousOn g (Ioo (-H) H) := fun v hv =>
      (hvertical z.1 hz.1 v hv).continuousAt.continuousWithinAt
    have hmono : StrictMonoOn g (Ioo (-H) H) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioo (-H) H) hg
      intro v hv
      rw [isOpen_Ioo.interior_eq] at hv
      rw [(hvertical z.1 hz.1 v hv).deriv]
      exact hpos (z.1, v) ⟨hz.1, hv⟩
    have hz0 : (0 : ℝ) ∈ Ioo (-H) H := ⟨neg_neg_of_pos hH, hH⟩
    have hg0 : g 0 = 0 := hzero z.1 hz.1
    have hlo := hmono.lt_iff_lt hz.2 hz0
    have hhi := hmono.lt_iff_lt hz0 hz.2
    rw [hg0] at hlo hhi
    exact ⟨hlo, hhi⟩
  have hOpen (Q : E2 ≃ₗᵢ[ℝ] E2) (hQ : IsCoordinateFrame Q)
      (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
      (f : ℝ → ℝ) (A B H : ℝ) (hf : ContDiffOn ℝ ∞ f (Ioo A B)) :
      IsOpen (shear Q sigma f '' (Ioo A B ×ˢ Ioo (-H) H)) := by
    have hbridge := explicit_shear_and_measure_bridge Q hQ sigma hsigma f A B hf
    have hleft := hbridge.2.2.2.1
    have hright := hbridge.2.2.2.2.1
    have hInv : ContDiffOn ℝ ∞ (unshear Q sigma f)
        {x : E2 | (Q x) 0 ∈ Ioo A B} := hbridge.2.2.2.2.2.2.2.1
    let V : Set E2 := {x : E2 | (Q x) 0 ∈ Ioo A B}
    have hV : IsOpen V := isOpen_Ioo.preimage
      ((EuclideanSpace.proj 0).continuous.comp Q.continuous)
    have hEq : shear Q sigma f '' (Ioo A B ×ˢ Ioo (-H) H) =
        V ∩ unshear Q sigma f ⁻¹' (Ioo A B ×ˢ Ioo (-H) H) := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hfirst := congrArg Prod.fst (hleft z)
        change (Q (shear Q sigma f z)) 0 = z.1 at hfirst
        refine ⟨?_, ?_⟩
        · change (Q (shear Q sigma f z)) 0 ∈ Ioo A B
          rw [hfirst]
          exact hz.1
        · change unshear Q sigma f (shear Q sigma f z) ∈ Ioo A B ×ˢ Ioo (-H) H
          rw [hleft z]
          exact hz
      · intro hx
        exact ⟨unshear Q sigma f x, hx.2, hright x⟩
    rw [hEq]
    exact hInv.continuousOn.isOpen_inter_preimage hV (isOpen_Ioo.prod isOpen_Ioo)
  obtain ⟨Q, hQ, hv⟩ := hFrame disc s gamma left right G q hq hz
  have hqzero : q ∈ {x ∈ disc | s x = 0} := ⟨hq, hz⟩
  rw [G.zero_set_exact] at hqzero
  obtain ⟨t, ht, hgt⟩ := hqzero.1
  have hgtDisc : gamma t ∈ disc := by rw [hgt]; exact hq
  have hgtTrans : transverse Q s (gamma t) ≠ 0 := by rw [hgt]; exact hv
  obtain ⟨J0, J1, A, B, f, eta, htJ, hJclose, hAB, hclockBig, hfBig, hetaBig,
    hetaMemBig, hetaLeftBig, hetaRightBig, hzeroBig, hgraphBig⟩ :=
    hGraph disc s gamma left right G t ht hgtDisc Q hgtTrans
  obtain ⟨Ve, hVe, htVe, hVeExclusion⟩ :=
    hExclusion disc s gamma left right G t ht (Ioo J0 J1) isOpen_Ioo htJ
  obtain ⟨sigma, Vs, hsig, hVs, hqVs, hVsDisc, hVsPos⟩ :=
    hOrientation disc s G.disc_open G.signed_smooth q hq Q hv
  let V := Ve ∩ Vs
  have hV : IsOpen V := hVe.inter hVs
  have hgtV : gamma t ∈ V := ⟨htVe, by rw [hgt]; exact hqVs⟩
  have hGammaT : ContinuousAt gamma t :=
    G.arc_smooth.continuousOn.continuousAt (isOpen_Ioo.mem_nhds ht)
  obtain ⟨l, r, htr, hlocal⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (inter_mem (isOpen_Ioo.mem_nhds htJ) (hGammaT.preimage_mem_nhds (hV.mem_nhds hgtV)))
  let j0 := (l+t)/2
  let j1 := (t+r)/2
  have htSmall : t ∈ Ioo j0 j1 := ⟨by dsimp [j0]; linarith [htr.1], by dsimp [j1]; linarith [htr.2]⟩
  have hj : j0 < j1 := htSmall.1.trans htSmall.2
  have hsmall : Icc j0 j1 ⊆ Ioo l r := by
    intro u hu
    have hlo : (l+t)/2 ≤ u := hu.1
    have hhi : u ≤ (t+r)/2 := hu.2
    constructor <;> linarith [htr.1, htr.2]
  have hsmallBig : Icc j0 j1 ⊆ Ioo J0 J1 := fun u hu => (hlocal (hsmall hu)).1
  have hsmallV : ∀ u ∈ Icc j0 j1, gamma u ∈ V := fun u hu => (hlocal (hsmall hu)).2
  have hsmallParameters : Icc j0 j1 ⊆ Ioo left right :=
    hsmallBig.trans (Ioo_subset_Icc_self.trans hJclose)
  let kappa : ℝ → ℝ := fun u => (Q (gamma u)) 0
  have hk : ContinuousOn kappa (Icc j0 j1) :=
    ((EuclideanSpace.proj 0).continuous.comp Q.continuous).comp_continuousOn
      (G.arc_smooth.continuousOn.mono hsmallParameters)
  have hkInjBig : InjOn kappa (Ioo J0 J1) := by
    intro u hu v hv huv
    have hh := congrArg eta huv
    rw [hetaLeftBig u hu, hetaLeftBig v hv] at hh
    exact hh
  have hintervals : ∃ a b : ℝ, a < b ∧
      kappa '' Ioo j0 j1 = Ioo a b ∧ kappa '' Icc j0 j1 = Icc a b ∧
      Icc a b ⊆ Ioo A B := by
    have hfirst : kappa j0 ∈ Ioo A B := by
      rw [← hclockBig]; exact mem_image_of_mem _ (hsmallBig (left_mem_Icc.mpr hj.le))
    have hlast : kappa j1 ∈ Ioo A B := by
      rw [← hclockBig]; exact mem_image_of_mem _ (hsmallBig (right_mem_Icc.mpr hj.le))
    rcases hk.strictMonoOn_of_injOn_Icc' hj.le (hkInjBig.mono hsmallBig) with hm | hm
    · refine ⟨kappa j0, kappa j1,
        hm (left_mem_Icc.mpr hj.le) (right_mem_Icc.mpr hj.le) hj,
        hk.image_Ioo_of_strictMonoOn hj.le hm,
        hk.image_Icc_of_monotoneOn hj.le hm.monotoneOn, ?_⟩
      intro u hu
      exact ⟨hfirst.1.trans_le hu.1, hu.2.trans_lt hlast.2⟩
    · refine ⟨kappa j1, kappa j0,
        hm (left_mem_Icc.mpr hj.le) (right_mem_Icc.mpr hj.le) hj,
        hk.image_Ioo_of_strictAntiOn hj.le hm,
        hk.image_Icc_of_antitoneOn hj.le hm.antitoneOn, ?_⟩
      intro u hu
      exact ⟨hlast.1.trans_le hu.1, hu.2.trans_lt hfirst.2⟩
  obtain ⟨a, b, hab, hclock, hclockClosed, hclosedBig⟩ := hintervals
  have hopenBig : Ioo a b ⊆ Ioo A B := Ioo_subset_Icc_self.trans hclosedBig
  have hf : ContDiffOn ℝ ∞ f (Ioo a b) := hfBig.mono hopenBig
  have hzeroShears : ∀ u : ℝ, shear Q sigma f (u, 0) = shear Q 1 f (u, 0) := by
    intro u
    simp only [shear, mul_zero, add_zero]
  have hetaLeft : ∀ v ∈ Ioo j0 j1, eta (kappa v) = v :=
    fun v hv => hetaLeftBig v (hsmallBig (Ioo_subset_Icc_self hv))
  have hgraph : ∀ v ∈ Ioo j0 j1, gamma v = shear Q sigma f (kappa v, 0) := by
    intro v hv
    rw [hzeroShears]
    exact hgraphBig v (hsmallBig (Ioo_subset_Icc_self hv))
  have hgraphClosed : ∀ u ∈ Icc a b, shear Q sigma f (u, 0) ∈ V := by
    intro u hu
    rw [← hclockClosed] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [hzeroShears, ← hgraphBig v (hsmallBig hv)]
    exact hsmallV v hv
  have hbridgeBig := explicit_shear_and_measure_bridge Q hQ sigma hsig f A B hfBig
  have haA : A < a := (hclosedBig (left_mem_Icc.mpr hab.le)).1
  have hbB : b < B := (hclosedBig (right_mem_Icc.mpr hab.le)).2
  obtain ⟨height, hheight, hstripV⟩ := hUniform Q sigma f A B a b hab.le haA hbB
    hbridgeBig.2.2.2.2.2.2.1.continuousOn V hV hgraphClosed
  let Rect := Ioo a b ×ˢ Ioo (-height) height
  let Omega := shear Q sigma f '' Rect
  have hOmegaV : Omega ⊆ V :=
    (image_mono (prod_mono Ioo_subset_Icc_self subset_rfl)).trans hstripV
  have hOmegaDisc : Omega ⊆ disc := hOmegaV.trans (inter_subset_right.trans hVsDisc)
  have htransverse : ∀ z ∈ Rect, 0 < sigma * transverse Q s (shear Q sigma f z) := by
    intro z hz
    exact hVsPos _ ((hOmegaV (mem_image_of_mem _ hz)).2)
  have hzero : ∀ u ∈ Ioo a b, s (shear Q sigma f (u, 0)) = 0 := by
    intro u hu
    rw [hzeroShears]
    exact (hzeroBig u (hopenBig hu)).2
  have hsigns := hSigns disc s G.disc_open G.signed_smooth Q sigma f a b height
    hheight hOmegaDisc htransverse hzero
  have hbridge := explicit_shear_and_measure_bridge Q hQ sigma hsig f a b hf
  have hleft := hbridge.2.2.2.1
  have hright := hbridge.2.2.2.2.1
  have hfirst : ∀ z : ℝ × ℝ, (Q (shear Q sigma f z)) 0 = z.1 := by
    intro z
    exact congrArg Prod.fst (hleft z)
  have hOmegaOpen : IsOpen Omega := hOpen Q hQ sigma hsig f a b height hf
  have hqOmega : q ∈ Omega := by
    refine ⟨(kappa t, 0), ?_, ?_⟩
    · refine ⟨?_, ⟨neg_neg_of_pos hheight, hheight⟩⟩
      rw [← hclock]
      exact mem_image_of_mem _ htSmall
    · exact (hgraph t htSmall).symm.trans hgt
  obtain ⟨L, hL, hqL, hLOmega⟩ := exists_compact_between isCompact_singleton hOmegaOpen
    (singleton_subset_iff.mpr hqOmega)
  have hclosureL : closure (interior L) ⊆ L := closure_minimal interior_subset hL.isClosed
  refine ⟨{
    center := q
    center_mem := hq
    center_zero := hz
    Q := Q
    frame := hQ
    sigma := sigma
    sigma_choice := hsig
    a0 := a
    b0 := b
    interval_nonempty := hab
    f := f
    graph_smooth := hf
    h0 := height
    height_positive := hheight
    omega_open := hOmegaOpen
    omega_subset := hOmegaDisc
    graph_zero := hzero
    level_zero_exact := by
      ext x
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hsZero⟩
        have hz2 : z.2 = 0 := by
          by_contra hn
          rcases lt_or_gt_of_ne hn with hn | hn
          · have hh := (hsigns z hz).1.mpr hn; rw [hsZero] at hh; exact lt_irrefl _ hh
          · have hh := (hsigns z hz).2.mpr hn; rw [hsZero] at hh; exact lt_irrefl _ hh
        refine ⟨z.1, hz.1, ?_⟩
        exact congrArg (shear Q sigma f) (show (z.1, 0) = z from Prod.ext rfl hz2.symm)
      · rintro ⟨u, hu, rfl⟩
        exact ⟨mem_image_of_mem _ ⟨hu, ⟨neg_neg_of_pos hheight, hheight⟩⟩, hzero u hu⟩
    strict_signs := hsigns
    transverse_positive := htransverse
    strict_side_image := by
      intro positive
      cases positive
      · ext x
        constructor
        · rintro ⟨⟨hxDisc, hsneg⟩, z, hz, rfl⟩
          exact ⟨z, ⟨hz.1, ⟨hz.2.1, (hsigns z hz).1.mp hsneg⟩⟩, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          have hzRect : z ∈ Rect := ⟨hz.1, hz.2.1, hz.2.2.trans hheight⟩
          exact ⟨⟨hOmegaDisc (mem_image_of_mem _ hzRect), (hsigns z hzRect).1.mpr hz.2.2⟩,
            mem_image_of_mem _ hzRect⟩
      · ext x
        constructor
        · rintro ⟨⟨hxDisc, hspos⟩, z, hz, rfl⟩
          exact ⟨z, ⟨hz.1, ⟨(hsigns z hz).2.mp hspos, hz.2.2⟩⟩, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          have hzRect : z ∈ Rect := ⟨hz.1, (neg_neg_of_pos hheight).trans hz.2.1, hz.2.2⟩
          exact ⟨⟨hOmegaDisc (mem_image_of_mem _ hzRect), (hsigns z hzRect).2.mpr hz.2.1⟩,
            mem_image_of_mem _ hzRect⟩
    shear_smooth := hbridge.2.2.2.2.2.2.1.mono (prod_mono subset_rfl (subset_univ _))
    inverse_smooth := hbridge.2.2.2.2.2.2.2.1.mono (by
      rintro x ⟨z, hz, rfl⟩
      change (Q (shear Q sigma f z)) 0 ∈ Ioo a b
      rw [hfirst]
      exact hz.1)
    chart_derivative := fun z hz => hbridge.2.2.2.2.2.2.2.2.1 z hz.1
    inverse_left := hleft
    inverse_right := hright
    j0 := j0
    j1 := j1
    parameter_nonempty := hj
    parameter_closure := hsmallParameters
    clock_image := hclock
    gamma_graph := hgraph
    original_parameter_exclusion := by
      intro u hu hgu
      have huBig := hVeExclusion u hu (hOmegaV hgu).1
      obtain ⟨z, hz, hzg⟩ := hgu
      have huClock : kappa u ∈ Ioo a b := by
        change (Q (gamma u)) 0 ∈ Ioo a b
        rw [← hzg, hfirst]
        exact hz.1
      rw [← hclock] at huClock
      obtain ⟨v, hv, hvu⟩ := huClock
      have hEq : v = u := hkInjBig (hsmallBig (Ioo_subset_Icc_self hv)) huBig hvu
      rwa [hEq] at hv
    inverseClock := eta
    inverseClock_mem := by
      intro u hu
      rw [← hclock] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      rw [hetaLeft v hv]
      exact hv
    inverseClock_left := hetaLeft
    inverseClock_right := fun u hu => hetaRightBig u (hopenBig hu)
    window := interior L
    window_open := isOpen_interior
    center_in_window := hqL (mem_singleton _)
    window_precompact := hL.of_isClosed_subset isClosed_closure hclosureL
    window_closure_subset := hclosureL.trans hLOmega
  }, rfl⟩

structure FiniteLocalization (disc : Set E2) (s : E2 → ℝ)
    (gamma : ℝ → E2) (left right : ℝ) (phi : E2 → ℝ) where
  n : ℕ
  Kprime : Set E2
  Kprime_compact : IsCompact Kprime
  Kprime_subset : Kprime ⊆ disc
  support_interior : tsupport phi ⊆ interior Kprime
  U : Fin n → Set E2
  U_open : ∀ j, IsOpen (U j)
  U_precompact : ∀ j, IsCompact (closure (U j))
  cover : Kprime ⊆ ⋃ j, U j
  patch : Fin n → SignedGraphChart disc s gamma left right ⊕ Bool
  boundary_window : ∀ j C, patch j = Sum.inl C → closure (U j) ⊆ C.window
  interior_window : ∀ j positive, patch j = Sum.inr positive →
    closure (U j) ⊆ signedDomain disc s positive
  chi : Fin n → E2 → ℝ
  chi_smooth : ∀ j, ContDiff ℝ ∞ (chi j)
  chi_bounds : ∀ j x, 0 ≤ chi j x ∧ chi j x ≤ 1
  chi_support : ∀ j, tsupport (chi j) ⊆ U j
  N : Set E2
  N_open : IsOpen N
  N_contains : tsupport phi ⊆ N
  partition : ∀ x ∈ N, ∑ j, chi j x = 1
  gradient_cancellation : ∀ x ∈ N, ∑ j, planarGradient (chi j) x = 0
  a : Fin n → ℝ
  b : Fin n → ℝ
  h : Fin n → ℝ
  boundary_support_margin : ∀ j C, patch j = Sum.inl C →
    C.a0 < a j ∧ a j < b j ∧ b j < C.b0 ∧ 0 < h j ∧ h j < C.h0 ∧
    (shear C.Q C.sigma C.f ⁻¹' tsupport (fun x => chi j x * phi x)) ⊆
      Ioo (a j) (b j) ×ˢ Ioo (-h j) (h j)
  boundary_rectangle : ∀ j C, patch j = Sum.inl C →
    IsCompact (shear C.Q C.sigma C.f '' Icc (a j, -h j) (b j, h j)) ∧
      shear C.Q C.sigma C.f '' Icc (a j, -h j) (b j, h j) ⊆ disc

theorem finite_localization_from_original_support
    (disc : Set E2) (s : E2 → ℝ) (gamma : ℝ → E2) (left right : ℝ)
    (G : SignedArcGeometry disc s gamma left right)
    (phi : E2 → ℝ) (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ disc) :
    Nonempty (FiniteLocalization disc s gamma left right phi) := by
  classical
  have hcharts := signed_graph_chart_from_original_geometry disc s gamma left right G
  have hcoverLemma (disc : Set E2) (s : E2 → ℝ) (gamma : ℝ → E2) (left right : ℝ)
      (G : SignedArcGeometry disc s gamma left right)
      (hcharts : ∀ x ∈ disc, s x = 0 →
        ∃ C : SignedGraphChart disc s gamma left right, C.center = x)
      (K : Set E2) (hK : IsCompact K) (hKd : K ⊆ disc) :
      ∃ (n : ℕ) (U : Fin n → Set E2)
        (P : Fin n → SignedGraphChart disc s gamma left right ⊕ Bool),
        (∀ j, IsOpen (U j)) ∧ (∀ j, IsCompact (closure (U j))) ∧
        K ⊆ ⋃ j, U j ∧
        (∀ j C, P j = Sum.inl C → closure (U j) ⊆ C.window) ∧
        (∀ j positive, P j = Sum.inr positive →
          closure (U j) ⊆ signedDomain disc s positive) := by
    classical
    have hside : ∀ positive : Bool, IsOpen (signedDomain disc s positive) := by
      intro positive
      cases positive
      · change IsOpen (disc ∩ s ⁻¹' Iio 0)
        exact G.signed_smooth.continuousOn.isOpen_inter_preimage G.disc_open isOpen_Iio
      · change IsOpen (disc ∩ s ⁻¹' Ioi 0)
        exact G.signed_smooth.continuousOn.isOpen_inter_preimage G.disc_open isOpen_Ioi
    have hlocal : ∀ x : K, ∃ (V : Set E2)
        (p : SignedGraphChart disc s gamma left right ⊕ Bool),
        IsOpen V ∧ (x : E2) ∈ V ∧
        (∀ C, p = Sum.inl C → V ⊆ C.window) ∧
        (∀ positive, p = Sum.inr positive → V ⊆ signedDomain disc s positive) := by
      intro x
      by_cases hz : s x = 0
      · obtain ⟨C, hCx⟩ := hcharts x (hKd x.2) hz
        refine ⟨C.window, Sum.inl C, C.window_open, ?_, ?_, ?_⟩
        · rw [← hCx]; exact C.center_in_window
        · intro D hD; cases hD; exact subset_rfl
        · intro positive hp; cases hp
      · rcases lt_or_gt_of_ne hz with hneg | hpos
        · refine ⟨signedDomain disc s false, Sum.inr false, hside false,
            ⟨hKd x.2, hneg⟩, ?_, ?_⟩
          · intro C hp; cases hp
          · intro positive hp; cases hp; exact subset_rfl
        · refine ⟨signedDomain disc s true, Sum.inr true, hside true,
            ⟨hKd x.2, hpos⟩, ?_, ?_⟩
          · intro C hp; cases hp
          · intro positive hp; cases hp; exact subset_rfl
    choose V P hV hxV hboundary hinterior using hlocal
    have hshrink : ∀ x : K, ∃ U : Set E2, IsOpen U ∧ (x : E2) ∈ U ∧
        IsCompact (closure U) ∧ closure U ⊆ V x := by
      intro x
      obtain ⟨L, hL, hxL, hLV⟩ := exists_compact_between isCompact_singleton (hV x)
        (singleton_subset_iff.mpr (hxV x))
      have hclosure : closure (interior L) ⊆ L :=
        closure_minimal interior_subset hL.isClosed
      refine ⟨interior L, isOpen_interior, hxL (mem_singleton _),
        hL.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hLV⟩
    choose U hU hxU hcompact hUV using hshrink
    have hcover : K ⊆ ⋃ x : K, U x := by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcover
    let e : Fin t.card ≃ t := t.equivFin.symm
    refine ⟨t.card, fun j => U (e j).val, fun j => P (e j).val,
      fun j => hU (e j).val, fun j => hcompact (e j).val, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy⟩ := mem_iUnion.mp (ht hx)
      obtain ⟨hyt, hxy⟩ := mem_iUnion.mp hy
      refine mem_iUnion.mpr ⟨e.symm ⟨y, hyt⟩, ?_⟩
      simpa only [Equiv.apply_symm_apply] using hxy
    · intro j C hj
      exact (hUV (e j).val).trans (hboundary (e j).val C hj)
    · intro j positive hj
      exact (hUV (e j).val).trans (hinterior (e j).val positive hj)
  have hpartitionLemma (n : ℕ) (K : Set E2) (hK : IsCompact K)
      (U : Fin n → Set E2) (hU : ∀ j, IsOpen (U j)) (hcover : K ⊆ ⋃ j, U j) :
      ∃ chi : Fin n → E2 → ℝ,
        (∀ j, ContDiff ℝ ∞ (chi j)) ∧
        (∀ j x, 0 ≤ chi j x ∧ chi j x ≤ 1) ∧
        (∀ j, tsupport (chi j) ⊆ U j) ∧
        (∀ x ∈ K, ∑ j, chi j x = 1) ∧
        (∀ x ∈ interior K, ∑ j, planarGradient (chi j) x = 0) := by
    classical
    obtain ⟨P, hP⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E2))
      hK.isClosed U hU hcover
    let chi : Fin n → E2 → ℝ := fun j => P j
    have hsmooth : ∀ j, ContDiff ℝ ∞ (chi j) := fun j => (P j).contMDiff.contDiff
    have hsum : ∀ x ∈ K, ∑ j, chi j x = 1 := by
      intro x hx
      simpa only [chi, finsum_eq_sum_of_fintype] using P.sum_eq_one hx
    refine ⟨chi, hsmooth, fun j x => ⟨P.nonneg j x, P.le_one j x⟩, hP, hsum, ?_⟩
    intro x hx
    have heq : (fun y => ∑ j, chi j y) =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [isOpen_interior.mem_nhds hx] with y hy
      exact hsum y (interior_subset hy)
    have hzero : fderiv ℝ (fun y => ∑ j, chi j y) x = 0 := by
      rw [heq.fderiv_eq (𝕜 := ℝ)]
      exact fderiv_const_apply (1 : ℝ)
    have hderiv : ∀ j ∈ (Finset.univ : Finset (Fin n)), DifferentiableAt ℝ (chi j) x :=
      fun j _ => (hsmooth j).differentiable (by simp) x
    rw [fderiv_fun_sum hderiv] at hzero
    change (∑ j : Fin n, ∑ i : Fin 2,
      fderiv ℝ (chi j) x (coordinateVector 2 i) • coordinateVector 2 i) = 0
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.sum_smul]
    have hcoeff : ∑ j : Fin n, fderiv ℝ (chi j) x (coordinateVector 2 i) = 0 := by
      have hh := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) hzero
      simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.zero_apply] using hh
    rw [hcoeff, zero_smul]
  have hmarginLemma (disc : Set E2) (s : E2 → ℝ) (gamma : ℝ → E2) (left right : ℝ)
      (C : SignedGraphChart disc s gamma left right)
      (theta : E2 → ℝ) (hc : HasCompactSupport theta)
      (hs : tsupport theta ⊆ C.window) :
      ∃ a b h : ℝ,
        C.a0 < a ∧ a < b ∧ b < C.b0 ∧ 0 < h ∧ h < C.h0 ∧
        (shear C.Q C.sigma C.f ⁻¹' tsupport theta) ⊆ Ioo a b ×ˢ Ioo (-h) h ∧
        IsCompact (shear C.Q C.sigma C.f '' Icc (a, -h) (b, h)) ∧
        shear C.Q C.sigma C.f '' Icc (a, -h) (b, h) ⊆ disc := by
    let T := shear C.Q C.sigma C.f
    let S := unshear C.Q C.sigma C.f
    let Omega := T '' (Ioo C.a0 C.b0 ×ˢ Ioo (-C.h0) C.h0)
    have hTheta : tsupport theta ⊆ Omega :=
      hs.trans (subset_closure.trans C.window_closure_subset)
    let K : Set (ℝ × ℝ) := S '' tsupport theta
    have hK : IsCompact K := hc.image_of_continuousOn (C.inverse_smooth.continuousOn.mono hTheta)
    have hKsub : K ⊆ Ioo C.a0 C.b0 ×ˢ Ioo (-C.h0) C.h0 := by
      rintro z ⟨x, hx, rfl⟩
      obtain ⟨w, hw, hTw⟩ := hTheta hx
      rw [← hTw]
      change unshear C.Q C.sigma C.f (shear C.Q C.sigma C.f w) ∈ _
      rw [C.inverse_left]
      exact hw
    have hpre : T ⁻¹' tsupport theta = K := by
      ext z
      constructor
      · intro hz
        exact ⟨T z, hz, C.inverse_left z⟩
      · rintro ⟨x, hx, rfl⟩
        change shear C.Q C.sigma C.f (unshear C.Q C.sigma C.f x) ∈ tsupport theta
        rw [C.inverse_right]
        exact hx
    have hrectangle : ∃ a b h : ℝ,
        C.a0 < a ∧ a < b ∧ b < C.b0 ∧ 0 < h ∧ h < C.h0 ∧
          K ⊆ Ioo a b ×ˢ Ioo (-h) h := by
      rcases K.eq_empty_or_nonempty with hempty | hne
      · refine ⟨(2*C.a0+C.b0)/3, (C.a0+2*C.b0)/3, C.h0/2, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first
        | linarith [C.interval_nonempty, C.height_positive]
        | simpa only [hempty] using empty_subset _
      · obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
        obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
        obtain ⟨r, hr, hheight⟩ := hK.exists_isMaxOn hne continuous_snd.abs.continuousOn
        have hpA : C.a0 < p.1 := (hKsub hp).1.1
        have hqB : q.1 < C.b0 := (hKsub hq).1.2
        have hpq : p.1 ≤ q.1 := hmin hq
        have hrH : |r.2| < C.h0 := abs_lt.mpr (hKsub hr).2
        have hr0 : 0 ≤ |r.2| := abs_nonneg _
        refine ⟨(C.a0+p.1)/2, (q.1+C.b0)/2, (|r.2|+C.h0)/2,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · linarith
        · linarith [C.height_positive]
        · linarith
        · intro z hz
          have hlow : p.1 ≤ z.1 := hmin hz
          have hupp : z.1 ≤ q.1 := hmax hz
          have hhgt : |z.2| ≤ |r.2| := hheight hz
          exact ⟨⟨by linarith, by linarith⟩, abs_lt.mp (by linarith)⟩
    obtain ⟨a, b, h, ha, hab, hb, hh, hh0, hmargin⟩ := hrectangle
    have hbox : Icc (a, -h) (b, h) ⊆ Ioo C.a0 C.b0 ×ˢ Ioo (-C.h0) C.h0 := by
      intro z hz
      exact ⟨⟨ha.trans_le hz.1.1, hz.2.1.trans_lt hb⟩,
        ⟨by linarith [hz.1.2], hz.2.2.trans_lt hh0⟩⟩
    refine ⟨a, b, h, ha, hab, hb, hh, hh0, ?_, ?_, ?_⟩
    · rw [← hpre] at hmargin
      exact hmargin
    · exact isCompact_Icc.image_of_continuousOn (C.shear_smooth.continuousOn.mono hbox)
    · exact (image_mono hbox).trans C.omega_subset
  obtain ⟨Kprime, hKprime, hsupport, hKdisc⟩ :=
    exists_compact_between hc G.disc_open hs
  obtain ⟨n, U, patch, hopen, hcompact, hcover, hboundary, hinterior⟩ :=
    hcoverLemma disc s gamma left right G hcharts Kprime hKprime hKdisc
  obtain ⟨chi, hchi, hbound, hchisupport, hsum, hgradient⟩ :=
    hpartitionLemma n Kprime hKprime U hopen hcover
  have hmargins : ∀ j : Fin n, ∃ a b h : ℝ,
      ∀ C : SignedGraphChart disc s gamma left right, patch j = Sum.inl C →
        (C.a0 < a ∧ a < b ∧ b < C.b0 ∧ 0 < h ∧ h < C.h0 ∧
          (shear C.Q C.sigma C.f ⁻¹' tsupport (fun x => chi j x * phi x)) ⊆
            Ioo a b ×ˢ Ioo (-h) h) ∧
        (IsCompact (shear C.Q C.sigma C.f '' Icc (a, -h) (b, h)) ∧
          shear C.Q C.sigma C.f '' Icc (a, -h) (b, h) ⊆ disc) := by
    intro j
    cases hp : patch j with
    | inl C =>
      have hthetac : HasCompactSupport (fun x => chi j x * phi x) := hc.mul_left
      have hthetas : tsupport (fun x => chi j x * phi x) ⊆ C.window :=
        tsupport_mul_subset_left.trans ((hchisupport j).trans
          (subset_closure.trans (hboundary j C hp)))
      obtain ⟨a, b, h, ha, hab, hb, hh, hh0, hmargin, hbox, hboxdisc⟩ :=
        hmarginLemma disc s gamma left right C (fun x => chi j x * phi x) hthetac hthetas
      refine ⟨a, b, h, ?_⟩
      intro C' hp'
      have hCC : C = C' := Sum.inl.inj hp'
      subst C'
      exact ⟨⟨ha, hab, hb, hh, hh0, hmargin⟩, hbox, hboxdisc⟩
    | inr positive =>
      refine ⟨0, 0, 0, ?_⟩
      intro C hp'
      cases hp'
  choose a b h hm using hmargins
  refine ⟨{
    n := n
    Kprime := Kprime
    Kprime_compact := hKprime
    Kprime_subset := hKdisc
    support_interior := hsupport
    U := U
    U_open := hopen
    U_precompact := hcompact
    cover := hcover
    patch := patch
    boundary_window := hboundary
    interior_window := hinterior
    chi := chi
    chi_smooth := hchi
    chi_bounds := hbound
    chi_support := hchisupport
    N := interior Kprime
    N_open := isOpen_interior
    N_contains := hsupport
    partition := fun x hx => hsum x (interior_subset hx)
    gradient_cancellation := hgradient
    a := a
    b := b
    h := h
    boundary_support_margin := fun j C hp => (hm j C hp).1
    boundary_rectangle := fun j C hp => (hm j C hp).2
  }⟩

theorem exact_shear_volume_transport
    (Q : E2 ≃ₗᵢ[ℝ] E2) (hQ : IsCoordinateFrame Q)
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (f : ℝ → ℝ) (a0 b0 : ℝ) (hf : ContDiffOn ℝ ∞ f (Ioo a0 b0))
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (hstrip : A ⊆ Ioo a0 b0 ×ˢ (univ : Set ℝ)) (d : E2 → ℝ) :
    MeasurableSet (shear Q sigma f '' A) ∧ InjOn (shear Q sigma f) A ∧
    (∀ z ∈ A, HasFDerivWithinAt (shear Q sigma f) (shearDerivative Q sigma f z.1) A z) ∧
    (IntegrableOn d (shear Q sigma f '' A) (volume : Measure E2) ↔
      IntegrableOn (d ∘ shear Q sigma f) A (volume : Measure (ℝ × ℝ))) ∧
    (∫ x in shear Q sigma f '' A, d x ∂(volume : Measure E2)) =
      ∫ z in A, d (shear Q sigma f z) ∂(volume : Measure (ℝ × ℝ)) := by
  obtain ⟨hcoord, hcoordMP, hinvMP, hleft, hright, hinj, hsmooth, hismooth, hderiv, hdet⟩ :=
    explicit_shear_and_measure_bridge Q hQ sigma hsigma f a0 b0 hf
  let B : Set E2 := coordinates ⁻¹' A
  let T : E2 → E2 := shear Q sigma f ∘ coordinates
  have hB : MeasurableSet B := hA.preimage coordinates.continuous.measurable
  have hinjT : InjOn T B := (hinj.comp coordinates.injective).injOn
  have hdf : ∀ x ∈ B, HasFDerivWithinAt T (fderiv ℝ T x) B x := by
    intro x hx
    have hc := (hderiv (coordinates x) (hstrip hx).1).comp x coordinates.hasFDerivAt
    exact hc.differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hjac : ∀ x ∈ B, |(fderiv ℝ T x).det| = 1 := by
    intro x hx
    exact hdet x (hstrip hx).1
  have himage : T '' B = shear Q sigma f '' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨coordinates y, hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨coordinates.symm z, ?_, ?_⟩
      · change coordinates (coordinates.symm z) ∈ A
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz
      · exact congrArg (shear Q sigma f) (coordinates.apply_symm_apply z)
  have hBimage : coordinates.symm '' A = B := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change coordinates (coordinates.symm z) ∈ A
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz
    · intro hx
      exact ⟨coordinates x, hx, coordinates.symm_apply_apply x⟩
  have hm : MeasurableSet (shear Q sigma f '' A) := by
    rw [← himage]
    exact measurable_image_of_fderivWithin hB hdf hinjT
  have hip : IntegrableOn d (T '' B) ↔ IntegrableOn (fun x => d (T x)) B := by
    have hi := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (volume : Measure E2) hB hdf hinjT d
    constructor
    · intro h
      exact (hi.mp h).congr_fun (fun x hx => by change |(fderiv ℝ T x).det| • d (T x) = d (T x); rw [hjac x hx, one_smul]) hB
    · intro h
      apply hi.mpr
      exact h.congr_fun (fun x hx => by change d (T x) = |(fderiv ℝ T x).det| • d (T x); rw [hjac x hx, one_smul]) hB
  have hcoordsInt : IntegrableOn (d ∘ shear Q sigma f) A ↔
      IntegrableOn (fun x => d (T x)) B := by
    have hp := hinvMP.restrict_image_emb coordinates.symm.toHomeomorph.measurableEmbedding A
    rw [hBimage] at hp
    have hi := hp.integrable_comp_emb coordinates.symm.toHomeomorph.measurableEmbedding
      (g := fun x => d (T x))
    change Integrable (d ∘ shear Q sigma f) (volume.restrict A) ↔
      Integrable (fun x => d (T x)) (volume.restrict B)
    simpa only [T, Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using hi
  refine ⟨hm, hinj.injOn, (fun z hz => (hderiv z (hstrip hz).1).hasFDerivWithinAt), ?_, ?_⟩
  · rw [← himage]
    exact hip.trans hcoordsInt.symm
  · rw [← himage]
    calc
      (∫ x in T '' B, d x) = ∫ x in B, |(fderiv ℝ T x).det| • d (T x) :=
        integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure E2) hB hdf hinjT d
      _ = ∫ x in B, d (T x) :=
        setIntegral_congr_fun hB (fun x hx => by rw [hjac x hx, one_smul])
      _ = ∫ z in A, d (shear Q sigma f z) := by
        have hi := hinvMP.setIntegral_image_emb coordinates.symm.toHomeomorph.measurableEmbedding
          (fun x => d (T x)) A
        rw [hBimage] at hi
        simpa only [T, Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using hi

theorem null_faces_and_summed_divergence_transfer
    (a b h : ℝ) (hab : a < b) (hh : 0 < h) (positive : Bool)
    (f' g' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)) (d : ℝ × ℝ → ℝ)
    (hd : IntegrableOn d (openHalfBox positive a b h))
    (heq : ∀ z ∈ openHalfBox positive a b h, f' z (1, 0) + g' z (0, 1) = d z) :
    (∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      z ∈ halfBox positive a b h ↔ z ∈ openHalfBox positive a b h) ∧
    (volume : Measure (ℝ × ℝ)) (halfBox positive a b h \ openHalfBox positive a b h) = 0 ∧
    IntegrableOn (fun z => f' z (1, 0) + g' z (0, 1)) (halfBox positive a b h) ∧
    (∫ z in halfBox positive a b h, f' z (1, 0) + g' z (0, 1)) =
      ∫ z in openHalfBox positive a b h, d z := by
  have hvol : (volume : Measure (ℝ × ℝ)) =
      (volume : Measure ℝ).prod (volume : Measure ℝ) :=
    Measure.volume_eq_prod ℝ ℝ
  have hae : openHalfBox positive a b h =ᵐ[volume] halfBox positive a b h := by
    rw [hvol]
    cases positive
    · change (Ioo a b ×ˢ Ioo (-h) 0) =ᵐ[_] Icc (a, -h) (b, 0)
      simpa only [Icc_prod_eq] using
        (Measure.set_prod_ae_eq
          (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := a) (b := b))
          (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := -h) (b := 0)))
    · change (Ioo a b ×ˢ Ioo 0 h) =ᵐ[_] Icc (a, 0) (b, h)
      simpa only [Icc_prod_eq] using
        (Measure.set_prod_ae_eq
          (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := a) (b := b))
          (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := 0) (b := h)))
  have hm : MeasurableSet (openHalfBox positive a b h) := by
    cases positive <;> exact measurableSet_Ioo.prod measurableSet_Ioo
  have hs : IntegrableOn (fun z => f' z (1, 0) + g' z (0, 1))
      (openHalfBox positive a b h) :=
    hd.congr_fun (fun z hz => (heq z hz).symm) hm
  refine ⟨?_, (ae_eq_set.mp hae.symm).1, hs.congr_set_ae hae.symm, ?_⟩
  · filter_upwards [hae.symm] with z hz
    exact Iff.of_eq hz
  · exact (setIntegral_congr_set hae.symm).trans (setIntegral_congr_fun hm heq)

theorem same_clock_smooth_inverse_and_orientation
    (disc : Set E2) (s : E2 → ℝ) (gamma : ℝ → E2) (left right : ℝ)
    (G : SignedArcGeometry disc s gamma left right)
    (C : SignedGraphChart disc s gamma left right) :
    let kappa : ℝ → ℝ := fun t => (C.Q (gamma t)) 0
    ContDiffOn ℝ ∞ kappa (Ioo C.j0 C.j1) ∧
    (∀ t ∈ Ioo C.j0 C.j1, deriv kappa t ≠ 0) ∧
    ContDiffOn ℝ ∞ C.inverseClock (Ioo C.a0 C.b0) ∧
    InjOn kappa (Ioo C.j0 C.j1) ∧ kappa '' Ioo C.j0 C.j1 = Ioo C.a0 C.b0 ∧
    ((∀ t ∈ Ioo C.j0 C.j1, 0 < deriv kappa t) ∨
      (∀ t ∈ Ioo C.j0 C.j1, deriv kappa t < 0)) := by
  let kappa : ℝ → ℝ := fun t => (C.Q (gamma t)) 0
  have hj : Ioo C.j0 C.j1 ⊆ Ioo left right :=
    Ioo_subset_Icc_self.trans C.parameter_closure
  have hgamma := G.arc_smooth.mono hj
  have hcoord : ContDiff ℝ ∞ (fun x : E2 => (C.Q x) 0) := by
    fun_prop
  have hk : ContDiffOn ℝ ∞ kappa (Ioo C.j0 C.j1) :=
    hcoord.comp_contDiffOn hgamma
  have hmem : ∀ t ∈ Ioo C.j0 C.j1, kappa t ∈ Ioo C.a0 C.b0 := by
    intro t ht
    rw [← C.clock_image]
    exact mem_image_of_mem _ ht
  have hn : ∀ t ∈ Ioo C.j0 C.j1, deriv kappa t ≠ 0 := by
    intro t ht hz
    have hkt : HasDerivAt kappa (deriv kappa t) t :=
      (hk.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp) |>.hasDerivAt
    have hp : HasDerivAt (fun u => (kappa u, (0 : ℝ))) (0, 0) t := by
      simpa [hz] using hkt.prodMk (hasDerivAt_const t (0 : ℝ))
    have hst := C.chart_derivative (kappa t, 0)
      ⟨hmem t ht, by exact ⟨neg_lt_zero.mpr C.height_positive, C.height_positive⟩⟩
    have hcomp : HasDerivAt (fun u => shear C.Q C.sigma C.f (kappa u, 0)) 0 t := by
      have hc := hst.comp_hasDerivAt t hp
      have hzmap : shearDerivative C.Q C.sigma C.f (kappa t) (0, 0) = 0 :=
        (shearDerivative C.Q C.sigma C.f (kappa t)).map_zero
      rw [hzmap] at hc
      exact hc
    have heq : gamma =ᶠ[𝓝 t] (fun u => shear C.Q C.sigma C.f (kappa u, 0)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
      exact C.gamma_graph u hu
    have hzero : fderiv ℝ gamma t 1 = 0 := by
      have hgzero := hcomp.congr_of_eventuallyEq heq
      simpa using congrArg (fun L : ℝ →L[ℝ] E2 => L 1) hgzero.hasFDerivAt.fderiv
    exact G.arc_regular t (hj ht) hzero
  have hinj : InjOn kappa (Ioo C.j0 C.j1) := by
    intro t ht u hu htu
    calc
      t = C.inverseClock (kappa t) := (C.inverseClock_left t ht).symm
      _ = C.inverseClock (kappa u) := congrArg C.inverseClock htu
      _ = u := C.inverseClock_left u hu
  have hdinv : ContDiffOn ℝ ∞ C.inverseClock (Ioo C.a0 C.b0) := by
    apply isOpen_Ioo.contDiffOn_iff.mpr
    intro u hu
    let t := C.inverseClock u
    have ht : t ∈ Ioo C.j0 C.j1 := C.inverseClock_mem u hu
    have hku : kappa t = u := C.inverseClock_right u hu
    have hkat := hk.contDiffAt (isOpen_Ioo.mem_nhds ht)
    let e : ℝ ≃L[ℝ] ℝ := .unitsEquivAut ℝ (.mk0 (deriv kappa t) (hn t ht))
    have hdf : HasFDerivAt kappa e.toContinuousLinearMap t :=
      ((hkat.differentiableAt (by simp)).hasDerivAt).hasFDerivAt_equiv (hn t ht)
    let R := hkat.toOpenPartialHomeomorph kappa hdf (by simp)
    have hRt : t ∈ R.source := hkat.mem_toOpenPartialHomeomorph_source hdf (by simp)
    have hRu : u ∈ R.target := by
      rw [← hku]
      exact hkat.image_mem_toOpenPartialHomeomorph_target hdf (by simp)
    have hinv : R.symm u = t := by
      rw [← hku]
      exact R.left_inv hRt
    have hRsmooth : ContDiffAt ℝ ∞ R.symm u := by
      apply R.contDiffAt_symm_deriv (hn t ht) hRu
      · rw [hinv]
        exact (hkat.differentiableAt (by simp)).hasDerivAt
      · rw [hinv]
        exact hkat
    have hRmem : ∀ᶠ v in 𝓝 u, R.symm v ∈ Ioo C.j0 C.j1 := by
      have hnbd : Ioo C.j0 C.j1 ∈ 𝓝 (R.symm u) := by
        rw [hinv]
        exact isOpen_Ioo.mem_nhds ht
      exact hRsmooth.continuousAt.preimage_mem_nhds hnbd
    have hagree : C.inverseClock =ᶠ[𝓝 u] R.symm := by
      filter_upwards [isOpen_Ioo.mem_nhds hu, hRmem, R.eventually_right_inverse hRu] with v hv hrv hright
      apply hinj (C.inverseClock_mem v hv) hrv
      exact (C.inverseClock_right v hv).trans hright.symm
    exact hRsmooth.congr_of_eventuallyEq hagree
  have hdcont : ContinuousOn (deriv kappa) (Ioo C.j0 C.j1) := by
    have hd := hk.continuousOn_fderiv_of_isOpen isOpen_Ioo (by simp)
    exact hd.clm_apply continuousOn_const
  have hsign : (∀ t ∈ Ioo C.j0 C.j1, 0 < deriv kappa t) ∨
      (∀ t ∈ Ioo C.j0 C.j1, deriv kappa t < 0) := by
    have hdimage := isPreconnected_Ioo.image (deriv kappa) hdcont
    have hdisj : Disjoint (Ioi (0 : ℝ)) (Iio 0) := by
      rw [disjoint_left]
      intro x hx hy
      exact lt_asymm (show 0 < x from hx) (show x < 0 from hy)
    have hcover : deriv kappa '' Ioo C.j0 C.j1 ⊆ Ioi 0 ∪ Iio 0 := by
      rintro x ⟨t, ht, rfl⟩
      rcases lt_or_gt_of_ne (hn t ht) with hneg | hpos
      · exact Or.inr hneg
      · exact Or.inl hpos
    rcases IsPreconnected.subset_or_subset isOpen_Ioi isOpen_Iio hdisj hcover hdimage with hp | hm
    · exact Or.inl (fun t ht => hp (mem_image_of_mem _ ht))
    · exact Or.inr (fun t ht => hm (mem_image_of_mem _ ht))
  exact ⟨hk, hn, hdinv, hinj, C.clock_image, hsign⟩

theorem original_restricted_arc_integral_transport
    (disc : Set E2) (s : E2 → ℝ) (gamma : ℝ → E2) (left right : ℝ)
    (G : SignedArcGeometry disc s gamma left right)
    (C : SignedGraphChart disc s gamma left right)
    (F : E2 → E2) (hF : ContinuousOn F disc)
    (theta : E2 → ℝ) (htheta : ContDiff ℝ ∞ theta) (hc : HasCompactSupport theta)
    (hsupport : tsupport theta ⊆ C.window)
    (a b h : ℝ) (ha : C.a0 < a) (hab : a < b) (hb : b < C.b0)
    (hh : 0 < h) (hheight : h < C.h0)
    (hmargin : (shear C.Q C.sigma C.f ⁻¹' tsupport theta) ⊆ Ioo a b ×ˢ Ioo (-h) h) :
    let W : E2 → E2 := fun x => theta x • F x
    let Z := transformedFlux C.Q C.sigma C.f W
    ∀ positive : Bool,
      IntegrableOn (fun u => (Z (u, 0)).2) (Icc a b) ∧
      IntegrableOn
        (fun t => inner ℝ (F (gamma t)) (signedNormal s positive (gamma t)) *
          theta (gamma t) * ‖fderiv ℝ gamma t 1‖)
        (arcParameters disc gamma left right) ∧
      (if positive then -(∫ u in Icc a b, (Z (u, 0)).2) else ∫ u in Icc a b, (Z (u, 0)).2) =
        ∫ t in arcParameters disc gamma left right,
          inner ℝ (F (gamma t)) (signedNormal s positive (gamma t)) *
            theta (gamma t) * ‖fderiv ℝ gamma t 1‖ := by
  dsimp only
  let W : E2 → E2 := fun x => theta x • F x
  let Z := transformedFlux C.Q C.sigma C.f W
  let kappa : ℝ → ℝ := fun t => (C.Q (gamma t)) 0
  let J := Ioo C.j0 C.j1
  let K := Ioo C.a0 C.b0
  have hθdisc : tsupport theta ⊆ disc :=
    hsupport.trans (subset_closure.trans (C.window_closure_subset.trans C.omega_subset))
  have hj : J ⊆ Ioo left right := Ioo_subset_Icc_self.trans C.parameter_closure
  obtain ⟨hk, hkn, hkInv, hkinj, hkimage, hkorientation⟩ :=
    same_clock_smooth_inverse_and_orientation disc s gamma left right G C
  have hkmem : ∀ t ∈ J, kappa t ∈ K := by
    intro t ht
    change kappa t ∈ Ioo C.a0 C.b0
    rw [← C.clock_image]
    exact mem_image_of_mem _ ht
  have hgraphMem : ∀ u ∈ K, shear C.Q C.sigma C.f (u, 0) ∈ disc := by
    intro u hu
    exact C.omega_subset ⟨(u, 0),
      ⟨hu, neg_lt_zero.mpr C.height_positive, C.height_positive⟩, rfl⟩
  have hJarc : J ⊆ arcParameters disc gamma left right := by
    intro t ht
    refine ⟨hj ht, ?_⟩
    rw [C.gamma_graph t ht]
    exact hgraphMem (kappa t) (hkmem t ht)
  have hWcont : Continuous W :=
    (htheta.continuous.continuousOn.smul hF).continuous_of_tsupport_subset
      G.disc_open ((tsupport_smul_subset_left theta F).trans hθdisc)
  have hIccK : Icc a b ⊆ K := fun u hu => ⟨ha.trans_le hu.1, hu.2.trans_lt hb⟩
  have hcurve : ContinuousOn (fun u => shear C.Q C.sigma C.f (u, 0)) (Icc a b) := by
    apply C.shear_smooth.continuousOn.comp (by fun_prop)
    intro u hu
    exact ⟨hIccK hu, neg_lt_zero.mpr C.height_positive, C.height_positive⟩
  have hdc : ContinuousOn (deriv C.f) (Icc a b) :=
    ((C.graph_smooth.continuousOn_fderiv_of_isOpen isOpen_Ioo (by simp)).clm_apply
      continuousOn_const).mono hIccK
  have hzcont : ContinuousOn (fun u => (Z (u, 0)).2) (Icc a b) := by
    have hx0 : ContinuousOn (fun u => (C.Q (W (shear C.Q C.sigma C.f (u, 0)))) 0) (Icc a b) := by
      exact ((by fun_prop : Continuous (fun x : E2 => (C.Q (W x)) 0))).comp_continuousOn hcurve
    have hx1 : ContinuousOn (fun u => (C.Q (W (shear C.Q C.sigma C.f (u, 0)))) 1) (Icc a b) := by
      exact ((by fun_prop : Continuous (fun x : E2 => (C.Q (W x)) 1))).comp_continuousOn hcurve
    exact (hx1.sub (hdc.mul hx0)).const_mul C.sigma
  have hzint : IntegrableOn (fun u => (Z (u, 0)).2) (Icc a b) :=
    hzcont.integrableOn_compact isCompact_Icc
  have hzout : ∀ u ∉ Icc a b, (Z (u, 0)).2 = 0 := by
    intro u hu
    have htzero : theta (shear C.Q C.sigma C.f (u, 0)) = 0 := by
      by_contra hz
      have hm := hmargin (subset_closure (mem_support.mpr hz))
      exact hu ⟨hm.1.1.le, hm.1.2.le⟩
    have hWzero : W (shear C.Q C.sigma C.f (u, 0)) = 0 := by
      change theta _ • F _ = 0
      rw [htzero, zero_smul]
    change C.sigma * ((C.Q (W (shear C.Q C.sigma C.f (u, 0)))) 1 -
      deriv C.f u * (C.Q (W (shear C.Q C.sigma C.f (u, 0)))) 0) = 0
    rw [hWzero, C.Q.map_zero]
    simp
  have hKint : IntegrableOn (fun u => (Z (u, 0)).2) K :=
    hzint.of_forall_sdiff_eq_zero isOpen_Ioo.measurableSet (fun u hu => hzout u hu.2)
  have hKintEq : (∫ u in Icc a b, (Z (u, 0)).2) = ∫ u in K, (Z (u, 0)).2 :=
    (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Icc a b) (t := K)
      isOpen_Ioo.measurableSet hIccK
      (fun u hu => hzout u hu.2)).symm
  have hnormal := signed_normal_graph_density disc s G.signed_smooth G.disc_open
    C.Q C.frame C.sigma C.sigma_choice C.f C.a0 C.b0 C.graph_smooth
    (fun u hu => ⟨hgraphMem u hu, C.graph_zero u hu⟩)
    (fun u hu => C.transverse_positive (u, 0)
      ⟨hu, neg_lt_zero.mpr C.height_positive, C.height_positive⟩) W
  have hspeed := original_clock_derivative_speed C.Q C.frame C.sigma C.sigma_choice
    C.f gamma C.a0 C.b0 C.j0 C.j1 C.graph_smooth (G.arc_smooth.mono hj)
    hkmem C.gamma_graph
  have hdf : ∀ t ∈ J, HasFDerivWithinAt kappa (fderiv ℝ kappa t) J t := by
    intro t ht
    exact ((hk.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hparam : MeasurableSet (arcParameters disc gamma left right) :=
    (G.arc_smooth.continuousOn.isOpen_inter_preimage isOpen_Ioo G.disc_open).measurableSet
  intro positive
  let g : ℝ → ℝ := fun u => if positive then -(Z (u, 0)).2 else (Z (u, 0)).2
  let i : ℝ → ℝ := fun t => inner ℝ (F (gamma t)) (signedNormal s positive (gamma t)) *
    theta (gamma t) * ‖fderiv ℝ gamma t 1‖
  have hi := compact_arc_test_integrability disc s gamma left right G F hF theta htheta hc hθdisc positive
  have hizero : ∀ t ∈ arcParameters disc gamma left right \ J, i t = 0 := by
    intro t ht
    have htzero : theta (gamma t) = 0 := by
      by_contra hz
      exact ht.2 (C.original_parameter_exclusion t ht.1.1
        (C.window_closure_subset (subset_closure (hsupport (subset_closure (mem_support.mpr hz))))))
    change inner ℝ _ _ * theta (gamma t) * _ = 0
    rw [htzero, mul_zero, zero_mul]
  have hJintEq : (∫ t in J, i t) = ∫ t in arcParameters disc gamma left right, i t :=
    (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := J)
      (t := arcParameters disc gamma left right) hparam hJarc hizero).symm
  have hJacEq : ∀ t ∈ J, |(fderiv ℝ kappa t).det| • g (kappa t) = i t := by
    intro t ht
    obtain ⟨hcoord, hspd, hdet⟩ := hspeed t ht
    obtain ⟨hdensity, hgrad, hnorm, hfalse, htrue, hZfalse, hZtrue⟩ := hnormal (kappa t) (hkmem t ht)
    rw [hdet]
    change |deriv kappa t| * g (kappa t) = i t
    dsimp only [g, i]
    rw [hspd]
    cases positive
    · simp only [Bool.false_eq_true, ite_false]
      rw [hZfalse, ← C.gamma_graph t ht]
      change |deriv kappa t| * (inner ℝ (theta (gamma t) • F (gamma t)) _ * _) = _
      rw [real_inner_smul_left]
      ring
    · simp only [ite_true]
      rw [hZtrue, ← C.gamma_graph t ht]
      change |deriv kappa t| * (inner ℝ (theta (gamma t) • F (gamma t)) _ * _) = _
      rw [real_inner_smul_left]
      ring
  refine ⟨hzint, hi, ?_⟩
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure ℝ) isOpen_Ioo.measurableSet hdf hkinj g
  rw [hkimage] at hchange
  have hri : (∫ t in J, |(fderiv ℝ kappa t).det| • g (kappa t)) = ∫ t in J, i t :=
    setIntegral_congr_fun isOpen_Ioo.measurableSet hJacEq
  have hgi : (if positive then -(∫ u in Icc a b, (Z (u, 0)).2) else ∫ u in Icc a b, (Z (u, 0)).2) =
      ∫ u in K, g u := by
    rw [hKintEq]
    cases positive <;> simp only [g, Bool.false_eq_true, ite_false, ite_true, integral_neg]
  exact hgi.trans (hchange.trans (hri.trans hJintEq))

end SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen
