import B1ActualGeometry_v468
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixB
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
theorem B1_original {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
    (D : B1OriginalData g J) :
    BddAbove {l : ℝ | ∃ s : Circle, ∃ r ∈ Icc (0 : ℝ) D.r0,
      l = |deriv (deriv (D.f s)) r|} ∧
    (∃ s : Circle, B1NormalDerivative D s ≠ 0) ∧
    (∃ ς : ℝ, (ς = 1 ∨ ς = -1) ∧
      ∃ I : ClosedLeafArc J D.boundaryLabel D.leafParameter,
      ∃ a0 r1 : ℝ, 0 < a0 ∧ 0 < r1 ∧ r1 ≤ D.r0 ∧
        ∀ s ∈ I.parameterSet, ∀ r : ℝ, 0 < r → r ≤ r1 →
          (1 / 2 : ℝ) * a0 * r ≤ ς * D.f s r ∧ 0 < (1 / 2 : ℝ) * a0 * r) := by
  classical
  have partial_smooth (f : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
      (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f p.1 p.2) U) :
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => deriv (f p.1) p.2) U := by
    intro p hp
    have h : ContDiffAt ℝ ∞
        (fun q : (ℝ × ℝ) × ℝ => f q.1.1 q.2) (p, p.2) :=
      (hf.contDiffAt (hU.mem_nhds hp)).comp (p,p.2)
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞
        (fun q : ℝ × ℝ => fderiv ℝ (f q.1) q.2) p :=
      h.fderiv contDiffAt_snd (by simp)
    have he := hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
    simpa only [deriv] using he.contDiffWithinAt
  let liftGraph : ℝ × ℝ → Circle × ℝ := fun p => (Circle.exp p.1, p.2)
  let U : Set (ℝ × ℝ) := liftGraph ⁻¹' D.extendedDomain
  have hLift : ContMDiff (𝓘(ℝ, ℝ × ℝ)) ((𝓡 1).prod 𝓘(ℝ)) ∞ liftGraph :=
    (contMDiff_circleExp.comp contDiff_fst.contMDiff).prodMk contDiff_snd.contMDiff
  have hU : IsOpen U := D.extendedDomain_open.preimage hLift.continuous
  have hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => D.f (Circle.exp p.1) p.2) U := by
    exact (D.f_smooth.comp hLift.contMDiffOn (fun _ h => h)).contDiffOn
  have hdf := partial_smooth (fun t r => D.f (Circle.exp t) r) U hU hf
  have hddf := partial_smooth (fun t r => deriv (D.f (Circle.exp t)) r) U hU hdf
  have hbounded : BddAbove {l : ℝ | ∃ s : Circle, ∃ r ∈ Icc (0 : ℝ) D.r0,
      l = |deriv (deriv (D.f s)) r|} := by
    let C : Set (ℝ × ℝ) := Icc (-Real.pi) Real.pi ×ˢ Icc 0 D.r0
    have hCU : C ⊆ U := by
      intro p hp
      exact D.extendedDomain_contains hp.2
    have hb := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
      (hddf.continuousOn.abs.mono hCU)
    apply hb.mono
    rintro l ⟨s,r,hr,rfl⟩
    refine ⟨(Complex.arg s, r), ?_, ?_⟩
    · exact ⟨⟨(Complex.neg_pi_lt_arg s).le, Complex.arg_le_pi s⟩,hr⟩
    · simp only [Circle.exp_arg]
  have hradial_smooth (s : Circle) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.r0) :
      ContDiffAt ℝ ∞ (D.f s) r := by
    have h := D.f_smooth.contMDiffAt
      (D.extendedDomain_open.mem_nhds (D.extendedDomain_contains (show (s,r) ∈ radialCylinder D.r0 from hr)))
    exact (h.comp r (contMDiffAt_const.prodMk contMDiffAt_id)).contDiffAt
  have hderivative (s : Circle) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.r0) :
      HasDerivAt (D.f s) (deriv (D.f s) r) r :=
    ((hradial_smooth s r hr).differentiableAt (by simp)).hasDerivAt
  have hsecond (s : Circle) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.r0) :
      HasDerivAt (deriv (D.f s)) (deriv (deriv (D.f s)) r) r :=
    (((hradial_smooth s r hr).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hnormal_continuous : Continuous (B1NormalDerivative D) := by
    have hpull : Continuous (fun t : ℝ => deriv (D.f (Circle.exp t)) 0) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      have hmem : (t,(0 : ℝ)) ∈ U := D.extendedDomain_contains ⟨le_rfl,D.r0_pos.le⟩
      exact ((hdf.contDiffAt (hU.mem_nhds hmem)).comp t
        (contDiffAt_id.prodMk contDiffAt_const)).continuousAt
    have hq := Circle.isCoveringMap_exp.isOpenMap.isQuotientMap
      Circle.exp.continuous Circle.exp_surjective
    exact hq.continuous_iff.mpr hpull
  have hbounded_final := hbounded
  obtain ⟨M,hM⟩ := hbounded
  let F : RadialC2Family Circle :=
    { f := D.f
      df := fun s r => deriv (D.f s) r
      ddf := fun s r => deriv (deriv (D.f s)) r
      r₀ := D.r0
      r₀_pos := D.r0_pos
      Λ := max 0 M
      Λ_nonneg := le_max_left _ _
      zero := D.f_boundary_zero
      derivative := hderivative
      second_derivative := hsecond
      second_bound := by
        intro s r hr
        exact (hM ⟨s,r,hr,rfl⟩).trans (le_max_right _ _) }
  have hboundary_critical (s : Circle) :
      mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
        (fun p : Circle × ℝ => D.f p.1 p.2) (s,0) = 0 ↔
      B1NormalDerivative D s = 0 := by
    have hpoint : (s,(0 : ℝ)) ∈ D.extendedDomain :=
      D.extendedDomain_contains ⟨le_rfl,D.r0_pos.le⟩
    have hsmooth := D.f_smooth.contMDiffAt (D.extendedDomain_open.mem_nhds hpoint)
    have hmd := hsmooth.mdifferentiableAt (by simp)
    have hz : (fun t : Circle => D.f t 0) = fun _ => (0 : ℝ) :=
      funext D.f_boundary_zero
    have hsplit (w : TangentSpace ((𝓡 1).prod 𝓘(ℝ)) (s,(0 : ℝ))) :
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
          (fun p : Circle × ℝ => D.f p.1 p.2) (s,0) w =
        mfderiv 𝓘(ℝ) 𝓘(ℝ) (D.f s) 0 w.2 := by
      rw [mfderiv_prod_eq_add_apply hmd,hz,mfderiv_const]
      change (0 : ℝ) + _ = _
      exact zero_add _
    have hright : mfderiv 𝓘(ℝ) 𝓘(ℝ) (D.f s) 0 = 0 ↔ deriv (D.f s) 0 = 0 := by
      constructor
      · intro h
        have he := congrArg (fun L =>
          (NormedSpace.fromTangentSpace (D.f s 0))
            (L ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))) h
        rw [mfderiv_eq_fderiv] at he
        simpa only [ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply,
          zero_apply,map_zero,fderiv_apply_one_eq_deriv] using he
      · intro h
        have hf0 : fderiv ℝ (D.f s) 0 = 0 := by
          apply ContinuousLinearMap.ext
          intro x
          simp only [fderiv_eq_deriv_mul,h,zero_mul,zero_apply]
        rw [mfderiv_eq_fderiv,hf0]
        simp
    change _ ↔ deriv (D.f s) 0 = 0
    rw [← hright]
    constructor
    · intro h
      apply ContinuousLinearMap.ext
      intro x
      calc
        mfderiv 𝓘(ℝ) 𝓘(ℝ) (D.f s) 0 x =
            mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
              (fun p : Circle × ℝ => D.f p.1 p.2) (s,0) (0,x) :=
          (hsplit (0,x)).symm
        _ = 0 := by rw [h]; rfl
    · intro h
      apply ContinuousLinearMap.ext
      intro w
      calc
        _ = mfderiv 𝓘(ℝ) 𝓘(ℝ) (D.f s) 0 w.2 := hsplit w
        _ = 0 := by rw [h]; rfl
  have horiginal_prop57 :
      ∃ rho : ℝ, 0 < rho ∧ rho ≤ D.r0 ∧
        (∀ s : Circle, ∀ r ∈ Ioo (0 : ℝ) rho,
          mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
            (fun p : Circle × ℝ => D.f p.1 p.2) (s,r) ≠ 0) ∧
        Set.Finite {s : Circle |
          mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
            (fun p : Circle × ℝ => D.f p.1 p.2) (s,0) = 0} := by
    exact original_prop57_tangencies D
  obtain ⟨rho,hrho,hrhor0,hopen,hfinite⟩ := horiginal_prop57
  have hfinite_normal : Set.Finite {s : Circle | B1NormalDerivative D s = 0} :=
    hfinite.subset (fun s hs => (hboundary_critical s).mpr hs)
  haveI : Infinite (Icc (0 : ℝ) Real.pi) := Set.Icc.infinite Real.pi_pos
  haveI : Infinite Circle := Infinite.of_injective
    (fun t : Icc (0 : ℝ) Real.pi => Circle.exp t)
    (fun x y h => Subtype.ext (Circle.exp_injOn_Icc
      (by linarith [Real.pi_pos] : Real.pi-0 < 2*Real.pi) x.property y.property h))
  have hnonzero : ∃ s : Circle, B1NormalDerivative D s ≠ 0 :=
    finite_zeros_not_identically_zero (B1NormalDerivative D) hfinite_normal
  refine ⟨hbounded_final,hnonzero,?_⟩
  obtain ⟨s0,hs0⟩ := hnonzero
  obtain ⟨ς,hς,V,hV,hsV,a0,ha0,r1,hr1,hr1bound,hlower⟩ :=
    uniform_radial_sign_on_neighborhood F hnormal_continuous s0 hs0
  let t0 : ℝ := Complex.arg s0
  have ht0 : t0 ∈ Circle.exp ⁻¹' V := by simpa [t0] using hsV
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp
    ((hV.preimage Circle.exp.continuous).mem_nhds ht0)
  let e : ℝ := min (d/2) (Real.pi/2)
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have hed : e < d := by have := min_le_left (d/2) (Real.pi/2); dsimp [e]; linarith
  have hep : e ≤ Real.pi/2 := min_le_right _ _
  let a : ℝ := t0-e
  let b : ℝ := t0+e
  have hab : a < b := by dsimp [a,b]; linarith
  have hsmall : b-a < 2*Real.pi := by dsimp [a,b]; linarith [Real.pi_pos]
  let Pset : Set Circle := Circle.exp '' Icc a b
  have hPcompact : IsCompact Pset := isCompact_Icc.image Circle.exp.continuous
  have hPV : Pset ⊆ V := by
    rintro s ⟨t,ht,rfl⟩
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [a,b] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hexp : IsEmbedding (fun t : Icc a b => Circle.exp t) :=
    ((Circle.exp.continuous.comp continuous_subtype_val).isClosedEmbedding
      (fun x y h => Subtype.ext (Circle.exp_injOn_Icc hsmall x.property y.property h))).isEmbedding
  have hrange : range (fun t : Icc a b => Circle.exp t) = Pset := by
    ext s
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨t,t.property,rfl⟩
    · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,rfl⟩
  let hP : Icc (0 : ℝ) 1 ≃ₜ Pset :=
    (iccHomeoI a b hab).symm.trans (hexp.toHomeomorph.trans (Homeomorph.setCongr hrange))
  have hleaf : IsEmbedding D.leafParameter := D.leafParameter_embedding.isEmbedding
  let imageSet : Set E.Carrier := D.leafParameter '' Pset
  let I : ClosedLeafArc J D.boundaryLabel D.leafParameter :=
    { parameterSet := Pset
      parameterSet_closed := hPcompact.isClosed
      parameterHomeomorph := hP
      carrier := imageSet
      carrier_exact := rfl
      carrier_closed := (hPcompact.image hleaf.continuous).isClosed
      leaf_subset := by
        rintro x ⟨s,hs,rfl⟩
        rw [← D.leafParameter_image]
        exact mem_range_self s
      intervalHomeomorph := hP.trans (hleaf.homeomorphImage Pset) }
  have hr1r0 : r1 ≤ D.r0 := by
    change r1 ≤ D.r0/4 at hr1bound
    linarith [D.r0_pos]
  refine ⟨ς,hς,I,a0,r1,ha0,hr1,hr1r0,?_⟩
  intro s hs r hr hrr
  have hl := (hlower s (hPV hs) r ⟨hr,hrr⟩).1
  constructor
  · change (1/2 : ℝ)*a0*r ≤ ς*F.f s r
    nlinarith
  · positivity

end SeifertSurfaces.OriginalEndpoints

#print axioms SeifertSurfaces.OriginalEndpoints.B1_original
