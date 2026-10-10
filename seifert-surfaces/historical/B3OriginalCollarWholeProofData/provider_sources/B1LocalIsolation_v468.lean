import B1FiniteTransport_v468
import B1NativeBoundaryChart_v466
import B1Globalization_v468
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem actual_boundary_local_isolation (D : B1OriginalData g J) (s : Circle) :
    LocalBoundaryIsolation D s := by
  have noncritical_boundary_isolation (D : B1OriginalData g J) (s : Circle)
      (hcritical : mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
        (fun p : Circle × ℝ => D.f p.1 p.2) (s, 0) ≠ 0) :
      LocalBoundaryIsolation D s := by
    let I := (𝓡 1).prod 𝓘(ℝ)
    let f : Circle × ℝ → ℝ := fun p => D.f p.1 p.2
    let p0 : Circle × ℝ := (s, 0)
    let A := inTangentCoordinates I 𝓘(ℝ) id f (mfderiv I 𝓘(ℝ) f) p0
    have hp0 : p0 ∈ D.extendedDomain := D.extendedDomain_contains ⟨le_rfl, D.r0_pos.le⟩
    have hsmooth := D.f_smooth.contMDiffAt (D.extendedDomain_open.mem_nhds hp0)
    have hAcont : ContinuousAt A p0 := (hsmooth.mfderiv_const (m := 0) (by simp)).continuousAt
    have hAne : A p0 ≠ 0 := by
      intro hzero
      apply hcritical
      let e1 := (trivializationAt (EuclideanSpace ℝ (Fin 1) × ℝ) (TangentSpace I) p0).continuousLinearEquivAt ℝ p0
        (FiberBundle.mem_baseSet_trivializationAt _ _ p0)
      let e2 := (trivializationAt ℝ (TangentSpace 𝓘(ℝ)) (f p0)).continuousLinearEquivAt ℝ (f p0)
        (FiberBundle.mem_baseSet_trivializationAt _ _ (f p0))
      change inTangentCoordinates I 𝓘(ℝ) id f (mfderiv I 𝓘(ℝ) f) p0 p0 = 0 at hzero
      dsimp only [inTangentCoordinates, id_eq] at hzero
      rw [ContinuousLinearMap.inCoordinates_eq
        (F := EuclideanSpace ℝ (Fin 1) × ℝ) (E := TangentSpace I)
        (F' := ℝ) (E' := TangentSpace 𝓘(ℝ))
        (FiberBundle.mem_baseSet_trivializationAt _ _ p0)
        (FiberBundle.mem_baseSet_trivializationAt _ _ (f p0))] at hzero
      apply ContinuousLinearMap.ext
      intro v
      have hv := congrArg (fun L => e2.symm (L (e1 v))) hzero
      change e2.symm (e2 ((mfderiv I 𝓘(ℝ) f p0) (e1.symm (e1 v)))) = e2.symm 0 at hv
      simp only [ContinuousLinearEquiv.symm_apply_apply, map_zero] at hv
      convert hv using 1 <;> rfl
    obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp (hAcont.eventually_ne hAne)
    refine ⟨U, hUopen, hpU, ?_⟩
    intro p hp _ hz
    apply hUsub hp.1
    change inTangentCoordinates I 𝓘(ℝ) id f (mfderiv I 𝓘(ℝ) f) p0 p = 0
    have hzp : mfderiv I 𝓘(ℝ) f p = 0 := hz
    simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, hzp]
    apply ContinuousLinearMap.ext
    intro v
    change ((trivializationAt ℝ (TangentSpace 𝓘(ℝ)) (f p0)).continuousLinearMapAt ℝ (f p)) 0 = 0
    exact map_zero _


  have local_parameter_contMDiff (D : B1OriginalData g J) (s : Circle) :
      ContMDiff 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ)) ∞
        (fun x : E2 => (localCircle D s (x 0), x 1)) := by
    apply ContMDiff.prodMk
    · change ContMDiff 𝓘(ℝ, E2) (𝓡 1) ∞
        (fun x : E2 => s * Circle.exp (2 * Real.pi * x 0 / D.leafLength))
      apply ContMDiff.mul contMDiff_const
      apply contMDiff_circleExp.comp
      apply ContDiff.contMDiff
      fun_prop
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.contMDiff

  have critical_local_height_at (D : B1OriginalData g J) (s : Circle) (x : E2)
      (hx : (localCircle D s (x 0), x 1) ∈ radialCylinder D.r0)
      (hc : mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
        (fun p : Circle × ℝ => D.f p.1 p.2) (localCircle D s (x 0), x 1) = 0) :
      fderiv ℝ (localHeight D s) x = 0 := by
    let c : E2 → Circle × ℝ := fun x => (localCircle D s (x 0), x 1)
    have hf := (D.f_smooth.contMDiffAt (D.extendedDomain_open.mem_nhds
      (D.extendedDomain_contains hx))).mdifferentiableAt (by simp)
    have hdf : HasMFDerivAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
        (fun p : Circle × ℝ => D.f p.1 p.2) (c x) 0 := by
      simpa only [hc] using hf.hasMFDerivAt
    have hcomp := hdf.comp x (((local_parameter_contMDiff D s).mdifferentiable (by simp)) x).hasMFDerivAt
    have hmder := hcomp.mfderiv
    have hfun : (fun p : Circle × ℝ => D.f p.1 p.2) ∘ c = localHeight D s := by
      funext y
      rfl
    rw [hfun, ContinuousLinearMap.zero_comp, mfderiv_eq_fderiv] at hmder
    apply ContinuousLinearMap.ext
    intro v
    have hvalue := congrArg
      (fun L => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (localHeight D s x))
        (L ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm v))) hmder
    convert hvalue using 1 <;> rfl

  have local_inverse_neighborhood (D : B1OriginalData g J) (s : Circle)
      (d : ℝ) (hd : 0 < d) :
      ∃ U : Set (Circle × ℝ), IsOpen U ∧ (s, 0) ∈ U ∧
        ∀ p ∈ U, ∃ x : E2, ‖x‖ < d ∧ (localCircle D s (x 0), x 1) = p := by
    let q : Circle × ℝ → E2 := fun p => (EuclideanSpace.equiv (Fin 2) ℝ).symm
      ![D.leafLength / (2 * Real.pi) * Complex.arg ((s⁻¹ * p.1 : Circle) : ℂ), p.2]
    have hq0 : q (s, 0) = 0 := by
      ext i
      fin_cases i <;> simp [q]
    have harg : ContinuousAt (fun p : Circle × ℝ => Complex.arg ((s⁻¹ * p.1 : Circle) : ℂ)) (s, 0) := by
      have hc : ContinuousAt (fun p : Circle × ℝ => ((s⁻¹ * p.1 : Circle) : ℂ)) (s, 0) := by fun_prop
      have ha : ContinuousAt Complex.arg (((s⁻¹ * s : Circle) : ℂ)) := by
        simpa using Complex.continuousAt_arg Complex.one_mem_slitPlane
      exact ContinuousAt.comp (f := fun p : Circle × ℝ => ((s⁻¹ * p.1 : Circle) : ℂ))
        (g := Complex.arg) (x := (s, (0 : ℝ))) ha hc
    have hq : ContinuousAt q (s, 0) := by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.continuousAt.comp
      apply continuousAt_pi.mpr
      intro i
      fin_cases i
      · exact continuousAt_const.mul harg
      · exact continuousAt_snd
    have hnear : ∀ᶠ p in 𝓝 (s, (0 : ℝ)), ‖q p‖ < d := by
      exact hq.norm.eventually_lt_const (by simpa only [hq0, norm_zero] using hd)
    obtain ⟨U, hUsub, hUopen, hUmem⟩ := mem_nhds_iff.mp hnear
    refine ⟨U, hUopen, hUmem, ?_⟩
    intro p hp
    refine ⟨q p, hUsub hp, ?_⟩
    apply Prod.ext
    · change s * Circle.exp (2 * Real.pi * (D.leafLength / (2 * Real.pi) *
        Complex.arg ((s⁻¹ * p.1 : Circle) : ℂ)) / D.leafLength) = p.1
      have ha : 2 * Real.pi * (D.leafLength / (2 * Real.pi) *
          Complex.arg ((s⁻¹ * p.1 : Circle) : ℂ)) / D.leafLength =
          Complex.arg ((s⁻¹ * p.1 : Circle) : ℂ) := by
        field_simp [ne_of_gt D.leafLength_pos, ne_of_gt Real.pi_pos]
      rw [ha, Circle.exp_arg]
      simp
    · rfl

  classical
  by_cases hc : mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
      (fun q : Circle × ℝ => D.f q.1 q.2) (s, 0) = 0
  · obtain ⟨W⟩ := actual_collar_window D s
    obtain ⟨N⟩ := small_half_disc_positive_solution D s W
    obtain ⟨F⟩ := inverse_metric_boundary_isothermal_coordinates D s W N
    obtain ⟨hw, heq, hlp⟩ := same_reflected_gradient_vekua_equation D s W N F
    obtain ⟨hA, hB⟩ := hlp 3 (by norm_num)
    obtain ⟨S⟩ := weak_vekua_similarity F.targetR F.targetR_pos F.w
      (vekuaA F.reflectedB) (vekuaB F.reflectedB) hw heq 3 (by norm_num) hA hB
    obtain ⟨m, hm, d, c1, c2, C, hd, hdR, hc1, hc2, hC, hb⟩ :=
      finite_order_transport_to_same_difference D s W N F S hc
    obtain ⟨U, hUopen, hUmem, hU⟩ := local_inverse_neighborhood D s d hd
    refine ⟨U, hUopen, hUmem, ?_⟩
    intro p hp hne hcrit
    obtain ⟨x, hxnorm, hxp⟩ := hU p hp.1
    have hxpos : 0 ≤ x 1 := by
      have h := hp.2.1
      rw [← hxp] at h
      exact h
    have hx : x ∈ closedHalfDisc d :=
      ⟨by simpa [closedDisc] using hxnorm.le, hxpos⟩
    have hxne : x ≠ 0 := by
      intro hzero
      apply hne
      rw [← hxp, hzero]
      simp [localCircle]
    have hdzero : fderiv ℝ (localHeight D s) x = 0 :=
      critical_local_height_at D s x (hxp.symm ▸ hp.2) (hxp.symm ▸ hcrit)
    have hgradzero : planarGradient (localHeight D s) x = 0 := by
      simp [planarGradient, hdzero]
    obtain ⟨hlow, hpos, _⟩ := hb x hx hxne
    rw [hgradzero, norm_zero] at hlow
    exact (not_lt_of_ge hlow) hpos
  · exact noncritical_boundary_isolation D s hc

end SeifertSurfaces.OriginalEndpoints.B1Tangency
