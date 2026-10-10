import AnalyticLongitudeProducers
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology
open Manifold IsManifold
namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
universe u v
noncomputable section

def complexPlane (w : ℂ) : Euc 2 := !₂[w.re, w.im]
def unitVector (z : Circle) : Euc 2 := complexPlane (z : ℂ)

theorem complexPlane_isometry :
    ∃ R : ℂ ≃ₗᵢ[ℝ] Euc 2, (R : ℂ → Euc 2) = complexPlane := by
  exact ⟨Complex.orthonormalBasisOneI.repr, rfl⟩
theorem unitVector_norm (z : Circle) : ‖unitVector z‖ = 1 := by
  rcases complexPlane_isometry with ⟨R, hR⟩
  rw [unitVector, ← hR, R.norm_map]
  exact Circle.norm_coe z
theorem unitVector_smooth : ContMDiff (𝓡 1) 𝓘(ℝ, Euc 2) ∞ unitVector := by
  rcases complexPlane_isometry with ⟨R, hR⟩
  letI : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere
  change ContMDiff (𝓡 1) 𝓘(ℝ, Euc 2) ∞ (fun z : Circle => complexPlane (z : ℂ))
  rw [← hR]
  exact R.toContinuousLinearEquiv.contDiff.contMDiff.comp hc
theorem unitVector_smoothEmbedding :
    Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, Euc 2) ∞ unitVector := by
  letI : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  rcases complexPlane_isometry with ⟨R, hR⟩
  have hinj : Function.Injective unitVector := by
    intro a b h
    apply Subtype.ext
    apply R.injective
    simpa only [hR, unitVector] using h
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
    (by simp) unitVector_smooth ?_, unitVector_smooth.continuous.isClosedEmbedding hinj |>.isEmbedding⟩
  intro z
  have hc : IsDiffImmersionAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) z :=
    IsDiffImmersionAt.of_injective_of_finiteDimensional (mfderiv_coe_sphere_injective z)
  have h : IsDiffImmersionAt (𝓡 1) 𝓘(ℝ, Euc 2) unitVector z := by
    change IsDiffImmersionAt (𝓡 1) 𝓘(ℝ, Euc 2)
      (fun z : Circle => complexPlane (z : ℂ)) z
    rw [← hR]
    exact R.toContinuousLinearEquiv.isDiffImmersionAt.comp hc
  exact h.mfderiv_injective
theorem unitVector_range : Set.range unitVector = Metric.sphere (0 : Euc 2) 1 := by
  rcases complexPlane_isometry with ⟨R, hR⟩
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    simpa only [Metric.mem_sphere, dist_zero_right] using unitVector_norm z
  · intro hx
    have hn : ‖R.symm x‖ = 1 := by
      simpa only [R.symm.norm_map, Metric.mem_sphere, dist_zero_right] using hx
    refine ⟨⟨R.symm x, mem_sphere_zero_iff_norm.mpr hn⟩, ?_⟩
    change complexPlane (R.symm x) = x
    rw [← hR, R.apply_symm_apply]
theorem unitVector_mem_tubeDisk (z : Circle) : unitVector z ∈ tubeDiskOpen := by
  change dist (unitVector z) 0 < 2
  rw [dist_zero_right, unitVector_norm]
  norm_num
def unitDisk (z : Circle) : TubeDisk := ⟨unitVector z, unitVector_mem_tubeDisk z⟩

variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
def rawShellSphere (p : Circle × Circle) : ThreeSphere := T.tube 0 (p.2, unitDisk p.1)
theorem rawShellSphere_range : Set.range (@rawShellSphere K T) = T.shell 0 := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(p.2, unitDisk p.1), unitVector_norm p.1, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    have hm : (p.2 : Euc 2) ∈ Set.range unitVector := by
      rw [unitVector_range]
      simpa only [Metric.mem_sphere, dist_zero_right] using (show ‖(p.2 : Euc 2)‖ = 1 from hp)
    rcases hm with ⟨z, hz⟩
    refine ⟨(z, p.1), ?_⟩
    change T.tube 0 (p.1, unitDisk z) = T.tube 0 p
    congr 1
    exact Prod.ext rfl (Subtype.ext hz)
theorem rawShellSphere_injective : Function.Injective (@rawShellSphere K T) := by
  rcases complexPlane_isometry with ⟨R, hR⟩
  intro p q hpq
  have h := (T.smoothEmbedding 0).isEmbedding.injective hpq
  have h₂ : p.2 = q.2 := congrArg Prod.fst h
  have h₁ : unitVector p.1 = unitVector q.1 :=
    congrArg (fun a : TubeDomain => (a.2 : Euc 2)) h
  apply Prod.ext _ h₂
  apply Subtype.ext
  apply R.injective
  simpa only [hR, unitVector] using h₁
theorem rawShellSphere_continuous : Continuous (@rawShellSphere K T) := by
  have hc : Continuous unitDisk := unitVector_smooth.continuous.subtype_mk _
  exact (T.smoothEmbedding 0).isEmbedding.continuous.comp
    (continuous_snd.prodMk (hc.comp continuous_fst))
theorem rawShellSphere_smoothEmbedding :
    Manifold.IsSmoothEmbedding TorusModel (𝓡 3) ∞ (@rawShellSphere K T) := by
  have hud : ContMDiff (𝓡 1) 𝓘(ℝ, Euc 2) ∞ unitDisk :=
    (ContMDiff.subtypeVal_comp_iff tubeDiskOpen unitDisk).mp unitVector_smooth
  have hsmooth : ContMDiff TorusModel (𝓡 3) ∞ (@rawShellSphere K T) :=
    (T.smoothEmbedding 0).contMDiff.comp
      (contMDiff_snd.prodMk (hud.comp contMDiff_fst))
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
    (by simp) hsmooth ?_, rawShellSphere_continuous.isClosedEmbedding rawShellSphere_injective |>.isEmbedding⟩
  intro p
  have huv := unitVector_smoothEmbedding.isImmersion.isDiffImmersionAt (by simp) p.1
  have hd : IsDiffImmersionAt (𝓡 1) 𝓘(ℝ, Euc 2) unitDisk p.1 :=
    IsDiffImmersionAt.of_comp (hud.mdifferentiable (by simp) p.1)
      ((Manifold.IsSmoothEmbedding.of_opens (n := ∞) tubeDiskOpen).contMDiff.mdifferentiable
        (by simp) (unitDisk p.1)) huv
  have hswap : IsDiffImmersionAt TorusModel TorusModel Prod.swap p :=
    ((Diffeomorph.prodComm (𝓡 1) (𝓡 1) Circle Circle ∞).isLocalDiffeomorph p).isDiffImmersionAt
      (by simp)
  have hid : IsDiffImmersionAt (𝓡 1) (𝓡 1) (@id Circle) p.2 :=
    (Manifold.IsImmersion.id (n := ∞)).isDiffImmersionAt (by simp) p.2
  have hp : IsDiffImmersionAt TorusModel ((𝓡 1).prod 𝓘(ℝ, Euc 2))
      (Prod.map (@id Circle) unitDisk) (p.2, p.1) := by
    apply IsDiffImmersionAt.of_injective_of_finiteDimensional
    rw [mfderiv_prodMap hid.mdifferentiableAt hd.mdifferentiableAt]
    intro a b hab
    exact Prod.ext (hid.mfderiv_injective (congrArg Prod.fst hab))
      (hd.mfderiv_injective (congrArg Prod.snd hab))
  have hcoords : IsDiffImmersionAt TorusModel ((𝓡 1).prod 𝓘(ℝ, Euc 2))
      (fun q => (q.2, unitDisk q.1)) p :=
    IsDiffImmersionAt.comp (f := Prod.swap) hp hswap
  exact (IsDiffImmersionAt.comp
    (f := fun q : Circle × Circle => (q.2, unitDisk q.1))
    ((T.smoothEmbedding 0).isImmersion.isDiffImmersionAt (by simp)
      (p.2, unitDisk p.1)) hcoords).mfderiv_injective
theorem rawShellSphere_exterior (p : Circle × Circle) :
    @rawShellSphere K T p ∈ T.exteriorSet := by
  change rawShellSphere p ∉ ⋃ i, T.openTube i
  intro hp
  rcases Set.mem_iUnion.mp hp with ⟨i, q, hq, heq⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have h := (T.smoothEmbedding 0).isEmbedding.injective heq
  have hn : ‖(q.2 : Euc 2)‖ = 1 := by
    rw [congrArg (fun a : TubeDomain => (a.2 : Euc 2)) h]
    exact unitVector_norm p.1
  exact (lt_irrefl (1 : ℝ)) (hn ▸ hq)
def rawShellTorus (p : Circle × Circle) : E.Carrier :=
  ⟨rawShellSphere (T := T) p, rawShellSphere_exterior p⟩
theorem rawShellTorus_range : Set.range (rawShellTorus E) = (𝓡∂ 3).boundary E.Carrier := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    have hm : rawShellSphere p ∈ ⋃ i, T.shell i :=
      Set.mem_iUnion.mpr ⟨0, rawShellSphere_range ▸ Set.mem_range_self p⟩
    rw [← E.boundary_image] at hm
    rcases hm with ⟨y, hy, heq⟩
    have hxy : y = rawShellTorus E p := Subtype.ext heq
    exact hxy ▸ hy
  · intro hx
    have hm : E.toSphere x ∈ ⋃ i, T.shell i := by
      rw [← E.boundary_image]
      exact ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.mp hm with ⟨i, hi⟩
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst i
    rw [← rawShellSphere_range] at hi
    rcases hi with ⟨p, hp⟩
    exact ⟨p, Subtype.ext hp⟩
theorem rawShellTorus_continuous : Continuous (rawShellTorus E) := by
  exact rawShellSphere_continuous.subtype_mk _
theorem rawShellTorus_smooth : ContMDiff TorusModel (𝓡∂ 3) ∞ (rawShellTorus E) := by
  letI : ChartedSpace (EuclideanHalfSpace 3) T.Carrier := E.charted
  have hi : Manifold.IsImmersion (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion.isImmersion
  apply (ContMDiff.iff_comp_isImmersion hi).mpr
  refine ⟨rawShellTorus_continuous E, ?_⟩
  have hu : ContMDiff (𝓡 1) 𝓘(ℝ, Euc 2) ∞ unitDisk :=
    (ContMDiff.subtypeVal_comp_iff tubeDiskOpen unitDisk).mp unitVector_smooth
  exact (T.smoothEmbedding 0).contMDiff.comp
    (contMDiff_snd.prodMk (hu.comp contMDiff_fst))
theorem rawShellTorus_differential_injective :
    ∀ p, Function.Injective (mfderiv TorusModel (𝓡∂ 3) (rawShellTorus E) p) := by
  intro p
  letI : ChartedSpace (EuclideanHalfSpace 3) T.Carrier := E.charted
  letI : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  rcases complexPlane_isometry with ⟨R, hR⟩
  have hcoe : IsDiffImmersionAt (𝓡 1) 𝓘(ℝ, ℂ)
      (fun z : Circle => (z : ℂ)) p.1 :=
    IsDiffImmersionAt.of_injective_of_finiteDimensional
      (mfderiv_coe_sphere_injective p.1)
  have huv : IsDiffImmersionAt (𝓡 1) 𝓘(ℝ, Euc 2) unitVector p.1 := by
    change IsDiffImmersionAt (𝓡 1) 𝓘(ℝ, Euc 2)
      (fun z : Circle => complexPlane (z : ℂ)) p.1
    rw [← hR]
    exact R.toContinuousLinearEquiv.isDiffImmersionAt.comp hcoe
  have hud : ContMDiff (𝓡 1) 𝓘(ℝ, Euc 2) ∞ unitDisk :=
    (ContMDiff.subtypeVal_comp_iff tubeDiskOpen unitDisk).mp unitVector_smooth
  have hd : IsDiffImmersionAt (𝓡 1) 𝓘(ℝ, Euc 2) unitDisk p.1 :=
    IsDiffImmersionAt.of_comp (hud.mdifferentiable (by simp) p.1)
      ((Manifold.IsSmoothEmbedding.of_opens (n := ∞) tubeDiskOpen).contMDiff.mdifferentiable
        (by simp) (unitDisk p.1)) huv
  have hswap : IsDiffImmersionAt TorusModel TorusModel
      Prod.swap p :=
    ((Diffeomorph.prodComm (𝓡 1) (𝓡 1) Circle Circle ∞).isLocalDiffeomorph p).isDiffImmersionAt
      (by simp)
  have hid : IsDiffImmersionAt (𝓡 1) (𝓡 1) (@id Circle) p.2 :=
    (Manifold.IsImmersion.id (n := ∞)).isDiffImmersionAt (by simp) p.2
  have hp : IsDiffImmersionAt TorusModel ((𝓡 1).prod 𝓘(ℝ, Euc 2))
      (Prod.map (@id Circle) unitDisk) (p.2, p.1) := by
    apply IsDiffImmersionAt.of_injective_of_finiteDimensional
    rw [mfderiv_prodMap hid.mdifferentiableAt hd.mdifferentiableAt]
    intro a b hab
    apply Prod.ext
    · exact hid.mfderiv_injective (congrArg Prod.fst hab)
    · exact hd.mfderiv_injective (congrArg Prod.snd hab)
  have hcoords : IsDiffImmersionAt TorusModel
      ((𝓡 1).prod 𝓘(ℝ, Euc 2)) (fun q => (q.2, unitDisk q.1)) p := by
    exact IsDiffImmersionAt.comp (f := Prod.swap) hp hswap
  have hs : IsDiffImmersionAt TorusModel (𝓡 3)
      (@rawShellSphere K T) p :=
    IsDiffImmersionAt.comp (f := fun q : Circle × Circle => (q.2, unitDisk q.1))
      ((T.smoothEmbedding 0).isImmersion.isDiffImmersionAt (by simp)
        (p.2, unitDisk p.1)) hcoords
  have hi : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion.contMDiff
  exact (IsDiffImmersionAt.of_comp
    ((rawShellTorus_smooth E).mdifferentiable (by simp) p)
    (hi.mdifferentiable (by simp) (rawShellTorus E p)) hs).mfderiv_injective

/-- T1: the precise missing codimension-one boundary normal-form criterion.
Smoothness/rank do not by themselves abbreviate IsImmersion. -/
theorem boundary_plane_immersion
    {V H X Y : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace H]
    (I : ModelWithCorners ℝ V H) [I.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 3) Y]
    [IsManifold (𝓡∂ 3) ∞ Y] (hdim : Module.finrank ℝ V = 2)
    (f : X → Y) (hf : ContMDiff I (𝓡∂ 3) ∞ f)
    (hboundary : ∀ x, f x ∈ (𝓡∂ 3).boundary Y)
    (hinj : ∀ x, Function.Injective (mfderiv I (𝓡∂ 3) f x)) :
    Manifold.IsImmersion I (𝓡∂ 3) ∞ f := by
  classical
  let : CompleteSpace V := FiniteDimensional.complete ℝ V
  let P : Euc 3 ≃L[ℝ] Euc 1 × Euc 2 :=
    EuclideanSpace.finAddEquivProd (n := 1) (m := 2)
  let L : V ≃L[ℝ] Euc 2 := ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  let A : (V × Euc 1) ≃L[ℝ] Euc 3 :=
    ((ContinuousLinearEquiv.prodCongr L (ContinuousLinearEquiv.refl ℝ (Euc 1))).trans
      (ContinuousLinearEquiv.prodComm ℝ (Euc 2) (Euc 1))).trans P.symm
  apply IsImmersionOfComplement.isImmersion (F := Euc 1)
  intro x
  let c := extChartAtPartialDiffeomorph I ∞ x
  let d := extChartAt (𝓡∂ 3) (f x)
  let g : V → Euc 3 := d ∘ f ∘ c.symm
  let U : Set V := c.target ∩ c.symm ⁻¹' (f ⁻¹' d.source)
  have hU : IsOpen U := c.toOpenPartialHomeomorph.isOpen_inter_preimage_symm
    (isOpen_extChartAt_source (f x) |>.preimage hf.continuous)
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hfd : f x ∈ d.source := mem_extChartAt_source (f x)
  have hcx : c.symm (c x) = x := c.left_inv hxc
  have hxU : c x ∈ U := by
    refine ⟨c.map_source hxc, ?_⟩
    change f (c.symm (c x)) ∈ d.source
    rw [hcx]
    exact hfd
  have hg : ContDiffOn ℝ ∞ g U := by
    have hs : ContMDiffOn 𝓘(ℝ, V) (𝓡∂ 3) ∞ (f ∘ c.symm) U :=
      hf.comp_contMDiffOn (c.symm.contMDiffOn.mono inter_subset_left)
    have hmaps : MapsTo (f ∘ c.symm) U (chartAt (EuclideanHalfSpace 3) (f x)).source := by
      intro w hw
      simpa only [d, extChartAt_source, mem_preimage, Function.comp_apply] using hw.2
    exact ((contMDiffOn_extChartAt (I := 𝓡∂ 3) (n := ∞) (x := f x)).comp hs hmaps).contDiffOn
  have hdg : HasFDerivAt g (mfderiv I (𝓡∂ 3) f x) (c x) := by
    have h := (hf.mdifferentiableAt (by simp) (x := x)).hasMFDerivAt
    have hw : HasFDerivWithinAt g (mfderiv I (𝓡∂ 3) f x) (range I) (c x) := h.2
    exact hw.hasFDerivAt (by rw [I.range_eq_univ]; exact Filter.univ_mem)
  -- Boundary-valued maps have zero normal coordinate in every chart they enter.
  have hnormal : ∀ w ∈ U, (P (g w)).1 = 0 := by
    intro w hw
    have hwchart : f (c.symm w) ∈ (chartAt (EuclideanHalfSpace 3) (f x)).source := by
      simpa only [d, extChartAt_source, mem_preimage, Function.comp_apply] using hw.2
    have hb := ((𝓡∂ 3).isBoundaryPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 3) (f x)) hwchart).mp (hboundary (c.symm w))
    have hzero : g w 0 = 0 := by
      by_contra hn
      have hnonneg : 0 ≤ g w 0 :=
        ((chartAt (EuclideanHalfSpace 3) (f x)) (f (c.symm w))).property
      have hpos : 0 < g w 0 := lt_of_le_of_ne hnonneg (Ne.symm hn)
      have hi : (𝓡∂ 3) ((chartAt (EuclideanHalfSpace 3) (f x)) (f (c.symm w))) ∈
          interior (range (𝓡∂ 3)) := by
        rw [interior_range_modelWithCornersEuclideanHalfSpace]
        exact hpos
      have hi' := (chartAt (EuclideanHalfSpace 3) (f x)).mem_interior_extend_target
        ((chartAt (EuclideanHalfSpace 3) (f x)).map_source hwchart) hi
      exact hb.2 hi'
    ext i
    fin_cases i
    exact hzero
  let N : Euc 3 →L[ℝ] Euc 1 :=
    (ContinuousLinearMap.fst ℝ (Euc 1) (Euc 2)).comp P.toContinuousLinearMap
  let Q : Euc 3 →L[ℝ] Euc 2 :=
    (ContinuousLinearMap.snd ℝ (Euc 1) (Euc 2)).comp P.toContinuousLinearMap
  have hN : N.comp (mfderiv I (𝓡∂ 3) f x) = 0 := by
    have heq : (fun w => (0 : Euc 1)) =ᶠ[𝓝 (c x)] N ∘ g := by
      filter_upwards [hU.mem_nhds hxU] with w hw
      exact (hnormal w hw).symm
    exact (N.hasFDerivAt.comp (c x) hdg).unique
      ((hasFDerivAt_const (0 : Euc 1) (c x)).congr_of_eventuallyEq heq.symm)
  let B : V →L[ℝ] V := L.symm.toContinuousLinearMap.comp
    (Q.comp (mfderiv I (𝓡∂ 3) f x))
  have hB : Function.Injective B := by
    intro a b hab
    apply hinj x
    apply P.injective
    apply Prod.ext
    · have h := congrArg (fun C : V →L[ℝ] Euc 1 => C a) hN
      have h' := congrArg (fun C : V →L[ℝ] Euc 1 => C b) hN
      exact h.trans h'.symm
    · exact L.symm.injective hab
  let B' : V ≃L[ℝ] V := (LinearEquiv.ofBijective B.toLinearMap
    ⟨hB, LinearMap.injective_iff_surjective.mp hB⟩).toContinuousLinearEquiv
  let q : V → V := L.symm ∘ Q ∘ g
  have hq : ContDiffOn ℝ ∞ q U := L.symm.contDiff.comp_contDiffOn
    (Q.contDiff.comp_contDiffOn hg)
  have hdq : HasFDerivAt q (B' : V →L[ℝ] V) (c x) :=
    L.symm.hasFDerivAt.comp (c x) (Q.hasFDerivAt.comp (c x) hdg)
  obtain ⟨e, hxe, heU, he, heinv, heq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv hq hU hxU hdq
  let ep : PartialDiffeomorph 𝓘(ℝ, V) 𝓘(ℝ, V) V V ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := he.contMDiffOn
      contMDiffOn_invFun := heinv.contMDiffOn }
  let mi : PartialDiffeomorph 𝓘(ℝ, V) I V H ∞ :=
    { toPartialEquiv := I.toHomeomorph.symm.toPartialEquiv
      open_source := isOpen_univ
      open_target := isOpen_univ
      contMDiffOn_toFun := by
        change ContMDiffOn 𝓘(ℝ, V) I ∞ I.symm univ
        simpa only [I.range_eq_univ] using I.contMDiffOn_symm (n := ∞)
      contMDiffOn_invFun := I.contMDiff.contMDiffOn }
  let α := (c.trans ep).trans mi
  apply IsImmersionAtOfComplement.mk_of_continuousAt hf.continuous.continuousAt A
    α.toOpenPartialHomeomorph (chartAt (EuclideanHalfSpace 3) (f x))
  · exact ⟨⟨hxc, hxe⟩, mem_univ _⟩
  · exact mem_chart_source (EuclideanHalfSpace 3) (f x)
  · exact α.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      α.contMDiffOn_toFun α.contMDiffOn_invFun
  · exact chart_mem_maximalAtlas (f x)
  · intro z hz
    have hIz : I (I.symm z) = z := I.toHomeomorph.apply_symm_apply z
    have hzα : I.symm z ∈ α.target := hz.2
    have hzt : z ∈ e.target := by
      have hmem := hzα.2.1
      change I (I.symm z) ∈ e.target at hmem
      rwa [hIz] at hmem
    have hwe : e.symm z ∈ e.source := e.map_target hzt
    have hwU : e.symm z ∈ U := heU hwe
    change g (e.symm (I (I.symm z))) = A (z, 0)
    rw [hIz]
    apply P.injective
    have hQ : Q (g (e.symm z)) = L z := by
      have hqz : q (e.symm z) = z := by rw [← heq, e.right_inv hzt]
      simpa only [q, Function.comp_apply, L.apply_symm_apply] using congrArg L hqz
    have hAz : P (A (z, 0)) = (0, L z) := by simp [A]
    rw [hAz]
    exact Prod.ext (hnormal _ hwU) hQ

theorem rawShellTorus_smoothEmbedding :
    Manifold.IsSmoothEmbedding TorusModel (𝓡∂ 3) ∞ (rawShellTorus E) := by
  refine ⟨boundary_plane_immersion TorusModel (by simp)
    (rawShellTorus E) (rawShellTorus_smooth E) ?_
    (rawShellTorus_differential_injective E), ?_⟩
  · intro p
    exact rawShellTorus_range E ▸ Set.mem_range_self p
  · apply IsClosedEmbedding.isEmbedding
    apply (rawShellTorus_continuous E).isClosedEmbedding
    intro p q h
    exact rawShellSphere_injective (congrArg E.toSphere h)

def graphRotationMap (v : Circle → Circle) (p : Circle × Circle) : Circle × Circle :=
  (p.1 * v p.2, p.2)
def graphRotationInverse (v : Circle → Circle) (p : Circle × Circle) : Circle × Circle :=
  (p.1 * (v p.2)⁻¹, p.2)

theorem graphRotation_diffeomorph_exists (v : Circle → Circle)
    (hv : ContMDiff (𝓡 1) (𝓡 1) ∞ v) :
    ∃ R : Diffeomorph TorusModel TorusModel (Circle × Circle) (Circle × Circle) ∞,
      (R : Circle × Circle → Circle × Circle) = graphRotationMap v ∧
      (R.symm : Circle × Circle → Circle × Circle) = graphRotationInverse v := by
  let R : Diffeomorph TorusModel TorusModel (Circle × Circle) (Circle × Circle) ∞ :=
    { toEquiv :=
        { toFun := graphRotationMap v
          invFun := graphRotationInverse v
          left_inv := by intro p; simp [graphRotationMap, graphRotationInverse, mul_assoc]
          right_inv := by intro p; simp [graphRotationMap, graphRotationInverse, mul_assoc] }
      contMDiff_toFun := by
        exact (contMDiff_fst.mul (hv.comp contMDiff_snd)).prodMk contMDiff_snd
      contMDiff_invFun := by
        exact (contMDiff_fst.mul ((hv.comp contMDiff_snd).inv)).prodMk contMDiff_snd }
  exact ⟨R, rfl, rfl⟩

def graphTorus (v : Circle → Circle) : Circle × Circle → E.Carrier :=
  rawShellTorus E ∘ graphRotationMap v

theorem graphTorus_smoothEmbedding (v : Circle → Circle)
    (hv : ContMDiff (𝓡 1) (𝓡 1) ∞ v) :
    Manifold.IsSmoothEmbedding TorusModel (𝓡∂ 3) ∞ (graphTorus E v) := by
  rcases graphRotation_diffeomorph_exists v hv with ⟨R, hR, _⟩
  rw [graphTorus, ← hR]
  exact Transport.smoothEmbedding_diffeomorph_precomp TorusModel (𝓡∂ 3)
    (rawShellTorus E) (rawShellTorus_smoothEmbedding E) R
theorem graphTorus_range (v : Circle → Circle) :
    Set.range (graphTorus E v) = (𝓡∂ 3).boundary E.Carrier := by
  rw [graphTorus, Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ,
    rawShellTorus_range]
  intro p
  refine ⟨graphRotationInverse v p, ?_⟩
  simp [graphRotationInverse, graphRotationMap, mul_assoc]
theorem graphTorus_witness_label (v : Circle → Circle) (z : Circle) :
    E.toSphere (graphTorus E v (1, z)) = T.tube 0 (z, unitDisk (v z)) := by
  simp [SmoothExterior.toSphere, graphTorus, rawShellTorus,
    rawShellSphere, graphRotationMap]

theorem graphTorus_leaf_homotopy (v : Circle → Circle)
    (hv : ContMDiff (𝓡 1) (𝓡 1) ∞ v) (a b : Circle) :
    ∃ fa fb : C(Circle, E.Carrier),
      (fa : Circle → E.Carrier) = (fun z => graphTorus E v (a, z)) ∧
      (fb : Circle → E.Carrier) = (fun z => graphTorus E v (b, z)) ∧
      ∃ H : ContinuousMap.Homotopy fa fb,
        ∀ t z, H (t, z) ∈ (𝓡∂ 3).boundary E.Carrier := by
  rcases graphRotation_diffeomorph_exists v hv with ⟨R, hR, _⟩
  have hc : Continuous (graphTorus E v) := by
    rw [graphTorus, ← hR]
    exact (rawShellTorus_continuous E).comp R.contMDiff.continuous
  let fa : C(Circle, E.Carrier) :=
    ⟨fun z => graphTorus E v (a, z), hc.comp (continuous_const.prodMk continuous_id)⟩
  let fb : C(Circle, E.Carrier) :=
    ⟨fun z => graphTorus E v (b, z), hc.comp (continuous_const.prodMk continuous_id)⟩
  let γ : Path a b := PathConnectedSpace.somePath a b
  let H : ContinuousMap.Homotopy fa fb :=
    { toFun := fun p => graphTorus E v (γ p.1, p.2)
      continuous_toFun := hc.comp ((γ.continuous.comp continuous_fst).prodMk continuous_snd)
      map_zero_left := by intro z; simp [fa]
      map_one_left := by intro z; simp [fb] }
  refine ⟨fa, fb, rfl, rfl, H, ?_⟩
  intro t z
  exact graphTorus_range E v ▸ Set.mem_range_self (γ t, z)

/-- T0 also produces the knot-case topological boundary torus obligation. -/
theorem actual_boundary_torus_homeomorph :
    Nonempty ((E.boundaryTorus 0) ≃ₜ (Circle × Circle)) := by
  let f : Circle × Circle → E.boundaryTorus 0 := fun p =>
    ⟨rawShellTorus E p, by
      change rawShellSphere p ∈ T.shell 0
      exact rawShellSphere_range ▸ Set.mem_range_self p⟩
  have hc : Continuous f := (rawShellTorus_continuous E).subtype_mk _
  have hinj : Function.Injective f := by
    intro p q hpq
    exact rawShellSphere_injective (congrArg (fun x : E.boundaryTorus 0 => E.toSphere x.1) hpq)
  have hsurj : Function.Surjective f := by
    intro x
    have hx : E.toSphere x.1 ∈ Set.range (@rawShellSphere K T) :=
      rawShellSphere_range ▸ x.2
    rcases hx with ⟨p, hp⟩
    exact ⟨p, Subtype.ext (Subtype.ext hp)⟩
  exact ⟨((hc.isClosedEmbedding hinj).isEmbedding.toHomeomorphOfSurjective hsurj).symm⟩

end
end SeifertSurfaces.LongitudeProducers
