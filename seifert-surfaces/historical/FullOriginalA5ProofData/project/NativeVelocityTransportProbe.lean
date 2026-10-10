import NativeConormalSectionProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

theorem native_transport_tangent_eq_of_cast
    (x y : ThreeSphere) (h : x = y) (v : TangentSpace (𝓡 3) x) (w : TangentSpace (𝓡 3) y)
    (hvw : v = tangentSpaceCast (𝓡 3) y x w) : h ▸ v = w := by
  subst y
  exact hvw

/-- The actual transported closed-side differential applied to the exact
coordinate lift velocity equals the actual native ambient seam velocity. -/
theorem native_actual_curve_velocity
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (U : Set ℝ) (hU : IsOpen U) (q : ℝ → Euc 2) (γ : ℝ → ThreeSphere)
    (hqc : ContDiffOn ℝ 1 q U)
    (hqm : MapsTo q U ((F.domain i).chart j).map.target)
    (heq : ∀ t ∈ U, pieceSphereCoordinate E F i j (q t) = γ t)
    (t : ℝ) (ht : t ∈ U) :
    actualPieceConormal E F i j (q t) (deriv q t) (γ t) (heq t ht) =
      mfderiv 𝓘(ℝ) (𝓡 3) γ t 1 := by
  let P := pieceSphereCoordinate E F i j
  let A := ((F.domain i).chart j).map.target
  have hP := ((native_piece_sphere_C1_rank E F i j).1 (q t) (hqm ht)).mdifferentiableWithinAt (by norm_num)
  have hd := mfderivWithin_comp (I := 𝓘(ℝ)) (I' := 𝓘(ℝ,Euc 2)) (I'' := 𝓡 3)
    t hP ((hqc t ht).differentiableWithinAt (by norm_num)).mdifferentiableWithinAt
      hqm (hU.uniqueMDiffOn t ht)
  have he := mfderivWithin_congr_of_mem (I := 𝓘(ℝ)) (I' := 𝓡 3) heq ht
  change mfderivWithin 𝓘(ℝ) (𝓡 3) (P ∘ q) U t = _ at he
  change mfderivWithin 𝓘(ℝ) (𝓡 3) (P ∘ q) U t = _ at hd
  rw [hd, mfderivWithin_of_mem_nhds (hU.mem_nhds ht),
    mfderivWithin_of_mem_nhds (hU.mem_nhds ht), mfderiv_eq_fderiv] at he
  have h1 := congrArg (fun L => L (1 : TangentSpace 𝓘(ℝ) t)) he
  have hder : fderiv ℝ q t (1 : ℝ) = deriv q t := by
    rw [fderiv_eq_smul_deriv]
    change (1 : ℝ) • deriv q t = deriv q t
    exact one_smul ℝ _
  change mfderivWithin 𝓘(ℝ,Euc 2) (𝓡 3) P A (q t)
    ((NormedSpace.fromTangentSpace (q t)).symm (fderiv ℝ q t 1)) =
      tangentSpaceCast (𝓡 3) (γ t) (P (q t)) (mfderiv 𝓘(ℝ) (𝓡 3) γ t 1) at h1
  rw [hder] at h1
  exact native_transport_tangent_eq_of_cast _ _ (heq t ht) _ _ h1

theorem native_straight_clock_velocity
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (q : ℝ → Euc 2) (γ : ℝ → ThreeSphere) (origin e : Euc 2) (clock : ℝ → ℝ)
    (hclock : ContDiffOn ℝ 1 clock (Ioo (-1 : ℝ) 1))
    (hline : ∀ t ∈ Ioo (-1 : ℝ) 1, q t = origin + clock t • e)
    (hqm : MapsTo q (Ioo (-1 : ℝ) 1) ((F.domain i).chart j).map.target)
    (heq : ∀ t ∈ Ioo (-1 : ℝ) 1, pieceSphereCoordinate E F i j (q t) = γ t)
    (t : SeamLocalTime) :
    mfderiv 𝓘(ℝ) (𝓡 3) γ (t : ℝ) 1 =
      deriv clock t • actualPieceConormal E F i j (q t) e (γ t) (heq t t.property) := by
  have hca := (hclock t t.property).contDiffAt (isOpen_Ioo.mem_nhds t.property)
  have hqevent : q =ᶠ[𝓝 (t : ℝ)] (fun t => origin + clock t • e) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds t.property) hline
  have hqc : ContDiffOn ℝ 1 q (Ioo (-1 : ℝ) 1) :=
    (contDiffOn_const.add (hclock.smul contDiffOn_const)).congr hline
  have hdq : deriv q t = deriv clock t • e := hqevent.deriv_eq.trans
    (((hca.differentiableAt (by norm_num)).hasDerivAt.smul_const e).const_add origin).deriv
  have hvel := native_actual_curve_velocity E F i j (Ioo (-1 : ℝ) 1) isOpen_Ioo q γ hqc hqm heq t t.property
  rw [hdq] at hvel
  rw [← hvel]
  simpa only [actualPieceDifferential_apply] using
    (actualPieceDifferential E F i j (q t) (γ t) (heq t t.property)).map_smul (deriv clock t) e

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
