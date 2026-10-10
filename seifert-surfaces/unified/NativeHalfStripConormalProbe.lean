import NativeVelocityTransportProbe
import NativeHalfStripRelativeWindowProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped Manifold ContDiff Bundle
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

structure NativeBoundaryConormalData (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (q : SeamLocalTime → Euc 2) (γ : ℝ → ThreeSphere)
    (heq : ∀ t : SeamLocalTime, pieceSphereCoordinate E F i j (q t) = γ t) where
  vector : SeamLocalTime → Euc 2
  continuous : Continuous vector
  outward : ∀ t : SeamLocalTime, ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Ioo (0 : ℝ) ε,
    q t - b • vector t ∈ interior ((F.domain i).chart j).map.target ∧
    q t + b • vector t ∉ ((F.domain i).chart j).map.target
  unit : ∀ t : SeamLocalTime, G.extension.inner (γ t)
    (actualPieceConormal E F i j (q t) (vector t) (γ t) (heq t))
    (actualPieceConormal E F i j (q t) (vector t) (γ t) (heq t)) = 1
  orthogonal : ∀ t : SeamLocalTime, G.extension.inner (γ t)
    (actualPieceConormal E F i j (q t) (vector t) (γ t) (heq t))
    (mfderiv 𝓘(ℝ) (𝓡 3) γ (t : ℝ) 1) = 0
  section_continuous : Continuous (fun t : SeamLocalTime =>
    Bundle.TotalSpace.mk' (Euc 3) (γ t)
      (actualPieceConormal E F i j (q t) (vector t) (γ t) (heq t)))

theorem native_halfstrip_full_conormal
    (G : A7.SourceGeometry E)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (q : SeamLocalTime → Euc 2) (γ : ℝ → ThreeSphere)
    (H : NativeSeamHalfStrip E F i j q)
    (hqb : ∀ t, q t ∈ ((F.domain i).chart j).map.target ∩ frontier ((F.domain i).chart j).map.target)
    (heq : ∀ t : SeamLocalTime, pieceSphereCoordinate E F i j (q t) = γ t) :
    Nonempty (NativeBoundaryConormalData E G F i j q γ heq) := by
  let q0 : ℝ → Euc 2 := fun t => H.origin + H.clock t • H.tangent
  have hline (t : SeamLocalTime) : q t = q0 t := by
    simpa only [nativeHalfStripCoordinates, zero_smul, add_zero] using H.exact_boundary_lift t
  have hq0c : ContDiffOn ℝ 1 q0 (Ioo (-1 : ℝ) 1) :=
    contDiffOn_const.add (H.clock_c1.smul contDiffOn_const)
  have hqc : Continuous q := hq0c.continuousOn.domRestrict.congr (fun t => (hline t).symm)
  obtain ⟨v, hvc, hvneg, hvunit, hvortho, hvsection⟩ := native_metric_unit_outward_section E G F i j
    q (fun t => γ t) hqc (fun t => (hqb t).1) heq H.tangent H.inward
      H.tangent_unit H.inward_unit H.frame_orthogonal
  refine ⟨⟨v, hvc, ?_, hvunit, ?_, hvsection⟩⟩
  · intro t
    apply local_halfplane_outward_direction _ _ H.inward _ _ (hvneg t)
    have hmap : MapsTo (fun z : ℝ × ℝ => H.origin + H.clock z.1 • H.tangent + z.2 • H.inward)
        (Ioo (-1 : ℝ) 1 ×ˢ Ico 0 H.height) ((F.domain i).chart j).model.domain := by
      have hmp := H.maps_to_sector
      change MapsTo (fun z : ℝ × ℝ => H.origin + H.clock z.1 • H.tangent + z.2 • H.inward)
        (Ioo (-1 : ℝ) 1 ×ˢ Ico 0 H.height) ((F.domain i).chart j).map.target at hmp
      rwa [((F.domain i).chart j).target_eq] at hmp
    have hbd : ∀ u ∈ Ioo (-1 : ℝ) 1,
        H.origin + H.clock u • H.tangent ∈ ((F.domain i).chart j).model.domain ∩
          frontier ((F.domain i).chart j).model.domain := by
      intro u hu
      have huq := hqb ⟨u, hu⟩
      rw [hline, ((F.domain i).chart j).target_eq] at huq
      exact huq
    have hs := native_halfstrip_boundary_halfplane ((F.domain i).chart j).model H.origin
      H.tangent H.inward H.clock H.height H.height_pos H.tangent_unit H.inward_unit
        H.frame_orthogonal H.clock_c1 (fun u hu => H.clock_regular ⟨u, hu⟩) hmap hbd t t.property
    rw [← ((F.domain i).chart j).target_eq] at hs
    simpa only [hline t] using hs
  · intro t
    have hqm : MapsTo q0 (Ioo (-1 : ℝ) 1) ((F.domain i).chart j).map.target := by
      intro u hu
      rw [← hline ⟨u, hu⟩]
      exact (hqb ⟨u, hu⟩).1
    have hpeq : ∀ u ∈ Ioo (-1 : ℝ) 1, pieceSphereCoordinate E F i j (q0 u) = γ u := by
      intro u hu
      rw [← hline ⟨u, hu⟩]
      exact heq ⟨u, hu⟩
    have hvel := native_straight_clock_velocity E F i j q0 γ H.origin H.tangent H.clock H.clock_c1
      (fun _ _ => rfl) hqm hpeq t
    have hvel' : mfderiv 𝓘(ℝ) (𝓡 3) γ (t : ℝ) 1 = deriv H.clock t •
        actualPieceConormal E F i j (q t) H.tangent (γ t) (heq t) := by
      simpa only [← hline t] using hvel
    rw [hvel']
    change (G.extension.inner (γ t)
      (actualPieceConormal E F i j (q t) (v t) (γ t) (heq t)))
        (deriv H.clock t • actualPieceConormal E F i j (q t) H.tangent (γ t) (heq t)) = 0
    rw [map_smul, hvortho, smul_zero]

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
