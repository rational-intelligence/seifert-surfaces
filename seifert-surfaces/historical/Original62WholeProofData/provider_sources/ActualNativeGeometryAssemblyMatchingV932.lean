import NativeGeometryReplayV752

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped Manifold ContDiff
open Set Topology TopologicalSpace Manifold
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualNativeGeometryAssemblyMatchingV932

/-- Native geometry fields assemble into the approved literal realization
record on the same annulus quotient, with no component or endpoint conclusion. -/
theorem actual_compression_realization_with_matching_product
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A : CompressionAnnulus D)
    [ChartedSpace (EuclideanHalfSpace 2) A.SurgerySpace]
    [IsManifold (𝓡∂ 2) ∞ A.SurgerySpace]
    (Ω : SmoothVolumeOrientation (𝓡∂ 2) A.SurgerySpace)
    (Rs : A.SurgerySpace → E.Carrier)
    (hRs : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ Rs)
    (hQbd : (𝓡∂ 2).boundary A.SurgerySpace =
      A.remainderInclusion '' {x : A.Remainder | x.val ∈ F.surface.boundary})
    (hQpre : Rs ⁻¹' ((𝓡∂ 3).boundary E.Carrier) = (𝓡∂ 2).boundary A.SurgerySpace)
    (hQtrans : ∀ y ∈ (𝓡∂ 2).boundary A.SurgerySpace,
      ∃ w : TangentSpace (𝓡∂ 2) y,
        inwardCoordinate (Rs y) (mfderiv (𝓡∂ 2) (𝓡∂ 3) Rs y w) ≠ 0)
    (Pdisk : ClosedDisk ≃ₜ D.disk)
    (hPdisk : ∀ z,Pdisk (CompressionAnnulus.capEdge z) = D.boundaryCircle.toFun z)
    (J : C(ClosedDisk × Time,E.Carrier)) (hJ : IsEmbedding J)
    (hJcenter : ∀ x,J (x,middleTime) = D.toFun (Pdisk x))
    (hJlateral : ∀ z t,J (CompressionAnnulus.capEdge z,t) = F.embedding.toFun (A.band (z,t)))
    (hJint : range J ⊆ (𝓡∂ 3).interior E.Carrier)
    (hJF : range J ∩ F.image = range (fun p : Circle × Time => F.embedding.toFun (A.band p)))
    (hJcaps : Disjoint (range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime 0)))
      (range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime 1))))
    (hJavoid : ∀ k : Fin 2,Disjoint
      (range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime k))) (range D.toFun))
    (hJattach : ∀ k : Fin 2,
      range (fun x : ClosedDisk => J (x,CompressionAnnulus.sideTime k)) ∩
        (F.embedding.toFun '' A.removedᶜ) =
      range (fun z : Circle => F.embedding.toFun (A.band (z,CompressionAnnulus.sideTime k))))
    (R : C(A.SurgerySpace,E.Carrier)) (hR : IsEmbedding R)
    (hRrem : ∀ x : A.Remainder,R (A.remainderInclusion x) = F.embedding.toFun x)
    (hRcap : ∀ k x,R (A.capInclusion k x) = J (x,CompressionAnnulus.sideTime k))
    (I : TopologicalAmbientIsotopy E.Carrier) (Wr : Set E.Carrier)
    (hWr : IsOpen Wr)
    (hWredges : ∀ k z,F.embedding.toFun (A.band (z,CompressionAnnulus.sideTime k)) ∈ Wr)
    (hWrbd : Disjoint (closure Wr) ((𝓡∂ 3).boundary E.Carrier))
    (hWrD : Disjoint (closure Wr) (range D.toFun))
    (hIoff : ∀ t x,x ∉ Wr → I.stage t x = x)
    (hIB : ∀ t x,x ∈ (𝓡∂ 3).boundary E.Carrier → I.stage t x = x)
    (hRsI : ∀ x,Rs x = I.stage 1 (R x))
    (N : Set F.surface) (hN : IsOpen N)
    (hNedge : ∀ k z,A.band (z,CompressionAnnulus.sideTime k) ∈ N)
    (hNbd : Disjoint (closure N) F.surface.boundary)
    (hRsunchanged : ∀ x : A.Remainder,(x : F.surface) ∉ N →
      Rs (A.remainderInclusion x) = F.embedding.toFun x)
    (hRsbd : ∀ x : A.Remainder,(x : F.surface) ∈ F.surface.boundary →
      Rs (A.remainderInclusion x) = F.embedding.toFun x)
    (m : F.surface → A.SurgerySpace)
    (hm : ∀ x : A.Remainder,m x = A.remainderInclusion x)
    (hms : ∀ x : F.surface,x ∉ N → x ∉ A.removed →
      ContMDiffAt (𝓡∂ 2) (𝓡∂ 2) ∞ m x)
    (hmo : ∀ x : F.surface,x ∉ N → x ∉ A.removed →
      ∀ v : Fin 2 → TangentSpace (𝓡∂ 2) x,0 < F.surface.orientation.form x v →
        0 < Ω.form (m x) (fun i => mfderiv (𝓡∂ 2) (𝓡∂ 2) m x (v i))) :
    ∃ P : SmoothCompressionSurface A,
      ∃ C : SeifertSurfaces.OriginalEndpoints.ActualCompressionRealization E F A P,
        C.diskParam = Pdisk ∧ C.thickening = J := by
  let _ := CompressionHausdorffSupport.surgery_hausdorff A
  let _ := CompressionCountableSupport.surgery_secondCountable A
  let _ := CompressionExactQuotientSupport.compact_surgery A
  have hboundary (x : A.Remainder) :
      A.remainderInclusion x ∈ (𝓡∂ 2).boundary A.SurgerySpace ↔ x.val ∈ F.surface.boundary := by
    rw [hQbd]
    constructor
    · rintro ⟨y,hy,he⟩
      exact CompressionQuotientSupport.remainderInclusion_injective A he ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  have hcaps := CompressionActualNativeCapBoundaryExclusion.actual_native_all_caps_away_boundary A hQbd
  let S : CompactOrientedSurface.{0} := {
    carrier := A.SurgerySpace
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    hausdorff := inferInstance
    secondCountable := inferInstance
    compact := inferInstance
    orientation := Ω }
  let P : SmoothCompressionSurface A := {
    surface := S
    realization := Homeomorph.refl _
    boundary_matches := hboundary
    caps_interior := hcaps }
  let f : NeatEmbedding P.surface E.Carrier := {
    toFun := Rs
    smoothEmbedding := hRs
    boundary_preimage := hQpre
    boundary_transverse := hQtrans }
  refine ⟨P,{
    embedding := f
    seamNeighborhood := N
    seam_open := hN
    seam_contains := hNedge
    unchanged := hRsunchanged
    boundary_fixed := hRsbd
    seam_away_boundary := disjoint_left.mpr (fun x hx hb => disjoint_left.mp hNbd (subset_closure hx) hb)
    diskParam := Pdisk
    diskParam_boundary := hPdisk
    thickening := J
    thickening_embedded := hJ
    thickening_center := hJcenter
    thickening_lateral := hJlateral
    thickening_interior := hJint
    thickening_surface_intersection := hJF
    caps_disjoint := hJcaps
    caps_avoid_suppliedDisk := hJavoid
    caps_meet_remainder_only_at_attachment := hJattach
    unrounded := R
    unrounded_embedded := hR
    unrounded_remainder := hRrem
    unrounded_caps := hRcap
    rounding := I
    roundingSupport := Wr
    roundingSupport_open := hWr
    roundingSupport_contains_seams := hWredges
    roundingSupport_away_boundary := hWrbd
    roundingSupport_away_centralDisk := hWrD
    rounding_fixed_outside := hIoff
    rounding_boundary_fixed := hIB
    rounded_identification := hRsI
    seam_closure_away_boundary := hNbd
    remainderMarking := m
    remainderMarking_eq := hm
    remainderMarking_smooth := hms
    remainder_orientation := hmo },rfl,rfl⟩

#print axioms actual_compression_realization_with_matching_product
end CompressionActualNativeGeometryAssemblyMatchingV932
