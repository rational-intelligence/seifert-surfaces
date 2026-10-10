import ChartHelpers
import RadialCutProducer

set_option maxSynthPendingDepth 3
open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers.CollarCutHelpers
open Foundations MetricFoundations
noncomputable section

abbrev CollarModel := (𝓡 1).prod (𝓡∂ 1)
abbrev TubeModel := (𝓡 1).prod 𝓘(ℝ, Euc 2)


structure TubeCoordinates {K : OrientedKnot} (T : TubularNeighborhood K) where
  map : Diffeomorph TubeModel (𝓡 3) TubeDomain (tubeImageOpen T) ∞
  equation : ∀ p, (map p : ThreeSphere) = T.tube 0 p

theorem half_time_mem : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by
  norm_num
def halfTime : Time := ⟨1 / 2, half_time_mem⟩
theorem scale_time_mem (a : ℝ) (ha : 0 ≤ a) (h1 : a ≤ 1) (t : Time) :
    a * (t : ℝ) ∈ Icc (0 : ℝ) 1 := by
  exact ⟨mul_nonneg ha t.property.1,
    (mul_le_mul_of_nonneg_left t.property.2 ha).trans (by simpa using h1)⟩
def scaleTime (a : ℝ) (ha : 0 ≤ a) (h1 : a ≤ 1) (t : Time) : Time :=
  ⟨a * (t : ℝ), scale_time_mem a ha h1 t⟩
def timeUnit : TangentSpace (𝓡∂ 1) (0 : Time) :=
  (tangentSpaceCastModel (𝓡∂ 1) (0 : Time)).symm (EuclideanSpace.single 0 1)


structure SourceCollar {K : OrientedKnot} (F : SphereSpanningSurface.{0} K) where
  toFun : Circle × Time → F.surface
  embedding : Manifold.IsSmoothEmbedding CollarModel (𝓡∂ 2) ∞ toFun
  boundary : ∀ z, toFun (z, 0) = F.boundary.toFun z
  neighborhood : IsOpen (toFun '' {p : Circle × Time | (p.2 : ℝ) < 1})
  inward : ∀ z, ∃ w : TangentSpace (𝓡∂ 1) (0 : Time),
    0 < inwardCoordinate (F.boundary.toFun z)
      (mfderiv (𝓡∂ 1) (𝓡∂ 2) (fun t => toFun (z, t)) 0 w)
  interior : ∀ z (t : Time), 0 < (t : ℝ) → toFun (z, t) ∉ F.surface.boundary


structure UpperExtendedCollar {K : OrientedKnot} {F : SphereSpanningSurface.{0} K}
    (c : SourceCollar F) where
  width : ℝ
  width_gt_one : 1 < width
  map : Circle × ℝ → F.surface
  agrees : ∀ p : Circle × Time, map (p.1, (p.2 : ℝ)) = c.toFun p
  smooth : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ map
    {p | 0 ≤ p.2 ∧ p.2 < width}
  upper_immersion : ∀ z, Manifold.IsImmersionAt ((𝓡 1).prod 𝓘(ℝ, ℝ))
    (𝓡∂ 2) ∞ map (z, 1)

theorem time_strip_open (a : ℝ) : IsOpen {p : Circle × Time | (p.2 : ℝ) < a} := by
  exact isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
def openTimeStrip (a : ℝ) : TopologicalSpace.Opens (Circle × Time) :=
  ⟨{p | (p.2 : ℝ) < a}, time_strip_open a⟩

structure CollarSubstrip {K : OrientedKnot} {F : SphereSpanningSurface.{0} K}
    (c : SourceCollar F) (a b : ℝ) where
  image : TopologicalSpace.Opens F.surface
  image_eq : (image : Set F.surface) = c.toFun '' {p | (p.2 : ℝ) < a}
  coordinates : Diffeomorph CollarModel (𝓡∂ 2) (openTimeStrip a) image ∞
  equation : ∀ p, (coordinates p : F.surface) = c.toFun p.val
  inverse_eq : ∀ p : openTimeStrip a,
    coordinates.symm (coordinates p) = p
  closed_strip_compact : IsCompact (c.toFun '' {p : Circle × Time | (p.2 : ℝ) ≤ b})
  remainder_compact : IsCompact ((image : Set F.surface)ᶜ)
  remainder_disjoint : Disjoint ((image : Set F.surface)ᶜ) (Set.range F.boundary.toFun)

theorem source_collar_substrip_coordinates {K : OrientedKnot}
    {F : SphereSpanningSurface.{0} K} (c : SourceCollar F)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Nonempty (CollarSubstrip c a b) := by
  let f1 : openTimeStrip 1 → F.surface := fun p => c.toFun p.val
  have he1 : IsEmbedding f1 := c.embedding.isEmbedding.comp IsEmbedding.subtypeVal
  have hr1 : Set.range f1 = c.toFun '' {p : Circle × Time | (p.2 : ℝ) < 1} := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  have hopen1 : IsOpenEmbedding f1 := ⟨he1, by rw [hr1]; exact c.neighborhood⟩
  have ha1 : a < 1 := hab.trans hb
  have hopen : IsOpen (c.toFun '' {p : Circle × Time | (p.2 : ℝ) < a}) := by
    have ho := hopen1.isOpenMap {p : openTimeStrip 1 | (p.val.2 : ℝ) < a}
      (isOpen_lt ((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val)
        continuous_const)
    have hh : f1 '' {p : openTimeStrip 1 | (p.val.2 : ℝ) < a} =
        c.toFun '' {p : Circle × Time | (p.2 : ℝ) < a} := by
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.val, hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨p, hp.trans ha1⟩, hp, rfl⟩
    rwa [hh] at ho
  let image : TopologicalSpace.Opens F.surface :=
    ⟨c.toFun '' {p : Circle × Time | (p.2 : ℝ) < a}, hopen⟩
  let f : openTimeStrip a → F.surface := fun p => c.toFun p.val
  have he : IsEmbedding f := c.embedding.isEmbedding.comp IsEmbedding.subtypeVal
  have hr : Set.range f = (image : Set F.surface) := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  let e : openTimeStrip a ≃ₜ image := he.toHomeomorph.trans (Homeomorph.setCongr hr)
  have heq (p : openTimeStrip a) : (e p : F.surface) = c.toFun p.val := rfl
  have hinveq : c.toFun ∘ (Subtype.val ∘ e.symm) = (Subtype.val : image → F.surface) := by
    funext p
    rw [Function.comp_apply, Function.comp_apply, ← heq, e.apply_symm_apply]
  have hforward : ContMDiff CollarModel (𝓡∂ 2) ∞ e := by
    apply (ContMDiff.subtypeVal_comp_iff image e).mp
    exact c.embedding.contMDiff.comp contMDiff_subtype_val
  have hinverse : ContMDiff (𝓡∂ 2) CollarModel ∞ e.symm := by
    apply (ContMDiff.subtypeVal_comp_iff (openTimeStrip a) e.symm).mp
    apply (ContMDiff.iff_comp_isImmersion c.embedding.isImmersion).mpr
    refine ⟨continuous_subtype_val.comp e.symm.continuous, ?_⟩
    rw [hinveq]
    exact contMDiff_subtype_val
  let d : Diffeomorph CollarModel (𝓡∂ 2) (openTimeStrip a) image ∞ :=
    ⟨e.toEquiv, hforward, hinverse⟩
  refine ⟨{ image := image
            image_eq := rfl
            coordinates := d
            equation := heq
            inverse_eq := d.symm_apply_apply
            closed_strip_compact := ?_
            remainder_compact := ?_
            remainder_disjoint := ?_ }⟩
  · apply (IsClosed.isCompact ?_).image c.embedding.isEmbedding.continuous
    exact isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const
  · exact image.isOpen.isClosed_compl.isCompact
  · apply Set.disjoint_left.mpr
    intro x hx hboundary
    rcases hboundary with ⟨z, rfl⟩
    apply hx
    exact ⟨(z, 0), by simpa using ha, c.boundary z⟩


theorem ribbon_collar_interior {K : OrientedKnot} {T : TubularNeighborhood K}
    {F : SphereSpanningSurface.{0} K} (R : FramedRibbon T F) :
    ∀ z (t : Time), 0 < (t : ℝ) → R.collar (z, t) ∉ F.surface.boundary := by
  intro z t ht hb
  rw [← F.boundary_covers] at hb
  obtain ⟨z', hz'⟩ := hb
  have heq := R.collar_embedding.isEmbedding.injective
    ((R.collar_boundary z').trans hz')
  have htime := congrArg (fun p : Circle × Time => (p.2 : ℝ)) heq
  change 0 = (t : ℝ) at htime
  linarith

def ribbonSourceCollar {K : OrientedKnot} {T : TubularNeighborhood K}
    {F : SphereSpanningSurface.{0} K} (R : FramedRibbon T F) : SourceCollar F where
  toFun := R.collar
  embedding := R.collar_embedding
  boundary := R.collar_boundary
  neighborhood := R.collar_neighborhood
  inward := R.collar_inward
  interior := ribbon_collar_interior R


end
end SeifertSurfaces.LongitudeProducers.CollarCutHelpers
