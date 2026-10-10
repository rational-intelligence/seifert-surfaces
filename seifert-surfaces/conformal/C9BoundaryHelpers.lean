import OriginalC9

noncomputable section
open Bundle
open scoped Manifold ContDiff Topology

namespace SeifertSurfaces.AppendixC.Original

universe u v
variable (S : Type u) [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]
  (D : Type v) [TopologicalSpace D] [ChartedSpace Plane D]
  [IsManifold (𝓡 2) ∞ D]

/-- The actual connected component and its closure occupy one specified
side of the GIVEN reflection disk. The side is chosen by the component,
not by a new parametrization or atlas. -/
structure ComponentHalfDiskSide
    (t : InteriorConformalField (𝓡∂ 2) S) (swap : D ≃ₜ D)
    (c : RawL2DoublePrime S D t swap) (p : S)
    (k : DiskReflectionChart D c.atlas c.involution (c.diffeomorph.homeomorph p : D))
    (upper : Bool) : Prop where
  component_side : c.component ∩ k.chart.source =
    {q ∈ k.chart.source | 0 < (if upper then k.chart q else star (k.chart q)).im}
  closure_side : closure c.component ∩ k.chart.source =
    {q ∈ k.chart.source | 0 ≤ (if upper then k.chart q else star (k.chart q)).im}

/-- One actual half-space chart pulled back through the SAME given
diffeomorphism, tied to the GIVEN reflection disk and its selected side.
This is construction output, never an assumption on the original endpoint. -/
structure HalfDiskPullbackAt
    (t : InteriorConformalField (𝓡∂ 2) S) (swap : D ≃ₜ D)
    (c : RawL2DoublePrime S D t swap) (p : S)
    (k : DiskReflectionChart D c.atlas c.involution (c.diffeomorph.homeomorph p : D))
    (upper : Bool) where
  chart : OpenPartialHomeomorph S (EuclideanHalfSpace 2)
  source_eq : chart.source =
    (fun q => (c.diffeomorph.homeomorph q : D)) ⁻¹' k.chart.source
  mem_source : p ∈ chart.source
  half_disk_target : chart.target =
    {x : EuclideanHalfSpace 2 | ‖halfSpaceComplex x‖ < k.radius}
  smooth : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ chart chart.source
  smooth_inverse : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ chart.symm chart.target
  coordinate_identity : ∀ q ∈ chart.source,
    halfSpaceComplex (chart q) =
      if upper then k.chart (c.diffeomorph.homeomorph q : D)
      else star (k.chart (c.diffeomorph.homeomorph q : D))
  inverse_identity : ∀ x ∈ chart.target,
    (c.diffeomorph.homeomorph (chart.symm x) : D) =
      k.chart.symm (if upper then halfSpaceComplex x else star (halfSpaceComplex x))
  boundary_axis : chart '' ((𝓡∂ 2).boundary S ∩ chart.source) =
    {x ∈ chart.target | x.1 0 = 0}

/-- Actual boundary preservation derived before any half-space target
chart is constructed. All ambient witnesses are exactly those of the
protected raw boundary interface. -/
theorem given_diffeomorphism_boundary_fixed
    [T2Space S] [SecondCountableTopology S] [CompactSpace S]
    [T2Space D] [SecondCountableTopology D] [CompactSpace D]
    (t : InteriorConformalField (𝓡∂ 2) S) (j : S → D)
    (d : SmoothDouble S D j)
    (c : RawL2DoublePrime S D t d.swap.toHomeomorph)
    (r : ∀ q : D, c.involution q = q →
      Nonempty (DiskReflectionChart D c.atlas c.involution q)) :
    ∀ p : S, (𝓡∂ 2).IsBoundaryPoint p ↔
      c.involution (c.diffeomorph.homeomorph p : D) =
        (c.diffeomorph.homeomorph p : D) := by
  classical
  let A : Set D := Set.range j
  let B : Set D := d.swap '' A
  let F : Set D := {q | d.swap q = q}
  have hA : IsClosed A := by
    simpa only [Set.image_univ] using
      (isCompact_univ.image d.inclusion.embedding.continuous).isClosed
  have hB : IsClosed B := d.swap.toHomeomorph.isClosedMap _ hA
  have hF : F = frontier A := d.fixed_boundary.trans d.inclusion.boundary_image
  have hcover : A ∪ B = Set.univ := d.cover
  have hoverlap : A ∩ B = F := d.overlap.trans d.fixed_boundary.symm
  have hswapF : d.swap '' F = F := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact congrArg d.swap hz
    · intro hq
      exact ⟨q, hq, hq⟩
  have hfrontierB : frontier B = F := by
    change frontier (d.swap.toHomeomorph '' A) = F
    rw [← d.swap.toHomeomorph.image_frontier A, ← hF]
    exact hswapF
  have hAi : interior A = Bᶜ := by
    rw [← closure_sdiff_frontier, hA.closure_eq, ← hF, ← hoverlap]
    ext q
    change (q ∈ A ∧ ¬(q ∈ A ∧ q ∈ B)) ↔ q ∉ B
    have hq : q ∈ A ∨ q ∈ B := by
      change q ∈ A ∪ B
      rw [hcover]
      trivial
    tauto
  have hBi : interior B = Aᶜ := by
    rw [← closure_sdiff_frontier, hB.closure_eq, hfrontierB, ← hoverlap]
    ext q
    change (q ∈ B ∧ ¬(q ∈ A ∧ q ∈ B)) ↔ q ∉ A
    have hq : q ∈ A ∨ q ∈ B := by
      change q ∈ A ∪ B
      rw [hcover]
      trivial
    tauto
  have hclosureAi : closure (interior A) = A := by
    rw [hAi, closure_compl, hBi, compl_compl]
  have hclosureBi : closure (interior B) = B := by
    rw [hBi, closure_compl, hAi, compl_compl]
  have hAinterior : j '' (𝓡∂ 2).interior S = interior A := by
    rw [← closure_sdiff_frontier, hA.closure_eq, ← d.inclusion.boundary_image]
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, rfl⟩, ?_⟩
      rintro ⟨w, hw, heq⟩
      have hwz : w = z := d.inclusion.embedding.injective heq
      exact (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint z).mp hz (hwz ▸ hw)
    · rintro ⟨⟨z, rfl⟩, hz⟩
      refine ⟨z, (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint z).mpr ?_, rfl⟩
      intro hzb
      exact hz ⟨z, hzb, rfl⟩
  have hconnectedAi : IsConnected (interior A) := hAinterior ▸ d.interior_connected
  have hconnectedBi : IsConnected (interior B) := by
    change IsConnected (interior (d.swap.toHomeomorph '' A))
    rw [← d.swap.toHomeomorph.image_interior A]
    exact hconnectedAi.image d.swap d.swap.toHomeomorph.continuous.continuousOn
  have hopenAi : IsOpen (interior A) := isOpen_interior
  have hopenBi : IsOpen (interior B) := isOpen_interior
  have hdisjoint : Disjoint (interior A) (interior B) := by
    rw [hAi, hBi]
    exact Set.disjoint_left.mpr fun q hqB hqA => by
      have hq : q ∈ A ∪ B := by rw [hcover]; trivial
      exact hq.elim hqA hqB
  have hnotfixed : {q : D | d.swap q ≠ q} = interior A ∪ interior B := by
    rw [hAi, hBi, ← Set.compl_inter, Set.inter_comm B A, hoverlap]
    rfl
  have hconjugate : c.conjugacy '' {q : D | d.swap q ≠ q} =
      {q : D | c.involution q ≠ q} := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      change c.involution (c.conjugacy z) ≠ c.conjugacy z
      rw [c.conjugate_swap]
      exact fun heq => hz (c.conjugacy.injective heq)
    · intro hq
      refine ⟨c.conjugacy.symm q, ?_, c.conjugacy.apply_symm_apply q⟩
      intro hz
      apply hq
      have heq := c.conjugate_swap (c.conjugacy.symm q)
      change d.swap.toHomeomorph (c.conjugacy.symm q) = c.conjugacy.symm q at hz
      simpa only [c.conjugacy.apply_symm_apply, hz] using heq
  let Ai : Set D := c.conjugacy '' interior A
  let Bi : Set D := c.conjugacy '' interior B
  have hnotfixedc : {q : D | c.involution q ≠ q} = Ai ∪ Bi := by
    rw [← hconjugate, hnotfixed, Set.image_union]
  have hopenAic : IsOpen Ai := c.conjugacy.isOpenMap _ hopenAi
  have hopenBic : IsOpen Bi := c.conjugacy.isOpenMap _ hopenBi
  have hdisjointc : Disjoint Ai Bi := Set.disjoint_image_of_injective c.conjugacy.injective hdisjoint
  have hcomponent_connected : IsConnected c.component := by
    rw [c.component_eq]
    exact isConnected_connectedComponentIn_iff.mpr c.point_not_fixed
  have hcomponent_sub : c.component ⊆ {q | c.involution q ≠ q} := by
    rw [c.component_eq]
    exact connectedComponentIn_subset _ _
  have hcomponent_choice : c.component = Ai ∨ c.component = Bi := by
    have hsub : c.component ⊆ Ai ∪ Bi := hnotfixedc ▸ hcomponent_sub
    rcases IsPreconnected.subset_or_subset hopenAic hopenBic hdisjointc hsub
      hcomponent_connected.isPreconnected with h | h
    · left
      refine Set.Subset.antisymm h ?_
      have hpt : c.component_point ∈ c.component := by
        rw [c.component_eq]
        exact mem_connectedComponentIn c.point_not_fixed
      rw [c.component_eq]
      exact (hconnectedAi.image _ c.conjugacy.continuous.continuousOn).isPreconnected.subset_connectedComponentIn
        (h hpt) (by intro q hq; rw [hnotfixedc]; exact Or.inl hq)
    · right
      refine Set.Subset.antisymm h ?_
      have hpt : c.component_point ∈ c.component := by
        rw [c.component_eq]
        exact mem_connectedComponentIn c.point_not_fixed
      rw [c.component_eq]
      exact (hconnectedBi.image _ c.conjugacy.continuous.continuousOn).isPreconnected.subset_connectedComponentIn
        (h hpt) (by intro q hq; rw [hnotfixedc]; exact Or.inr hq)
  have hcomponent_open : IsOpen c.component :=
    hcomponent_choice.elim (fun h => h ▸ hopenAic) (fun h => h ▸ hopenBic)
  have hcomponent_regular : interior (closure c.component) = c.component := by
    rcases hcomponent_choice with h | h
    · rw [h]
      change interior (closure (c.conjugacy '' interior A)) = c.conjugacy '' interior A
      rw [← c.conjugacy.image_closure, hclosureAi, ← c.conjugacy.image_interior]
    · rw [h]
      change interior (closure (c.conjugacy '' interior B)) = c.conjugacy '' interior B
      rw [← c.conjugacy.image_closure, hclosureBi, ← c.conjugacy.image_interior]
  have hconjugatefixed : c.conjugacy '' F = {q : D | c.involution q = q} := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      change c.involution (c.conjugacy z) = c.conjugacy z
      rw [c.conjugate_swap]
      exact congrArg c.conjugacy hz
    · intro hq
      refine ⟨c.conjugacy.symm q, ?_, c.conjugacy.apply_symm_apply q⟩
      apply c.conjugacy.injective
      change c.conjugacy (d.swap.toHomeomorph (c.conjugacy.symm q)) = c.conjugacy (c.conjugacy.symm q)
      rw [← c.conjugate_swap, c.conjugacy.apply_symm_apply]
      exact hq
  have hcomponent_frontier : frontier c.component = {q : D | c.involution q = q} := by
    rcases hcomponent_choice with h | h
    · rw [h]
      change frontier (c.conjugacy '' interior A) = _
      rw [← c.conjugacy.image_frontier]
      have hfa : frontier (interior A) = frontier A := by
        rw [frontier, hclosureAi, isOpen_interior.interior_eq]
        rw [frontier, hA.closure_eq]
      rw [hfa, ← hF, hconjugatefixed]
    · rw [h]
      change frontier (c.conjugacy '' interior B) = _
      rw [← c.conjugacy.image_frontier]
      have hfb : frontier (interior B) = frontier B := by
        rw [frontier, hclosureBi, isOpen_interior.interior_eq]
        rw [frontier, hB.closure_eq]
      rw [hfb, hfrontierB, hconjugatefixed]
  let f : S → D := fun q => (c.diffeomorph.homeomorph q : D)
  have hf : ContMDiff (𝓡∂ 2) (𝓡 2) ∞ f := c.diffeomorph.smooth
  have hfi : ∀ p, Function.Injective (mfderiv (𝓡∂ 2) (𝓡 2) f p) :=
    c.diffeomorph.immersion
  have hinterior_forward : ∀ p : S, (𝓡∂ 2).IsInteriorPoint p → f p ∈ c.component := by
    intro p hp
    let e := extChartAt (𝓡∂ 2) p
    let e' := extChartAt (𝓡 2) (f p)
    let g : Plane → Plane := e' ∘ f ∘ e.symm
    let a : Plane := e p
    have hra : Set.range (𝓡∂ 2) ∈ 𝓝 a := range_mem_nhds_isInteriorPoint hp
    have hga : g a = e' (f p) := by
      dsimp only [g, a, Function.comp_apply, e]
      rw [extChartAt_to_inv]
    have hgd : ContDiffAt ℝ ∞ g a :=
      ((contMDiffAt_iff.mp (hf p)).2).contDiffAt hra
    have hfd : MDifferentiableAt (𝓡∂ 2) (𝓡 2) f p := (hf p).mdifferentiableAt (by simp)
    have hginj : Function.Injective (fderivWithin ℝ g (Set.range (𝓡∂ 2)) a) := by
      have hi := hfi p
      simp only [mfderiv, hfd, ↓reduceIte] at hi
      change Function.Injective (fderivWithin ℝ g (Set.range (𝓡∂ 2)) a) at hi
      exact hi
    have hginj' : Function.Injective (fderiv ℝ g a) := by
      rw [← fderivWithin_eq_fderiv (by
        exact (𝓡∂ 2).uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range p (mem_extChartAt_target p))) (hgd.differentiableAt (by simp))] 
      exact hginj
    have hgsurj : Function.Surjective (fderiv ℝ g a) :=
      LinearMap.surjective_of_injective hginj'
    have hmap : Filter.map g (𝓝 a) = 𝓝 (g a) :=
      (hgd.hasStrictFDerivAt (by simp)).map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hgsurj)
    let T : Set Plane := e.target ∩ (f ∘ e.symm) ⁻¹' e'.source
    have ht : T ∈ 𝓝 a := by
      refine Filter.inter_mem ?_ ?_
      · have he : e.target ∈ 𝓝[Set.range (𝓡∂ 2)] a := extChartAt_target_mem_nhdsWithin p
        rwa [nhdsWithin_eq_nhds.mpr hra] at he
      · have hec : ContinuousAt (f ∘ e.symm) a :=
          (hf.continuous.continuousAt.comp (continuousAt_extChartAt_symm p))
        have : f (e.symm a) = f p := by dsimp only [e, a]; rw [extChartAt_to_inv]
        exact hec.preimage_mem_nhds (by
          change e'.source ∈ 𝓝 (f (e.symm a))
          rw [this]
          exact extChartAt_source_mem_nhds (f p))
    have himage : g '' T ∈ 𝓝 (e' (f p)) := by
      rw [← hga, ← hmap]
      exact Filter.image_mem_map ht
    have hpre : e' ⁻¹' (g '' T) ∩ e'.source ∈ 𝓝 (f p) :=
      Filter.inter_mem ((continuousAt_extChartAt (f p)).preimage_mem_nhds himage)
        (extChartAt_source_mem_nhds (f p))
    have hcnhds : closure c.component ∈ 𝓝 (f p) := by
      refine Filter.mem_of_superset hpre ?_
      rintro y ⟨⟨x, hx, hxy⟩, hy⟩
      have hxy' : e' (f (e.symm x)) = e' y := hxy
      have hyeq : f (e.symm x) = y := e'.injOn hx.2 hy hxy'
      exact hyeq ▸ (c.diffeomorph.homeomorph (e.symm x)).property
    rw [← hcomponent_regular]
    exact mem_interior_iff_mem_nhds.mpr hcnhds
  have hinterior_inverse : ∀ p : S, f p ∈ c.component → (𝓡∂ 2).IsInteriorPoint p := by
    intro p hp
    obtain ⟨U, g, hU, hpU, hg, hgeq⟩ := c.diffeomorph.smooth_inverse (c.diffeomorph.homeomorph p)
    have hq : c.diffeomorph.homeomorph.symm (c.diffeomorph.homeomorph p) = p :=
      c.diffeomorph.homeomorph.symm_apply_apply p
    have hgp : g (f p) = extChartAt (𝓡∂ 2) p p := by
      simpa only [hq] using (hgeq (c.diffeomorph.homeomorph p) hpU).2
    have hcomp : (g ∘ f) =ᶠ[𝓝 p] extChartAt (𝓡∂ 2) p := by
      filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hpU)] with z hz
      simpa only [Function.comp_apply, c.diffeomorph.homeomorph.symm_apply_apply, hq] using
        (hgeq (c.diffeomorph.homeomorph z) hz).2
    have hgd : MDifferentiableAt (𝓡 2) (𝓡 2) g (f p) :=
      (hg.contMDiffAt (hU.mem_nhds hpU)).mdifferentiableAt (by simp)
    have hfd : MDifferentiableAt (𝓡∂ 2) (𝓡 2) f p := (hf p).mdifferentiableAt (by simp)
    have hcompderiv : (mfderiv (𝓡 2) (𝓡 2) g (f p)).comp
        (mfderiv (𝓡∂ 2) (𝓡 2) f p) = ContinuousLinearMap.id ℝ Plane := by
      rw [← mfderiv_comp p hgd hfd]
      have heq := hcomp.mfderiv_eq (I := 𝓡∂ 2) (I' := 𝓡 2)
      rw [mfderiv_extChartAt_self] at heq
      change mfderiv (𝓡∂ 2) (𝓡 2) (g ∘ f) p = ContinuousLinearMap.id ℝ Plane at heq
      exact heq
    have hgsurj : Function.Surjective (mfderiv (𝓡 2) (𝓡 2) g (f p)) := by
      intro v
      exact ⟨mfderiv (𝓡∂ 2) (𝓡 2) f p v, DFunLike.congr_fun hcompderiv v⟩
    let e := extChartAt (𝓡 2) (f p)
    let a : Plane := e (f p)
    let g' : Plane → Plane := g ∘ e.symm
    have hg'a : g' a = g (f p) := by
      dsimp only [g', a, e, Function.comp_apply]
      rw [extChartAt_to_inv]
    have hgc : ContDiffAt ℝ ∞ g' a := by
      have h := (contMDiffAt_iff.mp (hg.contMDiffAt (hU.mem_nhds hpU))).2
      have h' : ContDiffWithinAt ℝ ∞ g' Set.univ a := by
        simpa only [g', a, e, f, mfld_simps] using h
      exact contDiffWithinAt_univ.mp h'
    have hgf : Function.Surjective (fderiv ℝ g' a) := by
      have h := hgsurj
      simp only [mfderiv, hgd, ↓reduceIte] at h
      change Function.Surjective (fderivWithin ℝ g' (Set.range (𝓡 2)) a) at h
      simpa only [Set.range_id, modelWithCornersSelf_coe, fderivWithin_univ] using h
    let V : Set Plane := e.target ∩ e.symm ⁻¹' (U ∩ c.component)
    have hV : V ∈ 𝓝 a := by
      refine Filter.inter_mem (extChartAt_target_mem_nhds (f p)) ?_
      have hnhds : U ∩ c.component ∈ 𝓝 ((extChartAt (𝓡 2) (f p)).symm
          (extChartAt (𝓡 2) (f p) (f p))) := by
        rw [extChartAt_to_inv]
        exact Filter.inter_mem (hU.mem_nhds hpU) (hcomponent_open.mem_nhds hp)
      exact (continuousAt_extChartAt_symm (f p)).preimage_mem_nhds hnhds
    have hmaps : Set.MapsTo g' V (Set.range (𝓡∂ 2)) := by
      intro y hy
      let q' : closure c.component := ⟨e.symm y, subset_closure hy.2.2⟩
      change g (e.symm y) ∈ Set.range (𝓡∂ 2)
      have hq' := hgeq q' hy.2.1
      rw [hq'.2]
      exact extChartAt_target_subset_range _ ((extChartAt (𝓡∂ 2)
        (c.diffeomorph.homeomorph.symm (c.diffeomorph.homeomorph p))).map_source hq'.1)
    have hmem : g' a ∈ interior (Set.range (𝓡∂ 2)) :=
      (hgc.differentiableAt (by simp)).mem_interior_convex_of_surjective_fderiv hV
        (𝓡∂ 2).convex_range (𝓡∂ 2).isClosed_range (𝓡∂ 2).nonempty_interior hmaps hgf
    rw [hg'a, hgp] at hmem
    exact hmem
  intro p
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint]
  have hpi : (𝓡∂ 2).IsInteriorPoint p ↔ f p ∈ c.component :=
    ⟨hinterior_forward p, hinterior_inverse p⟩
  rw [hpi]
  have hcl : f p ∈ closure c.component := (c.diffeomorph.homeomorph p).property
  have hfr : frontier c.component = closure c.component \ c.component := by
    rw [frontier, hcomponent_open.interior_eq]
  have hm : f p ∈ frontier c.component ↔ f p ∉ c.component := by
    rw [hfr]
    exact and_iff_right hcl
  exact hm.symm.trans (by rw [hcomponent_frontier]; rfl)


/-- The selected component chooses exactly one half of any supplied
reflection disk at an image boundary point. Boundary preservation is an
earlier explicit helper obligation, not a new original C.9 premise. -/
theorem reflection_component_half_disk_side
    [T2Space S] [SecondCountableTopology S] [CompactSpace S]
    [T2Space D] [SecondCountableTopology D] [CompactSpace D]
    (t : InteriorConformalField (𝓡∂ 2) S) (j : S → D)
    (d : SmoothDouble S D j)
    (c : RawL2DoublePrime S D t d.swap.toHomeomorph)
    (r : ∀ q : D, c.involution q = q →
      Nonempty (DiskReflectionChart D c.atlas c.involution q))
    (hboundary : ∀ p : S, (𝓡∂ 2).IsBoundaryPoint p ↔
      c.involution (c.diffeomorph.homeomorph p : D) = (c.diffeomorph.homeomorph p : D))
    (p : S) (hp : (𝓡∂ 2).IsBoundaryPoint p)
    (k : DiskReflectionChart D c.atlas c.involution (c.diffeomorph.homeomorph p : D)) :
    ∃ upper : Bool, ComponentHalfDiskSide S D t d.swap.toHomeomorph c p k upper := by
  classical
  let A : Set D := Set.range j
  let B : Set D := d.swap '' A
  let F : Set D := {q | d.swap q = q}
  have hA : IsClosed A := by
    simpa only [Set.image_univ] using
      (isCompact_univ.image d.inclusion.embedding.continuous).isClosed
  have hB : IsClosed B := d.swap.toHomeomorph.isClosedMap _ hA
  have hF : F = frontier A := d.fixed_boundary.trans d.inclusion.boundary_image
  have hcover : A ∪ B = Set.univ := d.cover
  have hoverlap : A ∩ B = F := d.overlap.trans d.fixed_boundary.symm
  have hswapF : d.swap '' F = F := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact congrArg d.swap hz
    · intro hq
      exact ⟨q, hq, hq⟩
  have hfrontierB : frontier B = F := by
    change frontier (d.swap.toHomeomorph '' A) = F
    rw [← d.swap.toHomeomorph.image_frontier A, ← hF]
    exact hswapF
  have hAi : interior A = Bᶜ := by
    rw [← closure_sdiff_frontier, hA.closure_eq, ← hF, ← hoverlap]
    ext q
    change (q ∈ A ∧ ¬(q ∈ A ∧ q ∈ B)) ↔ q ∉ B
    have hq : q ∈ A ∨ q ∈ B := by
      change q ∈ A ∪ B
      rw [hcover]
      trivial
    tauto
  have hBi : interior B = Aᶜ := by
    rw [← closure_sdiff_frontier, hB.closure_eq, hfrontierB, ← hoverlap]
    ext q
    change (q ∈ B ∧ ¬(q ∈ A ∧ q ∈ B)) ↔ q ∉ A
    have hq : q ∈ A ∨ q ∈ B := by
      change q ∈ A ∪ B
      rw [hcover]
      trivial
    tauto
  have hclosureAi : closure (interior A) = A := by
    rw [hAi, closure_compl, hBi, compl_compl]
  have hclosureBi : closure (interior B) = B := by
    rw [hBi, closure_compl, hAi, compl_compl]
  have hAinterior : j '' (𝓡∂ 2).interior S = interior A := by
    rw [← closure_sdiff_frontier, hA.closure_eq, ← d.inclusion.boundary_image]
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, rfl⟩, ?_⟩
      rintro ⟨w, hw, heq⟩
      have hwz : w = z := d.inclusion.embedding.injective heq
      exact (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint z).mp hz (hwz ▸ hw)
    · rintro ⟨⟨z, rfl⟩, hz⟩
      refine ⟨z, (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint z).mpr ?_, rfl⟩
      intro hzb
      exact hz ⟨z, hzb, rfl⟩
  have hconnectedAi : IsConnected (interior A) := hAinterior ▸ d.interior_connected
  have hconnectedBi : IsConnected (interior B) := by
    change IsConnected (interior (d.swap.toHomeomorph '' A))
    rw [← d.swap.toHomeomorph.image_interior A]
    exact hconnectedAi.image d.swap d.swap.toHomeomorph.continuous.continuousOn
  have hopenAi : IsOpen (interior A) := isOpen_interior
  have hopenBi : IsOpen (interior B) := isOpen_interior
  have hdisjoint : Disjoint (interior A) (interior B) := by
    rw [hAi, hBi]
    exact Set.disjoint_left.mpr fun q hqB hqA => by
      have hq : q ∈ A ∪ B := by rw [hcover]; trivial
      exact hq.elim hqA hqB
  have hnotfixed : {q : D | d.swap q ≠ q} = interior A ∪ interior B := by
    rw [hAi, hBi, ← Set.compl_inter, Set.inter_comm B A, hoverlap]
    rfl
  have hconjugate : c.conjugacy '' {q : D | d.swap q ≠ q} =
      {q : D | c.involution q ≠ q} := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      change c.involution (c.conjugacy z) ≠ c.conjugacy z
      rw [c.conjugate_swap]
      exact fun heq => hz (c.conjugacy.injective heq)
    · intro hq
      refine ⟨c.conjugacy.symm q, ?_, c.conjugacy.apply_symm_apply q⟩
      intro hz
      apply hq
      have heq := c.conjugate_swap (c.conjugacy.symm q)
      change d.swap.toHomeomorph (c.conjugacy.symm q) = c.conjugacy.symm q at hz
      simpa only [c.conjugacy.apply_symm_apply, hz] using heq
  let Ai : Set D := c.conjugacy '' interior A
  let Bi : Set D := c.conjugacy '' interior B
  have hnotfixedc : {q : D | c.involution q ≠ q} = Ai ∪ Bi := by
    rw [← hconjugate, hnotfixed, Set.image_union]
  have hopenAic : IsOpen Ai := c.conjugacy.isOpenMap _ hopenAi
  have hopenBic : IsOpen Bi := c.conjugacy.isOpenMap _ hopenBi
  have hdisjointc : Disjoint Ai Bi := Set.disjoint_image_of_injective c.conjugacy.injective hdisjoint
  have hcomponent_connected : IsConnected c.component := by
    rw [c.component_eq]
    exact isConnected_connectedComponentIn_iff.mpr c.point_not_fixed
  have hcomponent_sub : c.component ⊆ {q | c.involution q ≠ q} := by
    rw [c.component_eq]
    exact connectedComponentIn_subset _ _
  have hcomponent_choice : c.component = Ai ∨ c.component = Bi := by
    have hsub : c.component ⊆ Ai ∪ Bi := hnotfixedc ▸ hcomponent_sub
    rcases IsPreconnected.subset_or_subset hopenAic hopenBic hdisjointc hsub
      hcomponent_connected.isPreconnected with h | h
    · left
      refine Set.Subset.antisymm h ?_
      have hpt : c.component_point ∈ c.component := by
        rw [c.component_eq]
        exact mem_connectedComponentIn c.point_not_fixed
      rw [c.component_eq]
      exact (hconnectedAi.image _ c.conjugacy.continuous.continuousOn).isPreconnected.subset_connectedComponentIn
        (h hpt) (by intro q hq; rw [hnotfixedc]; exact Or.inl hq)
    · right
      refine Set.Subset.antisymm h ?_
      have hpt : c.component_point ∈ c.component := by
        rw [c.component_eq]
        exact mem_connectedComponentIn c.point_not_fixed
      rw [c.component_eq]
      exact (hconnectedBi.image _ c.conjugacy.continuous.continuousOn).isPreconnected.subset_connectedComponentIn
        (h hpt) (by intro q hq; rw [hnotfixedc]; exact Or.inr hq)
  have hcomponent_open : IsOpen c.component :=
    hcomponent_choice.elim (fun h => h ▸ hopenAic) (fun h => h ▸ hopenBic)
  have hcomponent_regular : interior (closure c.component) = c.component := by
    rcases hcomponent_choice with h | h
    · rw [h]
      change interior (closure (c.conjugacy '' interior A)) = c.conjugacy '' interior A
      rw [← c.conjugacy.image_closure, hclosureAi, ← c.conjugacy.image_interior]
    · rw [h]
      change interior (closure (c.conjugacy '' interior B)) = c.conjugacy '' interior B
      rw [← c.conjugacy.image_closure, hclosureBi, ← c.conjugacy.image_interior]
  have hconjugatefixed : c.conjugacy '' F = {q : D | c.involution q = q} := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      change c.involution (c.conjugacy z) = c.conjugacy z
      rw [c.conjugate_swap]
      exact congrArg c.conjugacy hz
    · intro hq
      refine ⟨c.conjugacy.symm q, ?_, c.conjugacy.apply_symm_apply q⟩
      apply c.conjugacy.injective
      change c.conjugacy (d.swap.toHomeomorph (c.conjugacy.symm q)) = c.conjugacy (c.conjugacy.symm q)
      rw [← c.conjugate_swap, c.conjugacy.apply_symm_apply]
      exact hq
  have hcomponent_frontier : frontier c.component = {q : D | c.involution q = q} := by
    rcases hcomponent_choice with h | h
    · rw [h]
      change frontier (c.conjugacy '' interior A) = _
      rw [← c.conjugacy.image_frontier]
      have hfa : frontier (interior A) = frontier A := by
        rw [frontier, hclosureAi, isOpen_interior.interior_eq]
        rw [frontier, hA.closure_eq]
      rw [hfa, ← hF, hconjugatefixed]
    · rw [h]
      change frontier (c.conjugacy '' interior B) = _
      rw [← c.conjugacy.image_frontier]
      have hfb : frontier (interior B) = frontier B := by
        rw [frontier, hclosureBi, isOpen_interior.interior_eq]
        rw [frontier, hB.closure_eq]
      rw [hfb, hfrontierB, hconjugatefixed]
  have hswapAi : c.involution '' Ai = Bi := by
    have heq : c.involution '' (c.conjugacy '' interior A) =
        c.conjugacy '' (d.swap.toHomeomorph '' interior A) := by
      rw [Set.image_image, Set.image_image]
      congr 1
      funext q
      exact c.conjugate_swap q
    change c.involution '' (c.conjugacy '' interior A) = c.conjugacy '' interior B
    rw [heq, d.swap.toHomeomorph.image_interior]
    rfl
  have hswapBi : c.involution '' Bi = Ai := by
    rw [← hswapAi, Set.image_image]
    have heq : c.involution ∘ c.involution = id := funext c.involutive
    change (c.involution ∘ c.involution) '' Ai = Ai
    rw [heq, Set.image_id]
  have hswap_disjoint : ∀ q ∈ c.component, c.involution q ∉ c.component := by
    intro q hq
    rcases hcomponent_choice with h | h
    · rw [h] at hq ⊢
      have hi : c.involution q ∈ Bi := by rw [← hswapAi]; exact Set.mem_image_of_mem _ hq
      exact fun hiA => Set.disjoint_left.mp hdisjointc hiA hi
    · rw [h] at hq ⊢
      have hi : c.involution q ∈ Ai := by rw [← hswapBi]; exact Set.mem_image_of_mem _ hq
      exact fun hiB => Set.disjoint_left.mp hdisjointc hi hiB
  let U : Set D := {q ∈ k.chart.source | 0 < (k.chart q).im}
  let L : Set D := {q ∈ k.chart.source | (k.chart q).im < 0}
  have hUsub : U ⊆ {q : D | c.involution q ≠ q} := by
    intro q hq heq
    have him := (k.fixed_iff q hq.1).mp heq
    exact (ne_of_gt hq.2) him
  have hLsub : L ⊆ {q : D | c.involution q ≠ q} := by
    intro q hq heq
    have him := (k.fixed_iff q hq.1).mp heq
    exact (ne_of_lt hq.2) him
  have hhalf : ∀ H : Set D, IsPreconnected H → H ⊆ {q : D | c.involution q ≠ q} →
      (H ∩ c.component).Nonempty → H ⊆ c.component := by
    intro H hH hHsub hmeet
    obtain ⟨q, hqH, hqC⟩ := hmeet
    have hqCC : q ∈ connectedComponentIn {q : D | c.involution q ≠ q} c.component_point :=
      c.component_eq ▸ hqC
    rw [c.component_eq, connectedComponentIn_eq hqCC]
    exact hH.subset_connectedComponentIn hqH hHsub
  have hmeet : (c.component ∩ k.chart.source).Nonempty :=
    (closure_inter_open_nonempty_iff k.chart.open_source).mp
      ⟨(c.diffeomorph.homeomorph p : D), (c.diffeomorph.homeomorph p).property, k.mem_source⟩
  have hcase : (U ∩ c.component).Nonempty ∨ (L ∩ c.component).Nonempty := by
    obtain ⟨q, hqC, hqS⟩ := hmeet
    have hnq := hcomponent_sub hqC
    have hq : q ∈ k.chart.source \ {q | c.involution q = q} := ⟨hqS, hnq⟩
    rw [k.complement] at hq
    exact hq.elim (fun h => Or.inl ⟨q, h, hqC⟩) (fun h => Or.inr ⟨q, h, hqC⟩)
  have hclosurecalc : ∀ (T : Set ℂ), k.chart.IsImage c.component T →
      closure c.component ∩ k.chart.source = {q ∈ k.chart.source | k.chart q ∈ closure T} := by
    intro T hT
    ext q
    constructor
    · rintro ⟨hqC, hqS⟩
      exact ⟨hqS, (hT.closure hqS).mpr hqC⟩
    · rintro ⟨hqS, hqT⟩
      exact ⟨(hT.closure hqS).mp hqT, hqS⟩
  rcases hcase with h | h
  · have hUC : U ⊆ c.component := hhalf U k.upper_connected.isPreconnected hUsub h
    have hLC : ∀ q ∈ L, q ∉ c.component := by
      intro q hq
      have hqu : c.involution q ∈ U := by
        change c.involution q ∈ {q ∈ k.chart.source | 0 < (k.chart q).im}
        rw [← k.exchange_lower]
        exact Set.mem_image_of_mem _ hq
      intro hqC
      exact hswap_disjoint q hqC (hUC hqu)
    have hside : c.component ∩ k.chart.source = U := by
      ext q
      constructor
      · rintro ⟨hqC, hqS⟩
        have hq : q ∈ k.chart.source \ {q | c.involution q = q} := ⟨hqS, hcomponent_sub hqC⟩
        rw [k.complement] at hq
        exact hq.elim id (fun hl => False.elim (hLC q hl hqC))
      · intro hq
        exact ⟨hUC hq, hq.1⟩
    refine ⟨true, ⟨?_, ?_⟩⟩
    · exact hside
    · have hi : k.chart.IsImage c.component {z : ℂ | 0 < z.im} := by
        intro q hqS
        have hmem := Set.ext_iff.mp hside q
        change (0 < (k.chart q).im) ↔ q ∈ c.component
        change (q ∈ c.component ∧ q ∈ k.chart.source) ↔
          (q ∈ k.chart.source ∧ 0 < (k.chart q).im) at hmem
        tauto
      have heq := hclosurecalc {z : ℂ | 0 < z.im} hi
      rw [Complex.closure_setOfPred_lt_im] at heq
      exact heq
  · have hLC : L ⊆ c.component := hhalf L k.lower_connected.isPreconnected hLsub h
    have hUC : ∀ q ∈ U, q ∉ c.component := by
      intro q hq
      have hql : c.involution q ∈ L := by
        change c.involution q ∈ {q ∈ k.chart.source | (k.chart q).im < 0}
        rw [← k.exchange_upper]
        exact Set.mem_image_of_mem _ hq
      intro hqC
      exact hswap_disjoint q hqC (hLC hql)
    have hside : c.component ∩ k.chart.source = L := by
      ext q
      constructor
      · rintro ⟨hqC, hqS⟩
        have hq : q ∈ k.chart.source \ {q | c.involution q = q} := ⟨hqS, hcomponent_sub hqC⟩
        rw [k.complement] at hq
        exact hq.elim (fun hu => False.elim (hUC q hu hqC)) id
      · intro hq
        exact ⟨hLC hq, hq.1⟩
    refine ⟨false, ⟨?_, ?_⟩⟩
    · rw [hside]
      ext q
      change (q ∈ k.chart.source ∧ (k.chart q).im < 0) ↔
        (q ∈ k.chart.source ∧ 0 < (star (k.chart q)).im)
      rw [Complex.star_def, Complex.conj_im]
      exact and_congr_right fun _ => neg_pos.symm
    · have hi : k.chart.IsImage c.component {z : ℂ | z.im < 0} := by
        intro q hqS
        have hmem := Set.ext_iff.mp hside q
        change ((k.chart q).im < 0) ↔ q ∈ c.component
        change (q ∈ c.component ∧ q ∈ k.chart.source) ↔
          (q ∈ k.chart.source ∧ (k.chart q).im < 0) at hmem
        tauto
      have heq := hclosurecalc {z : ℂ | z.im < 0} hi
      rw [Complex.closure_setOfPred_im_lt] at heq
      rw [heq]
      ext q
      change (q ∈ k.chart.source ∧ (k.chart q).im ≤ 0) ↔
        (q ∈ k.chart.source ∧ 0 ≤ (star (k.chart q)).im)
      rw [Complex.star_def, Complex.conj_im]
      exact and_congr_right fun _ => neg_nonneg.symm



/-- Construct the genuine local partial homeomorphism and prove both
smooth directions using the GIVEN diffeomorphism and its existing inverse
extensions. Its coordinate and inverse formulas use the same disk/side.
The side equality is supplied by the preceding construction obligation. -/
theorem reflection_component_local_half_disk_pullback
    [T2Space S] [SecondCountableTopology S] [CompactSpace S]
    [T2Space D] [SecondCountableTopology D] [CompactSpace D]
    (t : InteriorConformalField (𝓡∂ 2) S) (j : S → D)
    (d : SmoothDouble S D j)
    (c : RawL2DoublePrime S D t d.swap.toHomeomorph)
    (r : ∀ q : D, c.involution q = q →
      Nonempty (DiskReflectionChart D c.atlas c.involution q))
    (hboundary : ∀ p : S, (𝓡∂ 2).IsBoundaryPoint p ↔
      c.involution (c.diffeomorph.homeomorph p : D) = (c.diffeomorph.homeomorph p : D))
    (p : S) (hp : (𝓡∂ 2).IsBoundaryPoint p)
    (k : DiskReflectionChart D c.atlas c.involution (c.diffeomorph.homeomorph p : D))
    (upper : Bool)
    (hside : ComponentHalfDiskSide S D t d.swap.toHomeomorph c p k upper) :
    Nonempty (HalfDiskPullbackAt S D t d.swap.toHomeomorph c p k upper) := by
  classical
  let f : S → D := fun q => (c.diffeomorph.homeomorph q : D)
  let J : ℂ →L[ℝ] ℂ := if upper then ContinuousLinearMap.id ℝ ℂ else Complex.conjCLE.toContinuousLinearMap
  have hJ : ∀ z : ℂ, J z = if upper then z else star z := by
    intro z
    cases upper <;> rfl
  have hJJ : ∀ z : ℂ, J (J z) = z := by
    intro z
    cases upper
    · exact star_star z
    · rfl
  have hJnorm : ∀ z : ℂ, ‖J z‖ = ‖z‖ := by
    intro z
    cases upper
    · exact Complex.norm_conj z
    · rfl
  let L : ℂ →L[ℝ] Plane :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.pi (fun i : Fin 2 => if i = 0 then Complex.imCLM else Complex.reCLM))
  have hL0 : ∀ z : ℂ, L z 0 = z.im := by intro z; rfl
  have hL1 : ∀ z : ℂ, L z 1 = z.re := by intro z; rfl
  let T : Set (EuclideanHalfSpace 2) := {x | ‖halfSpaceComplex x‖ < k.radius}
  let U : Set S := f ⁻¹' k.chart.source
  let F : S → EuclideanHalfSpace 2 := fun q => (𝓡∂ 2).symm (L (J (k.chart (f q))))
  have hside_closure : ∀ q ∈ k.chart.source,
      q ∈ closure c.component ↔ 0 ≤ (J (k.chart q)).im := by
    intro q hq
    have heq := Set.ext_iff.mp hside.closure_side q
    change (q ∈ closure c.component ∧ q ∈ k.chart.source) ↔
      (q ∈ k.chart.source ∧ 0 ≤ (if upper then k.chart q else star (k.chart q)).im) at heq
    rw [← hJ] at heq
    change (q ∈ closure c.component ∧ q ∈ k.chart.source) ↔
      (q ∈ k.chart.source ∧ 0 ≤ (J (k.chart q)).im) at heq
    tauto
  have hFcoords : ∀ q ∈ U, halfSpaceComplex (F q) = J (k.chart (f q)) := by
    intro q hq
    have hnonneg := (hside_closure (f q) hq).mp (c.diffeomorph.homeomorph q).property
    have hLnonneg : 0 ≤ L (J (k.chart (f q))) 0 := hnonneg
    dsimp only [F]
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hLnonneg]
    apply Complex.ext <;> rfl
  have hFmap : Set.MapsTo F U T := by
    intro q hq
    change ‖halfSpaceComplex (F q)‖ < k.radius
    rw [hFcoords q hq, hJnorm]
    have h := k.chart.map_source hq
    rw [k.disk_target, Metric.mem_ball, dist_zero_right] at h
    exact h
  let g : D → S := fun q => if hq : q ∈ closure c.component then
      c.diffeomorph.homeomorph.symm ⟨q, hq⟩ else p
  have hg_on : ∀ (q : closure c.component), g q = c.diffeomorph.homeomorph.symm q := by
    intro q
    change (if hq : (q : D) ∈ closure c.component then c.diffeomorph.homeomorph.symm ⟨q, hq⟩ else p) = _
    rw [dite_eq_left q.property]
  have hfg : ∀ q ∈ closure c.component, f (g q) = q := by
    intro q hq
    rw [hg_on ⟨q, hq⟩]
    exact congrArg Subtype.val (c.diffeomorph.homeomorph.apply_symm_apply ⟨q, hq⟩)
  have hgf : ∀ q : S, g (f q) = q := by
    intro q
    rw [hg_on (c.diffeomorph.homeomorph q)]
    exact c.diffeomorph.homeomorph.symm_apply_apply q
  let K : Plane →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1) + Complex.I • Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)
  have hK : ∀ x : Plane, K x = ⟨x 1, x 0⟩ := by
    intro x
    apply Complex.ext <;> simp [K]
  have hhalfcontinuous : Continuous halfSpaceComplex := by
    have heq : halfSpaceComplex = K ∘ (𝓡∂ 2) := by
      funext x
      exact (hK x.val).symm
    rw [heq]
    exact K.continuous.comp (𝓡∂ 2).continuous
  have hhalfsmooth : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ halfSpaceComplex := by
    have heq : halfSpaceComplex = K ∘ (𝓡∂ 2) := by
      funext x
      exact (hK x.val).symm
    rw [heq]
    exact K.contMDiff.comp (𝓡∂ 2).contMDiff
  let z : EuclideanHalfSpace 2 → ℂ := fun x => J (halfSpaceComplex x)
  have hzmap : Set.MapsTo z T k.chart.target := by
    intro x hx
    rw [k.disk_target, Metric.mem_ball, dist_zero_right]
    exact (hJnorm _).trans_lt hx
  have hqmap : Set.MapsTo (k.chart.symm ∘ z) T (closure c.component) := by
    intro x hx
    have hz := hzmap hx
    have hsrc := k.chart.map_target hz
    apply (hside_closure (k.chart.symm (z x)) hsrc).mpr
    rw [k.chart.right_inv hz]
    dsimp only [z]
    rw [hJJ]
    exact x.property
  let G : EuclideanHalfSpace 2 → S := g ∘ k.chart.symm ∘ z
  have hGmap : Set.MapsTo G T U := by
    intro x hx
    change f (g (k.chart.symm (z x))) ∈ k.chart.source
    rw [hfg (k.chart.symm (z x)) (hqmap hx)]
    exact k.chart.map_target (hzmap hx)
  have hGF : ∀ q ∈ U, G (F q) = q := by
    intro q hq
    have hzq : z (F q) = k.chart (f q) := by
      dsimp only [z]
      rw [hFcoords q hq, hJJ]
    dsimp only [G, Function.comp_apply]
    rw [hzq, k.chart.left_inv hq, hgf]
  have hFG : ∀ x ∈ T, F (G x) = x := by
    intro x hx
    apply EuclideanHalfSpace.ext
    apply PiLp.ext
    intro i
    have hcoords := hFcoords (G x) (hGmap hx)
    have hcomp : halfSpaceComplex (F (G x)) = halfSpaceComplex x := by
      rw [hcoords]
      dsimp only [G, Function.comp_apply]
      rw [hfg (k.chart.symm (z x)) (hqmap hx), k.chart.right_inv (hzmap hx)]
      exact hJJ _
    fin_cases i
    · exact congrArg Complex.im hcomp
    · exact congrArg Complex.re hcomp
  have hFcontinuous : ContinuousOn F U := by
    exact (𝓡∂ 2).continuous_symm.comp_continuousOn
      (L.continuous.comp_continuousOn (J.continuous.comp_continuousOn
        (k.chart.continuousOn.comp c.diffeomorph.smooth.continuous.continuousOn (by intro q hq; exact hq))))
  have hgcontinuous : ContinuousOn g (closure c.component) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : Set.domRestrict (closure c.component) g = c.diffeomorph.homeomorph.symm := funext hg_on
    rw [heq]
    exact c.diffeomorph.homeomorph.symm.continuous
  have hzcontinuous : Continuous z := J.continuous.comp hhalfcontinuous
  have hGcontinuous : ContinuousOn G T :=
    hgcontinuous.comp (k.chart.continuousOn_symm.comp hzcontinuous.continuousOn hzmap) hqmap
  let e : OpenPartialHomeomorph S (EuclideanHalfSpace 2) := {
    toFun := F
    invFun := G
    source := U
    target := T
    map_source' := hFmap
    map_target' := hGmap
    left_inv' := hGF
    right_inv' := hFG
    open_source := k.chart.open_source.preimage c.diffeomorph.smooth.continuous
    open_target := isOpen_lt hhalfcontinuous.norm continuous_const
    continuousOn_toFun := hFcontinuous
    continuousOn_invFun := hGcontinuous }
  have hesmooth : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ e e.source := by
    have hbase : ContMDiffOn (𝓡∂ 2) (𝓡 2) ∞ (L ∘ J ∘ k.chart ∘ f) U :=
      L.contMDiff.comp_contMDiffOn (J.contMDiff.comp_contMDiffOn
        (k.holomorphic_chart.smooth.comp c.diffeomorph.smooth.contMDiffOn (by intro q hq; exact hq)))
    have hmap : Set.MapsTo (L ∘ J ∘ k.chart ∘ f) U (Set.range (𝓡∂ 2)) := by
      intro q hq
      rw [range_modelWithCornersEuclideanHalfSpace]
      change 0 ≤ L (J (k.chart (f q))) 0
      exact (hside_closure (f q) hq).mp (c.diffeomorph.homeomorph q).property
    exact (𝓡∂ 2).contMDiffOn_symm.comp hbase hmap
  have heinverse : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ e.symm e.target := by
    have hzsmooth : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ z := J.contMDiff.comp hhalfsmooth
    have hqsmooth : ContMDiffOn (𝓡∂ 2) (𝓡 2) ∞ (k.chart.symm ∘ z) T :=
      k.holomorphic_chart.smooth_inverse.comp hzsmooth.contMDiffOn hzmap
    intro x hx
    let q' : closure c.component := ⟨k.chart.symm (z x), hqmap hx⟩
    let a : S := c.diffeomorph.homeomorph.symm q'
    have ha : G x = a := hg_on q'
    obtain ⟨V, H, hV, hqV, hH, hHeq⟩ := c.diffeomorph.smooth_inverse q'
    have hcomp : ContMDiffWithinAt (𝓡∂ 2) (𝓡 2) ∞ (H ∘ k.chart.symm ∘ z) T x :=
      (hH.contMDiffAt (hV.mem_nhds hqV)).comp_contMDiffWithinAt x (hqsmooth x hx)
    have hlocal : ∀ᶠ y in 𝓝[T] x, y ∈ T ∧ k.chart.symm (z y) ∈ V := by
      exact Filter.inter_mem self_mem_nhdsWithin
        ((hqsmooth.continuousOn x hx).preimage_mem_nhdsWithin (hV.mem_nhds hqV))
    have hcoord : (extChartAt (𝓡∂ 2) (G x) ∘ G) =ᶠ[𝓝[T] x]
        (H ∘ k.chart.symm ∘ z) := by
      filter_upwards [hlocal] with y hy
      let qy : closure c.component := ⟨k.chart.symm (z y), hqmap hy.1⟩
      have h := (hHeq qy hy.2).2
      rw [← hg_on qy] at h
      change H (k.chart.symm (z y)) = extChartAt (𝓡∂ 2) a (G y) at h
      rw [ha]
      exact h.symm
    have hcoordx : (extChartAt (𝓡∂ 2) (G x) ∘ G) x =
        (H ∘ k.chart.symm ∘ z) x := by
      have h := (hHeq q' hqV).2
      change H (k.chart.symm (z x)) = extChartAt (𝓡∂ 2) a a at h
      rw [Function.comp_apply, ha]
      exact h.symm
    apply contMDiffWithinAt_iff_target.mpr
    exact ⟨hGcontinuous x hx, hcomp.congr_of_eventuallyEq hcoord hcoordx⟩
  have heaxis : e '' ((𝓡∂ 2).boundary S ∩ e.source) = {x ∈ e.target | x.1 0 = 0} := by
    ext x
    constructor
    · rintro ⟨q, ⟨hqB, hqS⟩, rfl⟩
      refine ⟨hFmap hqS, ?_⟩
      have hfixed := (hboundary q).mp hqB
      have him := (k.fixed_iff (f q) hqS).mp hfixed
      have hcoord := congrArg Complex.im (hFcoords q hqS)
      have hjzero : (J (k.chart (f q))).im = 0 := by
        rw [hJ]
        cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, Complex.star_def, Complex.conj_im, him, neg_zero]
      change (F q).val 0 = 0
      exact hcoord.trans hjzero
    · rintro ⟨hxT, hx0⟩
      refine ⟨G x, ⟨?_, hGmap hxT⟩, hFG x hxT⟩
      apply (hboundary (G x)).mpr
      apply (k.fixed_iff (f (G x)) (hGmap hxT)).mpr
      have hcoords := hFcoords (G x) (hGmap hxT)
      rw [hFG x hxT] at hcoords
      have hzero : (J (k.chart (f (G x)))).im = 0 :=
        (congrArg Complex.im hcoords).symm.trans hx0
      rw [hJ] at hzero
      cases upper
      · change -(k.chart (f (G x))).im = 0 at hzero
        exact neg_eq_zero.mp hzero
      · exact hzero
  refine ⟨{
    chart := e
    source_eq := rfl
    mem_source := k.mem_source
    half_disk_target := rfl
    smooth := hesmooth
    smooth_inverse := heinverse
    coordinate_identity := ?_
    inverse_identity := ?_
    boundary_axis := heaxis }⟩
  · intro q hq
    exact (hFcoords q hq).trans (hJ _)
  · intro x hx
    change f (g (k.chart.symm (z x))) = _
    rw [hfg (k.chart.symm (z x)) (hqmap hx)]
    congr 1
    exact hJ _


/-- Assemble the actual boundary atlas from the constructed local charts.
This requested helper retains the protected endpoint's same t,j,d,c,r
and all original output fields; its sole additional input is the earlier
boundary-preservation obligation. -/
theorem reflection_component_half_disk_pullback
    [T2Space S] [SecondCountableTopology S] [CompactSpace S]
    [T2Space D] [SecondCountableTopology D] [CompactSpace D]
    (t : InteriorConformalField (𝓡∂ 2) S) (j : S → D)
    (d : SmoothDouble S D j)
    (c : RawL2DoublePrime S D t d.swap.toHomeomorph)
    (r : ∀ q : D, c.involution q = q →
      Nonempty (DiskReflectionChart D c.atlas c.involution q))
    (hboundary : ∀ p : S, (𝓡∂ 2).IsBoundaryPoint p ↔
      c.involution (c.diffeomorph.homeomorph p : D) = (c.diffeomorph.homeomorph p : D)) :
    Nonempty (AnalyticBoundaryPullback S D t d.swap.toHomeomorph c) := by
  classical
  let k : ∀ (p : S), (𝓡∂ 2).IsBoundaryPoint p →
      DiskReflectionChart D c.atlas c.involution (c.diffeomorph.homeomorph p : D) :=
    fun p hp => Classical.choice (r _ ((hboundary p).mp hp))
  have hside : ∀ (p : S) (hp : (𝓡∂ 2).IsBoundaryPoint p),
      ∃ upper : Bool, ComponentHalfDiskSide S D t d.swap.toHomeomorph c p (k p hp) upper :=
    fun p hp => reflection_component_half_disk_side S D t j d c r hboundary p hp (k p hp)
  let upper : ∀ (p : S), (𝓡∂ 2).IsBoundaryPoint p → Bool :=
    fun p hp => Classical.choose (hside p hp)
  let e : ∀ (p : S) (hp : (𝓡∂ 2).IsBoundaryPoint p),
      HalfDiskPullbackAt S D t d.swap.toHomeomorph c p (k p hp) (upper p hp) :=
    fun p hp => Classical.choice
      (reflection_component_local_half_disk_pullback S D t j d c r hboundary p hp
        (k p hp) (upper p hp) (Classical.choose_spec (hside p hp)))
  exact ⟨{
    boundary_fixed := hboundary
    charts := k
    subsurface_chart := fun p hp => (e p hp).chart
    upper_side := upper
    source_eq := fun p hp => (e p hp).source_eq
    mem_source := fun p hp => (e p hp).mem_source
    half_disk_target := fun p hp => (e p hp).half_disk_target
    smooth := fun p hp => (e p hp).smooth
    smooth_inverse := fun p hp => (e p hp).smooth_inverse
    coordinate_identity := fun p hp => (e p hp).coordinate_identity
    inverse_identity := fun p hp => (e p hp).inverse_identity
    boundary_axis := fun p hp => (e p hp).boundary_axis }⟩

end SeifertSurfaces.AppendixC.Original
