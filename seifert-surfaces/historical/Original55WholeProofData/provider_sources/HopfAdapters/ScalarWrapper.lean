import HopfAdapters.BoundaryDerivative
import EllipticPdes.Existence.StrongMaximum

noncomputable section
open Set Metric Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates.HopfAdapters

/-- Public Hopf with its sole boundary differentiability premise replaced by a within jet.
The operator is definitionally the public `nondivOp` convention. -/
theorem hopf_ball_within_derivative {d : ℕ} (hd : 0 < d)
    {y : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ)
    (hsymm : ∀ x ∈ ball y R, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ ball y R, ∀ ξ : Fin d → ℝ,
      θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ ball y R, ∀ i j, |a x i j| ≤ A)
    (hb : ∀ x ∈ ball y R, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ ball y R, 0 ≤ c x) (hcC : ∀ x ∈ ball y R, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u (ball y R))
    (huc : ContinuousOn u (closedBall y R))
    (hsub : ∀ x ∈ ball y R, nondivOp a b c u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : dist x₀ y = R)
    (hlt : ∀ x ∈ ball y R, u x < u x₀)
    (hcu : ∀ x ∈ ball y R, 0 ≤ c x * u x₀)
    (D : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hD : HasFDerivWithinAt u D (closedBall y R) x₀) :
    0 < D (x₀ - y) := by
  let v := affineOutsideExtension (closedBall y R) u x₀ D
  have hxK : x₀ ∈ closedBall y R := mem_closedBall.mpr hx₀.le
  have heq : EqOn v u (closedBall y R) := affine_extension_eqOn _ _ _ _
  have hv : ContDiffOn ℝ 2 v (ball y R) := by
    exact hu.congr (heq.mono ball_subset_closedBall)
  have hvc : ContinuousOn v (closedBall y R) :=
    affine_extension_continuousOn _ _ _ _ huc
  have hvD : HasFDerivAt v D x₀ := affine_extension_hasFDerivAt _ _ _ hxK _ hD
  have hoperator (x) (hx : x ∈ ball y R) :
      EllipticPdes.Classical.nondivOp a b c v x = nondivOp a b c u x := by
    change nondivOp a b c v x = nondivOp a b c u x
    exact affine_extension_nondivOp_eq a b c _ u x₀ D x
      (ball_subset_interior_closedBall hx)
  have hhopf := EllipticPdes.Classical.hopf_lemma_ball hd hR hθ hsymm hell ha hb hc0 hcC
    hv hvc (fun x hx => by rw [hoperator x hx]; exact hsub x hx) hx₀
    (fun x hx => by rw [heq (ball_subset_closedBall hx), heq hxK]; exact hlt x hx)
    (fun x hx => by rw [heq hxK]; exact hcu x hx) hvD.differentiableAt
  rwa [hvD.fderiv] at hhopf

theorem graph_height_boundary_derivative (V : Set E3) (hV : IsOpen V)
    (U : Set E2) (p normal : E3) (hp : p ∈ V) (L : E2 →L[ℝ] E3)
    (w : E2 → ℝ) (hw₀ : w 0 = 0)
    (hwflat : HasFDerivWithinAt w (0 : E2 →L[ℝ] ℝ) U 0)
    (r : E3 → ℝ) (hr : ContDiffOn ℝ ∞ r V)
    (c : E2) (R : ℝ) (hK : closedBall c R ⊆ U) :
    HasFDerivWithinAt (graphHeight r (graphMap p L normal w))
      ((fderiv ℝ r p).comp L) (closedBall c R) 0 := by
  have hgraph : HasFDerivWithinAt (graphMap p L normal w) L (closedBall c R) 0 := by
    convert ((hasFDerivAt_const p (0 : E2)).hasFDerivWithinAt.add
      L.hasFDerivAt.hasFDerivWithinAt).add ((hwflat.mono hK).smul_const normal) using 1
    · rfl
    · simp
  have hrp : HasFDerivAt r (fderiv ℝ r p) p :=
    ((hr.differentiableOn (by simp) p hp).differentiableAt (hV.mem_nhds hp)).hasFDerivAt
  have hbase : graphMap p L normal w 0 = p := by simp [graphMap, hw₀]
  have hrgraph : HasFDerivAt r (fderiv ℝ r p) (graphMap p L normal w 0) :=
    hbase.symm ▸ hrp
  exact hrgraph.comp_hasFDerivWithinAt 0 hgraph

theorem hopf_graph_extension_boundary_derivative (V : Set E3) (hV : IsOpen V)
    (U : Set E2) (p normal : E3) (hp : p ∈ V) (L : E2 →L[ℝ] E3)
    (w : E2 → ℝ) (hw₀ : w 0 = 0)
    (hwflat : HasFDerivWithinAt w (0 : E2 →L[ℝ] ℝ) U 0)
    (r : E3 → ℝ) (hr : ContDiffOn ℝ ∞ r V)
    (c : E2) (R : ℝ) (hK : closedBall c R ⊆ U)
    (h0 : (0 : E2) ∈ closedBall c R) :
    HasFDerivAt (hopfGraphExtension c R p L normal w r)
      (-((fderiv ℝ r p).comp L)) 0 := by
  exact affine_extension_hasFDerivAt _ _ _ h0 _
    (graph_height_boundary_derivative V hV U p normal hp L w hw₀ hwflat r hr c R hK).neg

theorem hopf_graph_extension_regular (V : Set E3) (hV : IsOpen V)
    (g : CoordinateMetric V) (U : Set E2) (p normal : E3) (L : E2 →L[ℝ] E3)
    (w : E2 → ℝ) (hwC1 : ContDiffOn ℝ 1 w U)
    (hgraph : MapsTo (graphMap p L normal w) U V)
    (hminimal : IsMinimalParametrizationOn g.tensor (graphMap p L normal w) (interior U))
    (r : E3 → ℝ) (hr : ContDiffOn ℝ ∞ r V)
    (c : E2) (R : ℝ) (hK : closedBall c R ⊆ U) (hB : ball c R ⊆ interior U) :
    ContDiffOn ℝ 2 (hopfGraphExtension c R p L normal w r) (ball c R) ∧
      ContinuousOn (hopfGraphExtension c R p L normal w r) (closedBall c R) := by
  have hheight : ContDiffOn ℝ 2 (graphHeight r (graphMap p L normal w)) (ball c R) :=
    (hr.of_le (by simp)).comp ((hminimal.1.of_le (by simp)).mono hB)
      (hgraph.mono (hB.trans interior_subset) (Subset.refl V))
  have hgraphc : ContinuousOn (graphMap p L normal w) U := by
    exact (continuousOn_const.add L.continuous.continuousOn).add
      (hwC1.continuousOn.smul continuousOn_const)
  have hheightc : ContinuousOn (graphHeight r (graphMap p L normal w)) (closedBall c R) :=
    (hr.continuousOn.comp hgraphc hgraph).mono hK
  constructor
  · exact hheight.neg.congr
      ((affine_extension_eqOn (closedBall c R) _ 0 _).mono ball_subset_closedBall)
  · exact affine_extension_continuousOn _ _ _ _ hheightc.neg

theorem hopf_graph_extension_values (U : Set E2) (p normal : E3)
    (L : E2 →L[ℝ] E3) (w : E2 → ℝ) (hw₀ : w 0 = 0)
    (r : E3 → ℝ) (hr₀ : r p = 0)
    (hrPositive : ∀ x ∈ interior U, 0 < r (graphMap p L normal w x))
    (c : E2) (R : ℝ) (hR : 0 < R) (hdist : dist (0 : E2) c = R)
    (hB : ball c R ⊆ interior U) :
    hopfGraphExtension c R p L normal w r 0 = 0 ∧
      ∀ x ∈ ball c R, hopfGraphExtension c R p L normal w r x < 0 := by
  have h0 : (0 : E2) ∈ closedBall c R := mem_closedBall.mpr hdist.le
  have heq := affine_extension_eqOn (closedBall c R)
    (fun x => -graphHeight r (graphMap p L normal w) x) 0 (-((fderiv ℝ r p).comp L))
  constructor
  · change affineOutsideExtension _ _ _ _ 0 = 0
    rw [heq h0]
    simp [graphHeight, graphMap, hw₀, hr₀]
  · intro x hx
    change affineOutsideExtension _ _ _ _ x < 0
    rw [heq (ball_subset_closedBall hx)]
    exact neg_neg_of_pos (hrPositive x (hB hx))

theorem positive_negative_direction_implies_nonzero (D : E2 →L[ℝ] ℝ)
    (c : E2) (hpositive : 0 < (-D) ((0 : E2) - c)) : D ≠ 0 := by
  intro hzero
  simp [hzero] at hpositive

end SeifertSurfaces.AppendixACoordinates.HopfAdapters
