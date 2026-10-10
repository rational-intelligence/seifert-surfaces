import EndpointGeometry

noncomputable section
open Set Topology Function
open scoped Manifold ContDiff

namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.Foundations

universe u v
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]

/-- An actual smooth embedded sheet with boundary; compactness is not required
by A.3. The source surface and inclusion, including boundary derivatives, remain visible. -/
structure EmbeddedSheet (N : Type u) [TopologicalSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] where
  carrier : Type v
  [topology : TopologicalSpace carrier]
  [charted : ChartedSpace (EuclideanHalfSpace 2) carrier]
  [manifold : IsManifold (𝓡∂ 2) ∞ carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  inclusion : carrier → N
  smoothEmbedding : Manifold.IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ inclusion

attribute [instance] EmbeddedSheet.topology EmbeddedSheet.charted EmbeddedSheet.manifold
  EmbeddedSheet.hausdorff EmbeddedSheet.secondCountable

namespace EmbeddedSheet

def image (P : EmbeddedSheet.{u,v} N) : Set N := range P.inclusion

def boundaryImage (P : EmbeddedSheet.{u,v} N) : Set N :=
  P.inclusion '' (𝓡∂ 2).boundary P.carrier

def parameter (P : EmbeddedSheet.{u,v} N) (x : P.carrier) : E2 → N :=
  P.inclusion ∘ (extChartAt (𝓡∂ 2) x).symm

def coordinateInterior (P : EmbeddedSheet.{u,v} N) (x : P.carrier)
    (c : SmoothAmbientChart N) : Set E2 :=
  (extChartAt (𝓡∂ 2) x).target ∩
    ((extChartAt (𝓡∂ 2) x).symm ⁻¹' (𝓡∂ 2).interior P.carrier) ∩
    (P.parameter x ⁻¹' c.chart.source)

/-- Vanishing normal mean-curvature trace of the same sheet for the actual
ambient metric, expressed in every pair of its actual source/ambient charts. -/
def Minimal (P : EmbeddedSheet.{u,v} N) (h : AmbientMetric N) : Prop :=
  ∀ x : P.carrier, ∀ c : SmoothAmbientChart N,
    IsMinimalParametrizationOn (actualChartTensor h c)
      (c.chart ∘ P.parameter x) (P.coordinateInterior x c)

end EmbeddedSheet

abbrev ArcTime := Set.Ioo (-1 : ℝ) 1

/-- Push the outward source vector through the actual sheet differential,
transporting along the exact equality identifying its edge point with e(t). -/
def edgeConormal (P : EmbeddedSheet.{u,v} N) (e : ℝ → N)
    (lift : ArcTime → P.carrier) (heq : ∀ t : ArcTime, P.inclusion (lift t) = e t)
    (outward : ∀ t : ArcTime, TangentSpace (𝓡∂ 2) (lift t)) (t : ArcTime) :
    TangentSpace 𝓘(ℝ, E3) (e t) :=
  heq t ▸ mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) P.inclusion (lift t) (outward t)

def arcVelocity (e : ℝ → N) (t : ArcTime) : TangentSpace 𝓘(ℝ, E3) (e t) :=
  mfderiv 𝓘(ℝ) 𝓘(ℝ, E3) e (t : ℝ)
    ((NormedSpace.fromTangentSpace (t : ℝ)).symm 1)

/-- The literal A.3 configuration of two supplied smooth minimal sheets and
one common boundary arc. Matching graph derivatives and a weak equation are
not assumptions: those remain obligations of the theorem. -/
structure A3OriginalData (h : AmbientMetric N) (M : Set N) where
  sheetOne : EmbeddedSheet.{u,v} N
  sheetTwo : EmbeddedSheet.{u,v} N
  sheetOne_in_manifold : sheetOne.image ⊆ M
  sheetTwo_in_manifold : sheetTwo.image ⊆ M
  minimalOne : sheetOne.Minimal h
  minimalTwo : sheetTwo.Minimal h
  edge : ℝ → N
  edge_smooth : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E3) ∞ edge (Ioo (-1 : ℝ) 1)
  edge_embedding : IsEmbedding (fun t : ArcTime => edge t)
  edge_regular : ∀ t : ArcTime, arcVelocity edge t ≠ 0
  pointParameter : ArcTime
  liftOne : ArcTime → sheetOne.carrier
  liftTwo : ArcTime → sheetTwo.carrier
  liftOne_boundary : ∀ t : ArcTime, liftOne t ∈ (𝓡∂ 2).boundary sheetOne.carrier
  liftTwo_boundary : ∀ t : ArcTime, liftTwo t ∈ (𝓡∂ 2).boundary sheetTwo.carrier
  liftOne_exact : ∀ t : ArcTime, sheetOne.inclusion (liftOne t) = edge t
  liftTwo_exact : ∀ t : ArcTime, sheetTwo.inclusion (liftTwo t) = edge t
  outwardOne : ∀ t : ArcTime, TangentSpace (𝓡∂ 2) (liftOne t)
  outwardTwo : ∀ t : ArcTime, TangentSpace (𝓡∂ 2) (liftTwo t)
  outwardOne_direction : ∀ t : ArcTime, inwardCoordinate (liftOne t) (outwardOne t) < 0
  outwardTwo_direction : ∀ t : ArcTime, inwardCoordinate (liftTwo t) (outwardTwo t) < 0
  conormalOne_unit : ∀ t : ArcTime,
    h.inner (edge t) (edgeConormal sheetOne edge liftOne liftOne_exact outwardOne t)
      (edgeConormal sheetOne edge liftOne liftOne_exact outwardOne t) = 1
  conormalTwo_unit : ∀ t : ArcTime,
    h.inner (edge t) (edgeConormal sheetTwo edge liftTwo liftTwo_exact outwardTwo t)
      (edgeConormal sheetTwo edge liftTwo liftTwo_exact outwardTwo t) = 1
  conormalOne_orthogonal : ∀ t : ArcTime,
    h.inner (edge t) (edgeConormal sheetOne edge liftOne liftOne_exact outwardOne t)
      (arcVelocity edge t) = 0
  conormalTwo_orthogonal : ∀ t : ArcTime,
    h.inner (edge t) (edgeConormal sheetTwo edge liftTwo liftTwo_exact outwardTwo t)
      (arcVelocity edge t) = 0
  opposite_outward_conormals : ∀ t : ArcTime,
    edgeConormal sheetOne edge liftOne liftOne_exact outwardOne t +
      edgeConormal sheetTwo edge liftTwo liftTwo_exact outwardTwo t = 0
  otherwise_locally_disjoint : ∃ V : Set N, IsOpen V ∧ edge pointParameter ∈ V ∧
    (sheetOne.image ∩ sheetTwo.image) ∩ V = (edge '' Ioo (-1 : ℝ) 1) ∩ V

                                                                        
                                                                                  
                                                     
                                    
                                                                 
                                                      
                      
                                          
                                                                   
                                                                    
       

end SeifertSurfaces.OriginalEndpoints
