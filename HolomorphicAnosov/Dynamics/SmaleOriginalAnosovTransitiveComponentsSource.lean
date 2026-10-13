import HolomorphicAnosov.Dynamics.SmaleBasinIntersection
import HolomorphicAnosov.Dynamics.HreturnPseudoOrbitPositive
import HolomorphicAnosov.Dynamics.SmaleCyclicShadowing
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricExpansivity
import HolomorphicAnosov.Dynamics.SmaleCompactShadowing
import HolomorphicAnosov.Dynamics.SmaleShadowingIsolation
import HolomorphicAnosov.Dynamics.SmalePeriodicShadowingClosure
import HolomorphicAnosov.Dynamics.SmalePeriodicOrbitVisits
import HolomorphicAnosov.Dynamics.ManeDenseOrbitOfSaturation
import Mathlib.Topology.Sequences
import HolomorphicAnosov.Dynamics.SmaleNonwanderingClosed
import HolomorphicAnosov.Dynamics.SmalePeriodicClosureNonwandering
import HolomorphicAnosov.Dynamics.SmaleOrbitClusterNonwandering
import HolomorphicAnosov.Dynamics.SmaleNonwanderingNonempty
import HolomorphicAnosov.Dynamics.SmaleOrbitEventuallyNearNonwandering
import HolomorphicAnosov.Dynamics.SmaleDisjointBasins
import HolomorphicAnosov.Dynamics.SmaleFiniteBasinPartition
import HolomorphicAnosov.Dynamics.SmaleOrbitComponentCapture
import HolomorphicAnosov.Dynamics.SmaleDistanceFromClusterLimits
import HolomorphicAnosov.Dynamics.SmaleBasinFromNeighborhood
import HolomorphicAnosov.Dynamics.SmaleBasinPartitionFromNeighborhoods
import HolomorphicAnosov.Dynamics.SmaleBasinPartitionFromComponents
import HolomorphicAnosov.Dynamics.SmaleNonwanderingInverse
import HolomorphicAnosov.Dynamics.SmaleTwoSidedBasinPartition
import HolomorphicAnosov.Dynamics.SmaleCaptureOtherComponent
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Dynamics.HirschPughAdaptedOrbitPlaques
import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import HolomorphicAnosov.Dynamics.HyperbolicBracketOpenReturn
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import HolomorphicAnosov.Geometry.UniformExponentialLift
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle

import HolomorphicAnosov.Dynamics.SmaleOriginalAnosovCyclicShadowing
import HolomorphicAnosov.Dynamics.SmaleOriginalAnosovComponentDecomposition
namespace HolomorphicAnosov
open Set Filter
open scoped ContDiff _root_.Topology Bundle
universe u

/-- For an Anosov diffeomorphism with cyclic shadowing, the nonwandering set splits into finitely
many compact invariant transitive components with internal finite shadowing, each equal to the
intersection of its stable and unstable basins (Shub, Prop. 8.11; Thm. 8.13; Props. 8.20–8.22
and 9.7–9.8). -/
theorem smale_original_anosov_transitive_components_source
    {n : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M] [SecondCountableTopology M]
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (Es Eu : ContinuousRealTangentSubbundle
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M)
    (metric : Bundle.ContMDiffRiemannianMetric
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n))
      (fun x : M => TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x))
    (C lam : ℝ) :
    let I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨metric.toRiemannianMetric⟩
    IsRiemannianManifold I M →
    0 < C → 0 < lam → lam < 1 →
    (∀ x, IsCompl (Es.toDistribution x) (Eu.toDistribution x)) →
    (∀ x, (Es.toDistribution x).map (mfderiv I I f x).toLinearMap =
      Es.toDistribution (f x)) →
    (∀ x, (Eu.toDistribution x).map (mfderiv I I f x).toLinearMap =
      Eu.toDistribution (f x)) →
    (∀ x k (v : TangentSpace I x), v ∈ Es.toDistribution x →
      ‖mfderiv I I ((f : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) →
    (∀ x k (v : TangentSpace I x), v ∈ Eu.toDistribution x →
      ‖mfderiv I I ((f.symm : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 0 < n → ∀ q : Fin n → M,
        (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
          ∃ j : Fin n → M, Function.Semiconj j (finRotate n) f ∧
            ∀ i, dist (j i) (q i) < ε) →
    let Ω : Set M := {x | ∀ U : Set M, IsOpen U → x ∈ U →
      ∃ k : ℕ, 0 < k ∧ (((f : M → M)^[k]) '' U ∩ U).Nonempty}
    let Ws : Set M → Set M := fun L =>
      {x | Tendsto (fun k : ℕ => Metric.infDist (((f : M → M)^[k]) x) L)
        atTop (𝓝 0)}
    let Wu : Set M → Set M := fun L =>
      {x | Tendsto (fun k : ℕ => Metric.infDist (((f.symm : M → M)^[k]) x) L)
        atTop (𝓝 0)}
    ∃ (b : ℕ) (L : Fin b → Set M), (∀ i, (L i).Nonempty ∧ IsCompact (L i) ∧ f '' L i = L i) ∧
      Pairwise (fun i j => Disjoint (L i) (L j)) ∧
      Ω = ⋃ i, L i ∧
      (∀ i, ∀ U V : Set M, IsOpen U → (U ∩ L i).Nonempty →
        IsOpen V → (V ∩ L i).Nonempty →
        ∃ k : ℕ, ((f : M → M)^[k] '' (U ∩ L i) ∩ V).Nonempty) ∧
      (∀ i, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ (N : ℕ) (q : ℕ → M), (∀ k ≤ N, q k ∈ L i) →
          (∀ k < N, dist (f (q k)) (q (k + 1)) < δ) →
          ∃ a ∈ L i, ∀ k ≤ N, dist ((f : M → M)^[k] a) (q k) < ε) ∧
      ((∀ i, Ws (L i) ∩ Wu (L i) ⊆ Ω) ∧ (∀ i, (L i).Nonempty)) := by
  dsimp only
  intro hR hC hlam hlam1 hcompl hEs hEu hs hu hcyclic
  obtain ⟨b, L, hL, hdisjoint, hcover, htransitive, hfinite⟩ :=
    smale_original_anosov_component_decomposition f Es Eu metric C lam
      hR hC hlam hlam1 hcompl hEs hEu hs hu hcyclic
  refine ⟨b, L, hL, hdisjoint, hcover, htransitive, hfinite, ?_, fun i ↦ (hL i).1⟩
  intro i x hx
  exact hreturn_of_cyclic_basin_transitivity_pos f.toHomeomorph (L i) (hL i).1
    (htransitive i) hcyclic x hx.1 hx.2


end HolomorphicAnosov

