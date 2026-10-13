import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.identityDiffeomorph
import HolomorphicAnosov.Targets.Theorem11Support.Surface.surface_model_real_toral_conjugacy
import HolomorphicAnosov.Paper.Zhang.AnosovRealToralConjugacyViaDiffeomorph
import HolomorphicAnosov.Paper.Zhang.OriginalGlobalHolonomyTorusHomeomorph
import HolomorphicAnosov.Paper.Zhang.OriginalGlobalHolonomyEuclideanCover
import HolomorphicAnosov.Topology.RealTorusHomeomorphOfAffineCover
import HolomorphicAnosov.Topology.FranksManning
import HolomorphicAnosov.Targets.GhysTheoremA
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Paper.Zhang.HyperbolicRealToralConjugacy
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.anosov_selected_complex_line_two_le_dimension

/-!
Global unstable holonomy and a rank-one stable bundle yield a topological
conjugacy to a hyperbolic real toral automorphism, assuming homotopy-torus rigidity.
(Zhang, Prop. 2.9, p.10; Ghys, proof of Thm B, p.598)
-/
open Set Filter MeasureTheory Manifold
open scoped ContDiff Manifold ENNReal Topology _root_.Topology Bundle
namespace HolomorphicAnosov
universe u
attribute [local instance] complex_isManifold_real

/-- A compact holomorphic Anosov manifold with a rank-one stable bundle and global
unstable holonomy is topologically conjugate to a hyperbolic integral automorphism of the real
`2 * d`-torus, assuming homotopy-torus rigidity. (Zhang, Prop. 2.9, p.10; Ghys, Thm A,
p.585 and pp.598–600, and proof of Thm B, p.598) -/
theorem proposition_2_9 {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (hholonomy : HasOriginalAnosovGlobalUnstableHolonomy a)
    (HS : HomotopyTorusRigidity.{u}) :
    HyperbolicRealToralConjugacy (2 * d) X (fun x ↦ f x) := by
  have hd2 : 2 ≤ d :=
    TheoremAProof.Dimension.anosov_selected_complex_line_two_le_dimension f a (Or.inl hstable)
  by_cases hd : d = 2
  · subst d
    exact surface_model_real_toral_conjugacy _ (ghys_theorem_A f a)
  · have hd3 : 3 ≤ d := by omega
    have hT := original_global_holonomy_torus_homeomorph hd3 f a hstable hholonomy HS
    let coords := Theorem12SupportW2.coordinates d
    let : CompactSpace (Theorem12SupportW2.Recharted X) := inferInstanceAs (CompactSpace X)
    let : ConnectedSpace (Theorem12SupportW2.Recharted X) := inferInstanceAs (ConnectedSpace X)
    let : T2Space (Theorem12SupportW2.Recharted X) := inferInstanceAs (T2Space X)
    let : SecondCountableTopology (Theorem12SupportW2.Recharted X) :=
      inferInstanceAs (SecondCountableTopology X)
    let : ChartedSpace (EuclideanSpace ℝ (Fin (2 * d)))
        (Theorem12SupportW2.Recharted X) :=
      Theorem12SupportW2.copiedCharts (X := X) coords
    let : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d))) ∞
        (Theorem12SupportW2.Recharted X) :=
      Theorem12SupportW2.copied_isManifold (X := X) coords
    exact holomorphic_anosov_real_toral_conjugacy_via_diffeomorph
      (Theorem12SupportW2.identityDiffeomorph coords) f a hT


end HolomorphicAnosov
