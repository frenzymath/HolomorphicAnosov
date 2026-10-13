import HolomorphicAnosov.Geometry.LocalHolonomyContinuationExistsG9
import HolomorphicAnosov.Analysis.Complex.SchwarzianMobiusConverse
import HolomorphicAnosov.Paper.Ghys.SchwarzianAffineCurveCalculus
import HolomorphicAnosov.Paper.Ghys.SchwarzianLeafCocycleNativeProvider
import HolomorphicAnosov.Ghys.SchwarzianCoordinateIndependence
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Paper.Ghys.ActualInvariantSectionFlowboxCoverG5
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Ghys.AffineSchwarzianQuadraticForm
import HolomorphicAnosov.Paper.Ghys.Proposition31
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! This file states the Schwarzian cocycle laws for stable holonomy on simply connected intrinsic
stable leaves of a holomorphic Anosov system (Ghys, §4, pp. 594–595). -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real


section OriginalLeaves
variable {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  (f : Biholomorph d d M M) (AD : AnosovDatum f)
  (P : AnosovIntrinsicFoliationPresentation f AD)

/-- Stable holonomy on a simply connected intrinsic stable leaf has a Schwarzian quadratic cocycle
with zero diagonal, translation-invariant diameter, and quadratic scalar homogeneity. The
cocycle is equivariant under the Anosov map and its unstable derivative (Ghys, Lemma
4.2(i),(iii), p. 595, Props. 2.2 and 3.1; Nisoli, Remarks 1.3.2 and 1.3.5, Thm 1.3.8, pp.
21–25). -/
theorem schwarzian_original_stable_leaf_cocycle :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    letI : ∀ x : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.complex_manifold (Quotient.mk P.foliations.unstablePartition x)
    ∀
    (_hRank : HasComplexRankOne AD.splitting.unstable.toDistribution)
    (A : AffineUnstableLeafStructures P.foliations P.complexLeaves)
    (_hAffine : A.ActsAffinely P.foliations P.complexLeaves f)
    (_hContinuous : A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves),
    ∀ q : Quotient P.foliations.stablePartition,
    letI := P.foliations.stableTopology q
    let L := IntrinsicFoliationLeaf P.foliations.stablePartition q
    SimplyConnectedSpace L →
    ∃ q' : Quotient P.foliations.stablePartition,
    letI := P.foliations.stableTopology q'
    let L' := IntrinsicFoliationLeaf P.foliations.stablePartition q'
    ∃ es : L ≃ₜ L', (∀ x : L, (es x).val = f x.val) ∧
    ∃ (H : ∀ x y : L, PointedLeafHomeomorph P.foliations x.val y.val)
      (H' : ∀ x y : L', PointedLeafHomeomorph P.foliations x.val y.val)
      (Q : ∀ x _y : L, QuadraticForm ℂ
        (TangentSpace (complexModel 1) (P.foliations.uPoint x.val)))
      (Q' : ∀ x _y : L', QuadraticForm ℂ
        (TangentSpace (complexModel 1) (P.foliations.uPoint x.val))),
      (∀ (x y : L) (γ : Path x y), ∃ C : LocalHolonomyContinuation P.foliations γ,
        (Filter.Germ.ofFun (H (γ 0) (γ 1)).map :
          Filter.Germ (𝓝 (P.foliations.uPoint (γ 0).val)) (P.foliations.ULeaf (γ 1).val)) =
        Filter.Germ.ofFun (C.representative 0 1 (show (0 : unitInterval) ≤ 1 from bot_le)).map) ∧
      (∀ (x y : L) (γ : Path x y) (e : PathHolonomyRepresentative P.foliations γ 0 1),
        (Filter.Germ.ofFun (H (γ 0) (γ 1)).map :
          Filter.Germ (𝓝 (P.foliations.uPoint (γ 0).val)) (P.foliations.ULeaf (γ 1).val)) =
        Filter.Germ.ofFun e.map) ∧
      (∀ (x y : L') (γ : Path x y), ∃ C : LocalHolonomyContinuation P.foliations γ,
        (Filter.Germ.ofFun (H' (γ 0) (γ 1)).map :
          Filter.Germ (𝓝 (P.foliations.uPoint (γ 0).val)) (P.foliations.ULeaf (γ 1).val)) =
        Filter.Germ.ofFun (C.representative 0 1 (show (0 : unitInterval) ≤ 1 from bot_le)).map) ∧
      (∀ (x y : L') (γ : Path x y) (e : PathHolonomyRepresentative P.foliations γ 0 1),
        (Filter.Germ.ofFun (H' (γ 0) (γ 1)).map :
          Filter.Germ (𝓝 (P.foliations.uPoint (γ 0).val)) (P.foliations.ULeaf (γ 1).val)) =
        Filter.Germ.ofFun e.map) ∧
      (∀ x y : L, IsHolomorphicCurveLocalMap (H x y).map) ∧
      (∀ x y : L', IsHolomorphicCurveLocalMap (H' x y).map) ∧
      (∀ (x y : L) (c : OpenPartialHomeomorph (P.foliations.ULeaf x.val) ℂ)
        (e : OpenPartialHomeomorph (P.foliations.ULeaf y.val) ℂ),
        c ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves x.val) →
        e ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves y.val) →
        P.foliations.uPoint x.val ∈ c.source → P.foliations.uPoint y.val ∈ e.source →
        Q x y = schwarzianQuadraticAt c (H x y).map e (P.foliations.uPoint x.val)) ∧
      (∀ (x y : L') (c : OpenPartialHomeomorph (P.foliations.ULeaf x.val) ℂ)
        (e : OpenPartialHomeomorph (P.foliations.ULeaf y.val) ℂ),
        c ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves x.val) →
        e ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves y.val) →
        P.foliations.uPoint x.val ∈ c.source → P.foliations.uPoint y.val ∈ e.source →
        Q' x y = schwarzianQuadraticAt c (H' x y).map e (P.foliations.uPoint x.val)) ∧
      (∀ (x y z : L) (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)),
        Q x z v = Q x y v + Q y z
          (mfderiv (complexModel 1) (complexModel 1) (H x y).map
            (P.foliations.uPoint x.val) v)) ∧
      (∀ x : L, Q x x = 0) ∧
      (∀ (x y : L) (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val))
        (Ω : Set L), IsCompact Ω →
        Metric.diam ((fun z : L ↦ Q x z v) '' Ω) =
          Metric.diam ((fun z : L ↦ Q y z
            (mfderiv (complexModel 1) (complexModel 1) (H x y).map
              (P.foliations.uPoint x.val) v)) '' Ω)) ∧
      (∀ (x y : L) (lam : ℂ)
        (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)),
        Q x y (lam • v) = lam ^ 2 * Q x y v) ∧
      ∃ Φ : ∀ x : L, Biholomorph 1 1
        (P.foliations.ULeaf x.val) (P.foliations.ULeaf (es x).val),
        (∀ (x : L) (z : P.foliations.ULeaf x.val), (Φ x z).val = f z.val) ∧
        (∀ (x y : L) (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)),
          Q' (es x) (es y)
            (mfderiv (complexModel 1) (complexModel 1) (Φ x)
              (P.foliations.uPoint x.val) v) = Q x y v) ∧
        (∀ (x : L) (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)),
          mfderiv (complexModel 1) (complexModel d)
              (Subtype.val : P.foliations.ULeaf (es x).val → M)
              (P.foliations.uPoint (es x).val)
              (mfderiv (complexModel 1) (complexModel 1) (Φ x)
                (P.foliations.uPoint x.val) v) =
            mfderiv (complexModel d) (complexModel d) f x.val
              (mfderiv (complexModel 1) (complexModel d)
                (Subtype.val : P.foliations.ULeaf x.val → M)
                (P.foliations.uPoint x.val) v)) := by
  exact native_schwarzian_leaf_cocycle_provider f AD P

end OriginalLeaves
end HolomorphicAnosov.Ghys

