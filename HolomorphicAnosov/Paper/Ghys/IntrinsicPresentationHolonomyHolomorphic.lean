import HolomorphicAnosov.Geometry.IntrinsicHolonomyChainHolomorphic
import HolomorphicAnosov.Paper.Ghys.IntrinsicPresentationPlaqueHolomorphic

/-! This module proves holomorphicity of stable holonomy in intrinsic unstable charts. (Ghys, Prop. 2.2) -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

/-- Stable holonomy is biholomorphic in the intrinsic unstable complex charts. (Ghys, Prop. 2.2) -/
theorem intrinsicPresentation_holonomy_holomorphic
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (P : AnosovIntrinsicFoliationPresentation f a) :
    letI := P.realCharts
    ∀ (q : Quotient P.foliations.stablePartition)
      (x y : IntrinsicFoliationLeaf P.foliations.stablePartition q) (γ : Path x y)
      (t₀ t₁ : unitInterval) (H : PathHolonomyRepresentative P.foliations γ t₀ t₁),
      letI := P.complexLeaves.charts
        (Quotient.mk P.foliations.unstablePartition (γ t₀).val)
      letI := P.complexLeaves.charts
        (Quotient.mk P.foliations.unstablePartition (γ t₁).val)
      IsHolomorphicCurveLocalMap H.map := by
  let := P.realCharts
  intro q x y γ t₀ t₁ H
  exact intrinsic_holonomy_chain_holomorphic P.foliations P.complexLeaves
    (intrinsicPresentation_plaque_holomorphic f a hRank P)
    q x y γ t₀ t₁ H.map H.chain

end HolomorphicAnosov.Ghys

