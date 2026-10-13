import HolomorphicAnosov.Paper.Ghys.IntrinsicPresentationHolonomyHolomorphic
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation

/-! This file establishes holomorphicity of finite plaque-chain holonomy representatives in the
unstable complex leaf structures of an `AnosovIntrinsicFoliationPresentation` (Ghys, Prop. 2.2). -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

variable {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  (f : Biholomorph d d M M) (AD : AnosovDatum f)
  (P : AnosovIntrinsicFoliationPresentation f AD)

/-- A finite path holonomy representative is holomorphic in the prescribed unstable complex leaf
structures. -/
theorem path_holonomy_representative_holomorphic_g12
    (hRank : HasComplexRankOne AD.splitting.unstable.toDistribution) :
    letI := P.realCharts
    ∀ {q : Quotient P.foliations.stablePartition}
    {x y : IntrinsicFoliationLeaf P.foliations.stablePartition q}
    (γ : Path x y) (a b : unitInterval)
    (e : PathHolonomyRepresentative P.foliations γ a b),
    letI := P.complexLeaves.charts
      (Quotient.mk P.foliations.unstablePartition (γ a).val)
    letI := P.complexLeaves.charts
      (Quotient.mk P.foliations.unstablePartition (γ b).val)
    IsHolomorphicCurveLocalMap e.map := by
  let := P.realCharts
  intro q x y γ a b e
  exact intrinsicPresentation_holonomy_holomorphic f AD hRank P q x y γ a b e


theorem path_holonomy_pointed_holomorphic_g12
    (hRank : HasComplexRankOne AD.splitting.unstable.toDistribution) :
    letI := P.realCharts
    ∀ {q : Quotient P.foliations.stablePartition}
    {x y : IntrinsicFoliationLeaf P.foliations.stablePartition q}
    (γ : Path x y) (a b : unitInterval)
    (e : PathHolonomyRepresentative P.foliations γ a b),
    letI := P.complexLeaves.charts
      (Quotient.mk P.foliations.unstablePartition (γ a).val)
    letI := P.complexLeaves.charts
      (Quotient.mk P.foliations.unstablePartition (γ b).val)
    ∃ H : PointedLeafHomeomorph P.foliations (γ a).val (γ b).val,
      H = e.toPointedLeafHomeomorph ∧ IsHolomorphicCurveLocalMap H.map := by
  let := P.realCharts
  intro q x y γ a b e
  refine ⟨e.toPointedLeafHomeomorph, rfl, ?_⟩
  exact intrinsicPresentation_holonomy_holomorphic f AD hRank P q x y γ a b e

end HolomorphicAnosov.Ghys
