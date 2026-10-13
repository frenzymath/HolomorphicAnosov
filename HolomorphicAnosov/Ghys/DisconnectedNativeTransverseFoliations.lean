import HolomorphicAnosov.Ghys.DisconnectedComponentResidues
import HolomorphicAnosov.Ghys.DisconnectedHpsSourcePairCompletion
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne

/-! This file constructs the native real transverse foliations for a disconnected holomorphic Anosov system. (HPS, §7; Ghys, §2) -/

noncomputable section
open scoped ContDiff Manifold Topology _root_.Topology
open Set
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

/-- For a nonempty compact manifold with rank-one Anosov data, the native stable and unstable laminations form an invariant real transverse pair. (HPS, §7; Ghys, §2) -/
theorem disconnected_native_transverse_foliations
    {d : ℕ} {M : Type u} [MetricSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hmetric : (inferInstance : MetricSpace M).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace M))
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    ∃ B : ComplexModel d ≃L[ℝ] (Fin ((2*d-2)+2) → ℝ),
      letI := realCoordinateRechart (M := M) B
      ∃ F : TransverseContinuousFoliations.{u,u} (2*d-2) 2 M,
        ((∀ x y, F.stablePartition x y ↔ @ForwardAsymptotic M (inferInstance : MetricSpace M) f x y) ∧
          (∀ x y, F.unstablePartition x y ↔ @ForwardAsymptotic M (inferInstance : MetricSpace M) f.symm x y)) ∧
        (∀ q : Quotient F.stablePartition,
          letI := F.stableTopology q
          letI := F.stableCharts q
          ∃ smooth : IsManifold 𝓘(ℝ, Fin (2*d-2) → ℝ) ∞
              (IntrinsicFoliationLeaf F.stablePartition q),
            letI := smooth
            ∃ N : HPS.NativeLeaf (r := 2*d-2)
              a.splitting.stable.toDistribution
              (IntrinsicFoliationLeaf F.stablePartition q),
            N.inclusion = Subtype.val) ∧
        (∀ q : Quotient F.unstablePartition,
          letI := F.unstableTopology q
          letI := F.unstableCharts q
          ∃ smooth : IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞
              (IntrinsicFoliationLeaf F.unstablePartition q),
            letI := smooth
            ∃ N : HPS.NativeLeaf (r := 2)
              a.splitting.unstable.toDistribution
              (IntrinsicFoliationLeaf F.unstablePartition q),
    N.inclusion = Subtype.val) := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (ComplexModel d) M
  have hbridge := disconnected_component_residue_bridge f.toHomeomorph
  exact disconnected_hps_source_pair_completion f a hmetric hRank hbridge
end HolomorphicAnosov.Ghys
