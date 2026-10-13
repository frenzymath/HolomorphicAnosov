import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Paper.Ghys.NativeUnstableComplexRankOneFromRealRankTwo
import HolomorphicAnosov.Paper.Ghys.NativeAffineCarrierTransport
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

/-- A native intrinsic presentation admits complete affine unstable-leaf structures and a transverse
projective atlas whose coordinates locally differ from affine leaf coordinates by Möbius
transformations. (Ghys, Prop. 3.1, pp. 590–593; Prop. 4.1, pp. 593–597; §5, p. 597) -/
theorem native_affine_transverse_projective_atlas
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hu : ∀ x : M,
      Module.finrank ℝ (a.splitting.unstable.toDistribution x) = 2)
    (s : ℕ)
    (A : NativeTransverseAsymptoticIdentification.{u, u}
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2)
    (C : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (hC : letI := A.realAmbientCharts
      ∀ q : Quotient A.F.unstablePartition,
        letI := A.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) ∧
        ∀ z : IntrinsicFoliationLeaf A.F.unstablePartition q,
          Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
            (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) z) :
    letI := A.realAmbientCharts
    ∃ affine : AffineUnstableLeafStructures A.F C,
    (∀ q : Quotient A.F.unstablePartition,
      letI := A.F.unstableTopology q
      letI := C.charts q
      ComplexAffineStructure.Complete _ (affine.structureAt q)) ∧
    ∃ atlas : TransverseProjectiveAtlas A.F C,
    (∀ c ∈ atlas.charts, ∀ x : M, ∀ z : A.F.ULeaf x,
      letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition x)
      letI := C.charts (Quotient.mk A.F.unstablePartition x)
      z.val ∈ c.domain A.F C →
      ∃ b ∈ ComplexAffineStructure.maximalAtlas _ (affine.atPoint A.F C x),
        z ∈ b.source ∧ ∃ g : ComplexMobiusTransformation,
          ∀ᶠ w in 𝓝 z,
            w ∈ b.source ∧ w.val ∈ c.domain A.F C ∧
              c.transverseCoordinate A.F C w.val = g.apply (complexProjectiveLineFinite (b w))) := by
  have hRank := native_unstable_complex_rank_one_from_real_rank_two f a hu
  exact native_affine_carrier_transport f a hRank s A C hC


end HolomorphicAnosov.Ghys
