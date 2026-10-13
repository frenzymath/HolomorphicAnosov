import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne















namespace HolomorphicAnosov

universe u
attribute [local instance] complex_isManifold_real
















def IsComplexCodimensionOne {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    {f : Biholomorph d d X X} (a : AnosovDatum f) : Prop :=
  HasComplexRankOne a.splitting.stable.toDistribution ∨
    HasComplexRankOne a.splitting.unstable.toDistribution

end HolomorphicAnosov
