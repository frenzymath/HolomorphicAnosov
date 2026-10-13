import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Dynamics.Anosov.InvariantRealTangentSplitting
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateDerivative











namespace HolomorphicAnosov

open scoped Bundle ContDiff

attribute [local instance] complex_isManifold_real








structure AnosovDatum {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) where
  
  metric : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
    (fun x : X ↦ TangentSpace (realModel d) x)
  
  splitting : InvariantRealTangentSplitting f.toReal
  
  k : ℕ
  
  one_le_k : 1 ≤ k
  
  stable_contracting :
    letI : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨metric.toRiemannianMetric⟩
    ∀ x, ‖(restrictedIterateDerivative f.toReal splitting.stable.toDistribution
      splitting.stable_map k x).toContinuousLinearMap‖ < 1
  
  unstable_contracting :
    letI : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨metric.toRiemannianMetric⟩
    ∀ x, ‖(restrictedIterateDerivative f.toReal splitting.unstable.toDistribution
      splitting.unstable_map k x).symm.toContinuousLinearMap‖ < 1

end HolomorphicAnosov
