import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Riemannian.Basic
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealBilinear
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealMetric
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealBilinearSmooth

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- The smooth Riemannian metric on the real tangent bundle induced by the real part of a smooth
Hermitian metric. (Moroianu, §4.2, pp.24–25, §5.1, p.27; Demailly, VI §4, pp.296–297) -/
noncomputable def originalSmoothRealMetric {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h) :
    Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x) where
  inner := originalRealBilinear h
  symm := (originalRealMetric h).symm
  pos := (originalRealMetric h).pos
  isVonNBounded := (originalRealMetric h).isVonNBounded
  contMDiff := originalRealBilinear_smooth h hh

end StableFoliationsSupport
end HolomorphicAnosov
