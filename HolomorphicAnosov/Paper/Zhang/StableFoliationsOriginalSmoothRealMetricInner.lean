import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Riemannian.Basic
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealBilinearApply
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalSmoothRealMetric

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- The induced smooth real metric evaluates to the real Hermitian pairing on every pair of tangent
vectors. -/
theorem originalSmoothRealMetric_inner {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (x : M) (v w : TangentSpace (realModel d) x) :
    (originalSmoothRealMetric h hh).inner x v w = hermitianTangentRealPairing h x v w :=
  originalRealBilinear_apply h x v w

end StableFoliationsSupport
end HolomorphicAnosov
