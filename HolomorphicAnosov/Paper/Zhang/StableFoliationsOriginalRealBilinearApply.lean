import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Riemannian.Basic
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealPairingContinuousBilinear
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealBilinear

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- The real bilinear form evaluates to the real Hermitian pairing on every pair of tangent vectors. -/
theorem originalRealBilinear_apply {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] (h : HermitianTangentMetricCore d M)
    (x : M) (v w : TangentSpace (realModel d) x) :
    originalRealBilinear h x v w = hermitianTangentRealPairing h x v w :=
  Classical.choose_spec (real_pairing_continuous_bilinear h x) v w

end StableFoliationsSupport
end HolomorphicAnosov
