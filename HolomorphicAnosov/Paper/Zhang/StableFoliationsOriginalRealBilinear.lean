import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Riemannian.Basic
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealPairingContinuousBilinear

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- The continuous real bilinear form on each tangent fibre given by the real part of the Hermitian
pairing. -/
noncomputable def originalRealBilinear {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] (h : HermitianTangentMetricCore d M) (x : M) :
    TangentSpace (realModel d) x →L[ℝ] TangentSpace (realModel d) x →L[ℝ] ℝ :=
  Classical.choose (real_pairing_continuous_bilinear h x)

end StableFoliationsSupport
end HolomorphicAnosov
