import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- The real Hermitian pairing is symmetric. (Moroianu, §5.1, p.27) -/
theorem real_pairing_symm {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] (h : HermitianTangentMetricCore d M)
    (x : M) (v w : TangentSpace (realModel d) x) :
    hermitianTangentRealPairing h x v w = hermitianTangentRealPairing h x w v := by
  change ((h x).inner _ _).re = ((h x).inner _ _).re
  have hc := congrArg Complex.re ((h x).conj_inner_symm
    ((complexTangentToReal d x).symm w) ((complexTangentToReal d x).symm v))
  simpa using hc.symm

end StableFoliationsSupport
end HolomorphicAnosov
